type tree = Node of string * tree list | Leaf of string

let rec tree_yield = function
  | Leaf s -> [ s ]
  | Node (_, children) -> List.concat_map tree_yield children

type prep = {
  prods : Grammar.production array;
  mutable probs : float array;
  by_lhs : (string, int list) Hashtbl.t;
  lhs_list : string list;
  start : string;
}

let unary_order prods by_lhs =
  let children = Hashtbl.create 64 in
  let indegree = Hashtbl.create 64 in
  Hashtbl.iter (fun lhs _ -> Hashtbl.replace indegree lhs 0) by_lhs;
  Array.iter
    (fun (p : Grammar.production) ->
      match p.rhs with
      | [ Grammar.Nonterm child ] when Hashtbl.mem by_lhs child ->
          let outgoing =
            Option.value ~default:[] (Hashtbl.find_opt children p.lhs)
          in
          if not (List.mem child outgoing) then begin
            Hashtbl.replace children p.lhs (child :: outgoing);
            Hashtbl.replace indegree child (Hashtbl.find indegree child + 1)
          end
      | _ -> ())
    prods;
  let ready =
    Hashtbl.fold
      (fun lhs degree acc -> if degree = 0 then lhs :: acc else acc)
      indegree []
    |> List.sort String.compare
  in
  let rec visit order ready =
    match ready with
    | [] -> List.rev order
    | lhs :: rest ->
        let ready = ref rest in
        List.iter
          (fun child ->
            let degree = Hashtbl.find indegree child - 1 in
            Hashtbl.replace indegree child degree;
            if degree = 0 then
              ready := List.sort_uniq String.compare (child :: !ready))
          (Option.value ~default:[] (Hashtbl.find_opt children lhs));
        visit (lhs :: order) !ready
  in
  let order = visit [] ready in
  if List.length order <> Hashtbl.length by_lhs then
    invalid_arg "unit-production cycles must be normalised before parsing";
  order

let prepare (g : Grammar.t) =
  let prods : Grammar.production array = Array.of_list g.productions in
  let n = Array.length prods in
  let probs = Array.make n 0.0 in
  let by_lhs = Hashtbl.create 64 in
  Array.iteri
    (fun i (p : Grammar.production) ->
      let l =
        match Hashtbl.find_opt by_lhs p.lhs with Some l -> l | None -> []
      in
      Hashtbl.replace by_lhs p.lhs (i :: l))
    prods;
  Hashtbl.iter
    (fun _ idxs ->
      let tot =
        List.fold_left (fun s i -> s +. prods.(i).count) 0.0 idxs
      in
      let k = List.length idxs in
      List.iter
        (fun i ->
          probs.(i) <-
            (if tot > 0.0 then prods.(i).count /. tot
             else 1.0 /. float_of_int k))
        idxs)
    by_lhs;
  {
    prods;
    probs;
    by_lhs;
    lhs_list = unary_order prods by_lhs;
    start = g.start;
  }

let prepare_uniform (g : Grammar.t) =
  let prep = prepare g in
  Array.fill prep.probs 0 (Array.length prep.probs) 0.0;
  Hashtbl.iter
    (fun _ idxs ->
      let k = List.length idxs in
      if k > 0 then
        List.iter (fun i -> prep.probs.(i) <- 1.0 /. float_of_int k) idxs)
    prep.by_lhs;
  prep

let prob_of_prod prep (p : Grammar.production) =
  let idxs =
    Option.value ~default:[] (Hashtbl.find_opt prep.by_lhs p.lhs)
  in
  let rec find = function
    | [] -> 0.0
    | i :: rest ->
        if Grammar.equal_rhs prep.prods.(i).rhs p.rhs then prep.probs.(i)
        else find rest
  in
  find idxs

let log_add left right =
  if left = neg_infinity then right
  else if right = neg_infinity then left
  else if left >= right then left +. log1p (exp (right -. left))
  else right +. log1p (exp (left -. right))

let make_log_inside prep tokens =
  let n = List.length tokens in
  let w = Array.of_list tokens in
  let imemo = Hashtbl.create 1024 in
  let smemo = Hashtbl.create 1024 in
  let rec inside_nt nt i j =
    if j <= i then neg_infinity
    else
      match Hashtbl.find_opt imemo (nt, i, j) with
      | Some v -> v
      | None ->
          let idxs =
            Option.value ~default:[] (Hashtbl.find_opt prep.by_lhs nt)
          in
          let v =
            List.fold_left
              (fun acc pi ->
                let probability = prep.probs.(pi) in
                if probability <= 0.0 then acc
                else
                  log_add acc
                    (log probability +. seq_inside prep.prods.(pi).rhs i j))
              neg_infinity idxs
          in
          Hashtbl.replace imemo (nt, i, j) v;
          v
  and seq_inside rhs i j =
    match Hashtbl.find_opt smemo (rhs, i, j) with
    | Some v -> v
    | None ->
        let v =
          match rhs with
          | [] -> if i = j then 0.0 else neg_infinity
          | Grammar.Term a :: rest ->
              if i < n && String.equal w.(i) a then
                seq_inside rest (i + 1) j
              else neg_infinity
          | Grammar.Nonterm x :: rest ->
              let acc = ref neg_infinity in
              for k = i + 1 to j - List.length rest do
                let a = inside_nt x i k in
                if a <> neg_infinity then
                  acc := log_add !acc (a +. seq_inside rest k j)
              done;
              !acc
        in
        Hashtbl.replace smemo (rhs, i, j) v;
        v
  in
  (n, inside_nt, seq_inside)

let log_inside prep tokens =
  let n, inside_nt, _ = make_log_inside prep tokens in
  let probability = inside_nt prep.start 0 n in
  if probability = neg_infinity then None else Some probability

let inside prep tokens =
  match log_inside prep tokens with None -> 0.0 | Some probability -> exp probability

let log_viterbi prep tokens =
  let n = List.length tokens in
  let w = Array.of_list tokens in
  let vmemo = Hashtbl.create 1024 in
  let smemo = Hashtbl.create 1024 in
  let rec vnt nt i j =
    if j <= i then (neg_infinity, None)
    else
      match Hashtbl.find_opt vmemo (nt, i, j) with
      | Some v -> v
      | None ->
          let idxs =
            Option.value ~default:[] (Hashtbl.find_opt prep.by_lhs nt)
          in
          let bestp = ref neg_infinity and bestt = ref None in
          List.iter
            (fun pi ->
              let p = prep.prods.(pi) in
              let sp, sch = seq_vit p.rhs i j in
              if prep.probs.(pi) > 0.0 && sp <> neg_infinity then begin
                let v = log prep.probs.(pi) +. sp in
                if v > !bestp then begin
                  bestp := v;
                  bestt :=
                    (match sch with
                    | Some ch -> Some (Node (nt, ch))
                    | None -> None)
                end
              end)
            idxs;
          let res = (!bestp, !bestt) in
          Hashtbl.replace vmemo (nt, i, j) res;
          res
  and seq_vit rhs i j =
    match Hashtbl.find_opt smemo (rhs, i, j) with
    | Some v -> v
    | None ->
        let v =
          match rhs with
          | [] -> if i = j then (0.0, Some []) else (neg_infinity, None)
          | Grammar.Term a :: rest ->
              if i < n && String.equal w.(i) a then (
                match seq_vit rest (i + 1) j with
                | p, Some ts -> (p, Some (Leaf a :: ts))
                | z -> z)
              else (neg_infinity, None)
          | Grammar.Nonterm x :: rest ->
              let bestp = ref neg_infinity and bestch = ref None in
              for k = i + 1 to j - List.length rest do
                let px, tx = vnt x i k in
                if px <> neg_infinity then begin
                  let pr, tr = seq_vit rest k j in
                  if pr <> neg_infinity then begin
                    let v = px +. pr in
                    if v > !bestp then begin
                      bestp := v;
                      bestch :=
                        (match (tx, tr) with
                        | Some tx, Some tr -> Some (tx :: tr)
                        | _ -> None)
                    end
                  end
                end
              done;
              (!bestp, !bestch)
        in
        Hashtbl.replace smemo (rhs, i, j) v;
        v
  in
  vnt prep.start 0 n

let viterbi prep tokens =
  let log_probability, tree = log_viterbi prep tokens in
  (exp log_probability, tree)

let tree_to_string ?(indent = 0) tree =
  let rec go indent tree =
    let pad = String.make (2 * indent) ' ' in
    match tree with
    | Leaf s -> pad ^ s
    | Node (nt, children) ->
        pad ^ nt ^ "\n"
        ^ String.concat "\n" (List.map (go (indent + 1)) children)
  in
  go indent tree

let expected_counts_log prep tokens =
  let n, inside_nt, seq_inside = make_log_inside prep tokens in
  let ptotal = inside_nt prep.start 0 n in
  let np = Array.length prep.prods in
  if ptotal = neg_infinity then (Array.make np 0.0, neg_infinity)
  else begin
    let omemo = Hashtbl.create 1024 in
    let get_o nt i j =
      Option.value ~default:neg_infinity (Hashtbl.find_opt omemo (nt, i, j))
    in
    let add_o nt i j v =
      Hashtbl.replace omemo (nt, i, j) (log_add (get_o nt i j) v)
    in
    add_o prep.start 0 n 0.0;
    for len = n downto 1 do
      for p = 0 to n - len do
        let q = p + len in
        List.iter
          (fun b ->
            let ob = get_o b p q in
            if ob <> neg_infinity then
              List.iter
                (fun pi ->
                  let prod = prep.prods.(pi) in
                  if String.equal prod.lhs b then begin
                    let prob = prep.probs.(pi) in
                    if prob > 0.0 then begin
                      let arr = Array.of_list prod.rhs in
                      let m = Array.length arr in
                      Array.iteri
                        (fun k s ->
                          match s with
                          | Grammar.Nonterm x ->
                              let left =
                                Array.to_list (Array.sub arr 0 k)
                              in
                              let right =
                                Array.to_list
                                  (Array.sub arr (k + 1) (m - k - 1))
                              in
                              for i = p to q do
                                let lw = seq_inside left p i in
                                if lw <> neg_infinity then
                                  for j = i to q do
                                    let rw = seq_inside right j q in
                                    if rw <> neg_infinity then
                                      add_o x i j
                                        (ob +. log prob +. lw +. rw)
                                  done
                              done
                          | Grammar.Term _ -> ())
                        arr
                    end
                  end)
                (Option.value ~default:[]
                   (Hashtbl.find_opt prep.by_lhs b)))
          prep.lhs_list
      done
    done;
    let counts = Array.make np 0.0 in
    Array.iteri
      (fun pi (prod : Grammar.production) ->
        let prob = prep.probs.(pi) in
        let s = ref neg_infinity in
        for i = 0 to n do
          for j = i to n do
            let o = get_o prod.lhs i j in
            if o <> neg_infinity then
              s := log_add !s (o +. seq_inside prod.rhs i j)
          done
        done;
        counts.(pi) <-
          if prob <= 0.0 || !s = neg_infinity then 0.0
          else exp (log prob +. !s -. ptotal))
      prep.prods;
    (counts, ptotal)
  end

let expected_counts prep tokens =
  let counts, probability = expected_counts_log prep tokens in
  (counts, exp probability)

let fit_em prep (corpus : Corpus.t) ~iters ~tol =
  let np = Array.length prep.prods in
  let expectation () =
    let acc = Array.make np 0.0 in
    let ll = ref 0.0 in
    List.iter
      (fun s ->
        if s.Corpus.count <> 0.0 then begin
          let cnt, log_probability = expected_counts_log prep s.Corpus.tokens in
          if log_probability = neg_infinity then ll := neg_infinity
          else begin
            Array.iteri
              (fun i x -> acc.(i) <- acc.(i) +. (s.Corpus.count *. x))
              cnt;
            ll := !ll +. (s.Corpus.count *. log_probability)
          end
        end)
      corpus;
    (acc, !ll)
  in
  let initial_counts, initial_ll = expectation () in
  let counts = ref initial_counts and ll = ref initial_ll in
  (try
     for _ = 1 to iters do
       Hashtbl.iter
         (fun _ idxs ->
           let tot = List.fold_left (fun s i -> s +. (!counts).(i)) 0.0 idxs in
           if tot > 0.0 then
             List.iter (fun i -> prep.probs.(i) <- (!counts).(i) /. tot) idxs)
         prep.by_lhs;
       let next_counts, next_ll = expectation () in
       let converged = Float.is_finite !ll && abs_float (next_ll -. !ll) < tol in
       counts := next_counts;
       ll := next_ll;
       if converged then raise Exit
     done
   with Exit -> ());
  (!counts, !ll)
