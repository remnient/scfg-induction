type symbol = Term of string | Nonterm of string

type production = {
  lhs : string;
  rhs : symbol list;
  count : float;
}

type t = {
  start : string;
  productions : production list;
}

module SSet = Set.Make (String)

let symbol_to_string = function Term s -> s | Nonterm s -> s

let symbol_key = function Term s -> "t:" ^ s | Nonterm s -> "n:" ^ s

let symbol_is_nonterm = function Nonterm _ -> true | Term _ -> false

let equal_symbol a b =
  match (a, b) with
  | Term x, Term y | Nonterm x, Nonterm y -> String.equal x y
  | _ -> false

let equal_rhs a b =
  List.length a = List.length b && List.for_all2 equal_symbol a b

let rhs_to_string rhs = String.concat " " (List.map symbol_to_string rhs)

let production_to_string p =
  Printf.sprintf "%s -> %s" p.lhs (rhs_to_string p.rhs)

let make ~start productions = { start; productions }

let nonterminals g =
  let acc = ref (SSet.singleton g.start) in
  List.iter
    (fun p ->
      acc := SSet.add p.lhs !acc;
      List.iter
        (function Nonterm x -> acc := SSet.add x !acc | Term _ -> ())
        p.rhs)
    g.productions;
  SSet.elements !acc

let terminals g =
  let acc = ref SSet.empty in
  List.iter
    (fun p ->
      List.iter
        (function Term x -> acc := SSet.add x !acc | Nonterm _ -> ())
        p.rhs)
    g.productions;
  SSet.elements !acc

let productions_of g lhs =
  List.filter (fun p -> String.equal p.lhs lhs) g.productions

let total_count prods = List.fold_left (fun s p -> s +. p.count) 0.0 prods

let probabilities g =
  let by_lhs = Hashtbl.create 64 in
  List.iter
    (fun p ->
      let l =
        match Hashtbl.find_opt by_lhs p.lhs with Some l -> l | None -> []
      in
      Hashtbl.replace by_lhs p.lhs (p :: l))
    g.productions;
  let tbl = Hashtbl.create 64 in
  Hashtbl.iter
    (fun lhs ps ->
      let ps = List.rev ps in
      let tot = total_count ps in
      let k = List.length ps in
      let probs =
        if tot > 0.0 then List.map (fun p -> (p, p.count /. tot)) ps
        else List.map (fun p -> (p, 1.0 /. float_of_int k)) ps
      in
      Hashtbl.replace tbl lhs probs)
    by_lhs;
  tbl

let canonical_string g =
  let nts = nonterminals g in
  let signature colors nt =
    let symbol = function
      | Term value -> Printf.sprintf "t%d:%s" (String.length value) value
      | Nonterm value -> Printf.sprintf "n%d" (Hashtbl.find colors value)
    in
    let productions =
      productions_of g nt
      |> List.map (fun p ->
             "[" ^ String.concat ";" (List.map symbol p.rhs) ^ "]")
      |> List.sort String.compare
    in
    Printf.sprintf "%d|%b|%s" (Hashtbl.find colors nt)
      (String.equal nt g.start) (String.concat "|" productions)
  in
  let refine colors =
    let rec loop colors =
      let signatures = List.map (fun nt -> (nt, signature colors nt)) nts in
      let unique =
        signatures |> List.map snd |> List.sort_uniq String.compare
      in
      let ids = Hashtbl.create (List.length unique) in
      List.iteri (fun index key -> Hashtbl.replace ids key index) unique;
      let next = Hashtbl.create (List.length nts) in
      List.iter
        (fun (nt, key) -> Hashtbl.replace next nt (Hashtbl.find ids key))
        signatures;
      if
        List.for_all
          (fun nt -> Hashtbl.find colors nt = Hashtbl.find next nt)
          nts
      then next
      else loop next
    in
    loop colors
  in
  let encode colors =
    let order =
      List.sort
        (fun left right ->
          compare (Hashtbl.find colors left) (Hashtbl.find colors right))
        nts
    in
    let names = Hashtbl.create (List.length order) in
    List.iteri
      (fun index nt -> Hashtbl.replace names nt (Printf.sprintf "N%d" index))
      order;
    let symbol = function
      | Term value -> Printf.sprintf "t%d:%s" (String.length value) value
      | Nonterm value -> Hashtbl.find names value
    in
    g.productions
    |> List.map (fun p ->
           Printf.sprintf "%s -> %s" (Hashtbl.find names p.lhs)
             (String.concat " " (List.map symbol p.rhs)))
    |> List.sort String.compare |> String.concat "\n"
  in
  let rec canonical colors =
    let colors = refine colors in
    let classes = Hashtbl.create (List.length nts) in
    List.iter
      (fun nt ->
        let color = Hashtbl.find colors nt in
        let members =
          Option.value ~default:[] (Hashtbl.find_opt classes color)
        in
        Hashtbl.replace classes color (nt :: members))
      nts;
    let ambiguous =
      Hashtbl.fold
        (fun color members acc ->
          if List.length members > 1 then (color, members) :: acc else acc)
        classes []
      |> List.sort (fun (left, _) (right, _) -> compare left right)
    in
    match ambiguous with
    | [] -> encode colors
    | (_, members) :: _ ->
        let fresh =
          List.fold_left
            (fun highest nt -> max highest (Hashtbl.find colors nt))
            (-1) nts
          + 1
        in
        members
        |> List.map (fun chosen ->
               let branch = Hashtbl.copy colors in
               Hashtbl.replace branch chosen fresh;
               canonical branch)
        |> List.sort String.compare |> List.hd
  in
  let colors = Hashtbl.create (List.length nts) in
  List.iter
    (fun nt ->
      Hashtbl.replace colors nt (if String.equal nt g.start then 0 else 1))
    nts;
  canonical colors

let equal_structure a b = String.equal (canonical_string a) (canonical_string b)

let copy_with g productions = { g with productions }

let prods_of_list prods lhs =
  List.filter (fun p -> String.equal p.lhs lhs) prods

let dedupe prods =
  let tbl = Hashtbl.create 64 in
  List.iter
    (fun p ->
      match Hashtbl.find_opt tbl (p.lhs, p.rhs) with
      | Some c -> Hashtbl.replace tbl (p.lhs, p.rhs) (c +. p.count)
      | None -> Hashtbl.replace tbl (p.lhs, p.rhs) p.count)
    prods;
  Hashtbl.fold (fun (lhs, rhs) count acc -> { lhs; rhs; count } :: acc) tbl []

let remove_unit_cycles prods =
  let unit_edges = Hashtbl.create 64 in
  List.iter
    (fun (p : production) ->
      match p.rhs with
      | [ Nonterm b ] ->
          let l =
            match Hashtbl.find_opt unit_edges p.lhs with
            | Some l -> l
            | None -> []
          in
          Hashtbl.replace unit_edges p.lhs (b :: l)
      | _ -> ())
    prods;
  let reaches a target =
    let seen = Hashtbl.create 16 in
    let rec go x =
      if String.equal x target then true
      else if Hashtbl.mem seen x then false
      else begin
        Hashtbl.replace seen x ();
        List.exists go
          (Option.value ~default:[] (Hashtbl.find_opt unit_edges x))
      end
    in
    go a
  in
  let nts = List.map (fun p -> p.lhs) prods |> List.sort_uniq String.compare in
  List.concat_map
    (fun lhs ->
      let members =
        List.filter (fun nt -> reaches lhs nt && reaches nt lhs) nts
      in
      List.filter_map
        (fun p ->
          if not (List.mem p.lhs members) then None
          else
            match p.rhs with
            | [ Nonterm child ] when List.mem child members -> None
            | _ -> Some { p with lhs })
        prods)
    nts
  |> dedupe

let productive_set prods =
  let tbl = Hashtbl.create 64 in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun p ->
        if not (Hashtbl.mem tbl p.lhs) then begin
          let ok =
            List.for_all
              (function Term _ -> true | Nonterm x -> Hashtbl.mem tbl x)
              p.rhs
          in
          if ok then begin
            Hashtbl.replace tbl p.lhs ();
            changed := true
          end
        end)
      prods
  done;
  tbl

let remove_nonproductive prods =
  let prod = productive_set prods in
  List.filter
    (fun p ->
      Hashtbl.mem prod p.lhs
      && List.for_all
           (function Term _ -> true | Nonterm x -> Hashtbl.mem prod x)
           p.rhs)
    prods

let remove_unreachable start prods =
  let tbl = Hashtbl.create 64 in
  Hashtbl.replace tbl start ();
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun p ->
        if Hashtbl.mem tbl p.lhs then
          List.iter
            (function
              | Nonterm x ->
                  if not (Hashtbl.mem tbl x) then begin
                    Hashtbl.replace tbl x ();
                    changed := true
                  end
              | Term _ -> ())
            p.rhs)
      prods
  done;
  List.filter (fun p -> Hashtbl.mem tbl p.lhs) prods

let derives_form g start target =
  let n = List.length target in
  let arr = Array.of_list target in
  let key = symbol_key in
  let d = Array.make_matrix (n + 1) (n + 1) SSet.empty in
  for i = 0 to n - 1 do
    d.(i).(i + 1) <- SSet.singleton (key arr.(i))
  done;
  let rhs_matches rhs i j =
    let rec go rhs p =
      match rhs with
      | [] -> p = j
      | [ last ] -> p < j && SSet.mem (key last) d.(p).(j)
      | s :: rest ->
          let rem = List.length rest in
          let rec try_q q =
            if q > j - rem then false
            else if SSet.mem (key s) d.(p).(q) && go rest q then true
            else try_q (q + 1)
          in
          try_q (p + 1)
    in
    List.length rhs > 0 && go rhs i
  in
  for len = 1 to n do
    for i = 0 to n - len do
      let j = i + len in
      let changed = ref true in
      while !changed do
        changed := false;
        List.iter
          (fun (p : production) ->
            let lhs_key = key (Nonterm p.lhs) in
            if not (SSet.mem lhs_key d.(i).(j)) then begin
              let ok =
                match p.rhs with
                | [ y ] -> SSet.mem (key y) d.(i).(j)
                | _ -> rhs_matches p.rhs i j
              in
              if ok then begin
                d.(i).(j) <- SSet.add lhs_key d.(i).(j);
                changed := true
              end
            end)
          g.productions
      done
    done
  done;
  SSet.mem (key (Nonterm start)) d.(0).(n)

let prune_redundant g =
  let prods = ref (dedupe g.productions) in
  let changed = ref true in
  while !changed do
    changed := false;
    let victim = ref None in
    (try
       List.iter
         (fun (p : production) ->
           let g' =
             { g with productions = List.filter (fun q -> not (q == p)) !prods }
           in
           if derives_form g' p.lhs p.rhs then begin
             victim := Some p;
             raise Exit
           end)
         !prods
     with Exit -> ());
    match !victim with
    | Some p ->
        prods := List.filter (fun q -> not (q == p)) !prods;
        changed := true
    | None -> ()
  done;
  { g with productions = !prods }

let normalize g =
  let step prods =
    prods |> dedupe |> remove_unit_cycles |> remove_nonproductive
    |> remove_unreachable g.start
  in
  let p1 = step g.productions in
  let p2 = step p1 in
  let g1 = { g with productions = p2 } in
  let g2 = prune_redundant g1 in
  let g3 = step g2.productions in
  { g with productions = g3 }

let language_up_to g max_len =
  let tbl = Hashtbl.create 256 in
  let get x len =
    Option.value ~default:[] (Hashtbl.find_opt tbl (x, len))
  in
  for len = 1 to max_len do

    let changed = ref true in
    while !changed do
      changed := false;
      List.iter
        (fun x ->
          let acc = ref (get x len) in
          List.iter
            (fun (p : production) ->
              let rhs = p.rhs in
              let m = List.length rhs in
              let rec gen rhs l =
                match rhs with
                | [] -> if l = 0 then [ [] ] else []
                | s :: rest ->
                    let out = ref [] in
                    for k = 1 to l - (List.length rest) do
                      let ss =
                        match s with
                        | Term a -> if k = 1 then [ [ a ] ] else []
                        | Nonterm y -> get y k
                      in
                      let rs = gen rest (l - k) in
                      List.iter
                        (fun a ->
                          List.iter (fun b -> out := (a @ b) :: !out) rs)
                        ss
                    done;
                    !out
              in
              if len >= m then acc := gen rhs len @ !acc)
            (productions_of g x);
          let acc = List.sort_uniq compare !acc in
          if List.length acc > List.length (get x len) then begin
            Hashtbl.replace tbl (x, len) acc;
            changed := true
          end)
        (nonterminals g)
    done
  done;
  let all = List.concat (List.init max_len (fun i -> get g.start (i + 1))) in
  List.sort_uniq compare all

let initial_grammar ?(start = "S") samples =
  let term_nts = Hashtbl.create 64 in
  let prods = ref [] in
  List.iter
    (fun (tokens, count) ->
      let rhs =
        List.map
          (fun tok ->
            match Hashtbl.find_opt term_nts tok with
            | Some nt -> Nonterm nt
            | None ->
                let nt = "T_" ^ tok in
                Hashtbl.replace term_nts tok nt;
                prods := { lhs = nt; rhs = [ Term tok ]; count = 1.0 } :: !prods;
                Nonterm nt)
          tokens
      in
      prods := { lhs = start; rhs; count } :: !prods)
    samples;
  make ~start (List.rev !prods)

let is_recursive g =
  let deps = Hashtbl.create 64 in
  List.iter
    (fun x ->
      let l =
        List.concat_map
          (fun p ->
            List.filter_map
              (function Nonterm y -> Some y | Term _ -> None)
              p.rhs)
          (productions_of g x)
      in
      Hashtbl.replace deps x l)
    (nonterminals g);
  List.exists
    (fun a ->
      let seen = Hashtbl.create 64 in
      let rec go x =
        List.exists
          (fun y ->
            if String.equal y a then true
            else if Hashtbl.mem seen y then false
            else begin
              Hashtbl.replace seen y ();
              go y
            end)
          (Option.value ~default:[] (Hashtbl.find_opt deps x))
      in
      go a)
    (nonterminals g)

let to_string ?(decimals = 3) g =
  let probs = probabilities g in
  let fmt p =
    let pr =
      match Hashtbl.find_opt probs p.lhs with
      | None -> 0.0
      | Some l -> (
          match List.find_opt (fun (q, _) -> q == p) l with
          | Some (_, x) -> x
          | None -> 0.0)
    in
    Printf.sprintf "%-8s -> %-24s [%.*f]" p.lhs (rhs_to_string p.rhs) decimals
      pr
  in
  let header =
    Printf.sprintf "# start = %s, %d nonterminals, %d terminals, %d productions"
      g.start
      (List.length (nonterminals g))
      (List.length (terminals g))
      (List.length g.productions)
  in
  String.concat "\n" (header :: List.map fmt g.productions)

let is_nonterminal_name s =
  String.length s > 0
  &&
  let c = s.[0] in
  (c >= 'A' && c <= 'Z') || c = '_' || c = '<'

let find_sub s sub =
  let n = String.length s and m = String.length sub in
  let rec go i =
    if i + m > n then None
    else if String.equal (String.sub s i m) sub then Some i
    else go (i + 1)
  in
  go 0

let parse_start line =
  match find_sub line "start =" with
  | None -> None
  | Some i ->
      let rest =
        String.sub line (i + 7) (String.length line - i - 7) |> String.trim
      in
      let stop =
        match (String.index_opt rest ' ', String.index_opt rest ',') with
        | Some a, Some b -> min a b
        | Some a, None | None, Some a -> a
        | None, None -> String.length rest
      in
      let name = String.sub rest 0 stop in
      if String.length name = 0 then None else Some name

let of_string text =
  let lines = String.split_on_char '\n' text in
  let prods = ref [] in
  let start = ref None in
  List.iter
    (fun raw ->
      let trimmed = String.trim raw in
      if String.length trimmed > 0 && trimmed.[0] = '#' then
        match parse_start trimmed with
        | Some s -> start := Some s
        | None -> ()
      else begin
        let line =
          match String.index_opt raw '#' with
          | Some i -> String.sub raw 0 i
          | None -> raw
        in
        let toks =
          String.split_on_char ' ' (String.trim line)
          |> List.filter (fun s -> String.length s > 0)
        in
        match toks with
        | [] -> ()
        | lhs :: arrow :: rhs_toks when String.equal arrow "->" ->
            let rhs_toks, prob =
              match List.rev rhs_toks with
              | last :: rest_rev
                when String.length last > 2 && last.[0] = '[' -> (
                  match
                    float_of_string_opt
                      (String.sub last 1 (String.length last - 2))
                  with
                  | Some p -> (List.rev rest_rev, Some p)
                  | None -> (rhs_toks, None))
              | _ -> (rhs_toks, None)
            in
            let rhs =
              List.map
                (fun s -> if is_nonterminal_name s then Nonterm s else Term s)
                rhs_toks
            in
            if !start = None then start := Some lhs;
            prods :=
              { lhs; rhs; count = Option.value ~default:1.0 prob } :: !prods
        | _ -> ()
      end)
    lines;
  let start = Option.value ~default:"S" !start in
  make ~start (List.rev !prods)
