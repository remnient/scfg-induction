type step = {
  transform : Transform.t;
  parent : Grammar.t;
  result : Grammar.t;
  parent_score : float;
  score : float;
}

type proposal = {
  iteration : int;
  transform : Transform.t;
  parent_key : string;
  score : float;
  accepted : bool;
}

type entry = { g : Grammar.t; score : float; hist : step list }

type result = {
  best : Grammar.t;
  best_score : float;
  initial_score : float;
  steps : step list;
  proposals : proposal list;
  iterations : int;
}

let key_of = Grammar.canonical_string

let transform_key (s : step) =
  (key_of s.parent, Transform.describe s.transform)

let compare_entries (a : entry) (b : entry) =
  let score_order = compare b.score a.score in
  if score_order <> 0 then score_order
  else
    let structure_order = String.compare (key_of a.g) (key_of b.g) in
    if structure_order <> 0 then structure_order
    else
      compare
        (List.sort compare a.g.Grammar.productions, List.rev_map transform_key a.hist)
        (List.sort compare b.g.Grammar.productions, List.rev_map transform_key b.hist)

let run ~config ~beam_width ~max_steps ~patience ?(on_step = fun _ _ -> ()) g0
    corpus =
  let score g = Scoring.posterior ~config g corpus in
  let s0 = score g0 in
  let beam = ref [ { g = g0; score = s0; hist = [] } ] in
  let best = ref { g = g0; score = s0; hist = [] } in
  let proposals = ref [] in
  let accepted = Hashtbl.create 64 in
  let no_improve = ref 0 in
  let iter = ref 0 in
  let stop = ref false in
  while (not !stop) && !iter < max_steps do
    incr iter;
    let cands =
      List.concat_map
        (fun e ->
          List.filter_map
            (fun t ->
              let g' = Grammar.normalize (Transform.apply ~occurrence:config.chunk_occurrence e.g t) in
              let s' = score g' in
              if s' = neg_infinity then None
              else
                let step =
                  {
                    transform = t;
                    parent = e.g;
                    result = g';
                    parent_score = e.score;
                    score = s';
                  }
                in
                Some { g = g'; score = s'; hist = step :: e.hist })
            (Transform.candidates e.g config))
        !beam
    in
    let tbl = Hashtbl.create 128 in
    List.iter
      (fun e ->
        let k = key_of e.g in
        match Hashtbl.find_opt tbl k with
        | Some e0 when compare_entries e0 e <= 0 -> ()
        | _ -> Hashtbl.replace tbl k e)
      cands;
    let cands = Hashtbl.fold (fun _ e acc -> e :: acc) tbl [] |> List.sort compare_entries in
    List.iter
      (fun e ->
        match e.hist with
        | step :: _ ->
            proposals :=
              {
                iteration = !iter;
                transform = step.transform;
                parent_key = key_of step.parent;
                score = e.score;
                accepted = false;
              }
              :: !proposals
        | [] -> ())
      cands;
    let newbeam = List.filteri (fun i _ -> i < beam_width) cands in
    (match newbeam with
    | e :: _ when e.score > !best.score +. 1e-9 ->
        best := e;
        (match e.hist with
        | step :: _ ->
            Hashtbl.replace accepted (transform_key step) ();
            on_step !iter step
        | [] -> ());
        no_improve := 0
    | _ -> incr no_improve);
    beam := newbeam;
    if newbeam = [] then stop := true;
    if !no_improve >= patience then stop := true
  done;
  let steps = List.rev !best.hist in
  let proposals =
    List.rev !proposals
    |> List.map (fun p ->
           {
             p with
             accepted =
               Hashtbl.mem accepted
                 (p.parent_key, Transform.describe p.transform);
           })
  in
  {
    best = !best.g;
    best_score = !best.score;
    initial_score = s0;
    steps;
    proposals;
    iterations = !iter;
  }

let run_best_first ~config ~frontier_cap ~max_expansions ~patience g0 corpus =
  let score g = Scoring.posterior ~config g corpus in
  let s0 = score g0 in
  let frontier = ref [ { g = g0; score = s0; hist = [] } ] in
  let best = ref { g = g0; score = s0; hist = [] } in
  let proposals = ref [] in
  let accepted = Hashtbl.create 64 in
  let no_improve = ref 0 in
  let expansions = ref 0 in
  let iter = ref 0 in
  let dedupe entries =
    let tbl = Hashtbl.create 256 in
    List.iter
      (fun e ->
        let k = key_of e.g in
        match Hashtbl.find_opt tbl k with
        | Some e0 when compare_entries e0 e <= 0 -> ()
        | _ -> Hashtbl.replace tbl k e)
      entries;
    Hashtbl.fold (fun _ e acc -> e :: acc) tbl []
  in
  while
    !frontier <> [] && !expansions < max_expansions && !no_improve < patience
  do
    incr iter;
    let sorted = List.sort compare_entries !frontier in
    let e = List.hd sorted in
    frontier := List.tl sorted;
    incr expansions;
    let cands =
      List.filter_map
        (fun t ->
          let g' = Grammar.normalize (Transform.apply ~occurrence:config.chunk_occurrence e.g t) in
          let s' = score g' in
          if s' = neg_infinity then None
          else
            Some
              {
                g = g';
                score = s';
                hist =
                  {
                    transform = t;
                    parent = e.g;
                    result = g';
                    parent_score = e.score;
                    score = s';
                  }
                  :: e.hist;
              })
        (Transform.candidates e.g config)
      |> List.sort compare_entries
    in
    List.iter
      (fun c ->
        match c.hist with
        | step :: _ ->
            proposals :=
              {
                iteration = !iter;
                transform = step.transform;
                parent_key = key_of step.parent;
                score = c.score;
                accepted = false;
              }
              :: !proposals
        | [] -> ())
      cands;
    let candidate =
      List.fold_left
        (fun best candidate -> if compare_entries candidate best < 0 then candidate else best)
        e cands
    in
    if candidate.score > !best.score +. 1e-9 then begin
      best := candidate;
      (match candidate.hist with
      | step :: _ -> Hashtbl.replace accepted (transform_key step) ()
      | [] -> ());
      no_improve := 0
    end
    else incr no_improve;
    frontier := cands @ !frontier |> dedupe;
    let sorted = List.sort compare_entries !frontier in
    frontier := List.filteri (fun i _ -> i < frontier_cap) sorted
  done;
  let steps = List.rev !best.hist in
  let proposals =
    List.rev !proposals
    |> List.map (fun p ->
           {
             p with
             accepted =
               Hashtbl.mem accepted
                 (p.parent_key, Transform.describe p.transform);
           })
  in
  {
    best = !best.g;
    best_score = !best.score;
    initial_score = s0;
    steps;
    proposals;
    iterations = !iter;
  }

let proposals_to_tsv result =
  let header = "iteration\tparent_key\ttransform\tscore\taccepted" in
  let rows =
    List.map
      (fun p ->
        Printf.sprintf "%d\t%s\t%s\t%.10g\t%b" p.iteration
          (String.concat "\\n" (String.split_on_char '\n' p.parent_key))
          (Transform.describe p.transform)
          p.score p.accepted)
      result.proposals
  in
  String.concat "\n" (header :: rows)

let steps_to_tsv result =
  let header = "step\tparent_score\tscore\tdelta\ttransform" in
  let rows =
    List.mapi
      (fun i (s : step) ->
        Printf.sprintf "%d\t%.10g\t%.10g\t%.10g\t%s" (i + 1) s.parent_score
          s.score (s.score -. s.parent_score)
          (Transform.describe s.transform))
      result.steps
  in
  String.concat "\n" (header :: rows)
