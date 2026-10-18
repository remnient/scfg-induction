open Scfg

let failures = ref 0

let check name cond =
  if cond then Printf.printf "ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end;
  flush stdout

let approx ?(tol = 1e-9) a b = abs_float (a -. b) < tol

let nt s = Grammar.Nonterm s
let tm s = Grammar.Term s
let prod lhs rhs = { Grammar.lhs; rhs; count = 1.0 }
let g start ps = Grammar.make ~start ps

let has_prod g lhs rhs =
  List.exists
    (fun (p : Grammar.production) ->
      String.equal p.lhs lhs && Grammar.equal_rhs p.rhs rhs)
    g.Grammar.productions

let sample tokens count = { Corpus.tokens; count }

let () =
  check "log_gamma(1)=0" (approx (Scoring.log_gamma 1.0) 0.0);
  check "log_gamma(2)=0" (approx (Scoring.log_gamma 2.0) 0.0);
  check "log_gamma(1/2)=log sqrt pi"
    (approx (Scoring.log_gamma 0.5) (0.5 *. log Float.pi));
  check "log_gamma(3)=log 2"
    (approx (Scoring.log_gamma 3.0) (log 2.0))

let () =
  let amb = g "S" [ prod "S" [ nt "S"; nt "S" ]; prod "S" [ tm "a" ] ] in
  let prep = Parse.prepare amb in
  check "P(a) = 1/2" (approx (Parse.inside prep [ "a" ]) 0.5);
  check "P(aa) = 1/8" (approx (Parse.inside prep [ "a"; "a" ]) 0.125);
  check "P(aaa) = 1/16" (approx (Parse.inside prep [ "a"; "a"; "a" ]) 0.0625);
  let vp, vt = Parse.viterbi prep [ "a"; "a" ] in
  check "viterbi P(aa) = 1/8" (approx vp 0.125);
  check "viterbi tree exists" (vt <> None)

let () =
  let recursive =
    g "S"
      [ { Grammar.lhs = "S"; rhs = [ tm "a"; nt "S" ]; count = 1.0 };
        { Grammar.lhs = "S"; rhs = [ tm "a" ]; count = 999.0 } ]
  in
  let tokens = List.init 120 (fun _ -> "a") in
  match Parse.log_inside (Parse.prepare recursive) tokens with
  | Some probability ->
      check "log inside survives probability underflow"
        (Float.is_finite probability && probability < -700.0)
  | None -> check "log inside survives probability underflow" false

let () =
  let gr = g "S" [ prod "S" [ nt "A"; nt "B" ]; prod "A" [ tm "a" ]; prod "B" [ tm "b" ] ] in
  let prep = Parse.prepare gr in
  let cnt, p = Parse.expected_counts prep [ "a"; "b" ] in
  check "inside(ab)=1" (approx p 1.0);
  check "E[count S->AB]=1" (approx cnt.(0) 1.0);
  check "E[count A->a]=1" (approx cnt.(1) 1.0);
  check "E[count B->b]=1" (approx cnt.(2) 1.0)

let () =
  let amb = g "S" [ prod "S" [ nt "S"; nt "S" ]; prod "S" [ tm "a" ] ] in
  let prep = Parse.prepare amb in
  let cnt, _ = Parse.expected_counts prep [ "a"; "a" ] in
  check "E[count S->SS]=1" (approx cnt.(0) 1.0);
  check "E[count S->a]=2" (approx cnt.(1) 2.0)

let () =
  let gd =
    g "S"
      [ prod "S" [ tm "a" ];
        { Grammar.lhs = "S"; rhs = [ tm "a" ]; count = 2.0 } ]
  in
  let gn = Grammar.normalize gd in
  check "dedupe keeps one production"
    (List.length gn.Grammar.productions = 1);
  check "dedupe sums counts"
    (approx (List.hd gn.Grammar.productions).Grammar.count 3.0)

let () =
  let left =
    g "S"
      [ prod "S" [ nt "A" ]; prod "S" [ nt "B" ]; prod "A" [ tm "a" ];
        prod "B" [ tm "b" ] ]
  in
  let reordered =
    g "S"
      [ prod "S" [ nt "B" ]; prod "S" [ nt "A" ]; prod "B" [ tm "b" ];
        prod "A" [ tm "a" ] ]
  in
  let renamed =
    g "Root"
      [ prod "Root" [ nt "Right" ]; prod "Left" [ tm "a" ];
        prod "Root" [ nt "Left" ]; prod "Right" [ tm "b" ] ]
  in
  check "canonical form ignores production order"
    (Grammar.equal_structure left reordered);
  check "canonical form ignores nonterminal names"
    (Grammar.equal_structure left renamed)

let () =
  let gs = g "S" [ prod "S" [ nt "S" ]; prod "S" [ tm "a" ] ] in
  let gn = Grammar.normalize gs in
  check "self-loop removed"
    (not (has_prod gn "S" [ nt "S" ]));
  check "self-loop grammar keeps S->a" (has_prod gn "S" [ tm "a" ])

let () =
  let gc =
    Grammar.make ~start:"A"
      [ prod "A" [ nt "B" ]; prod "B" [ nt "A" ]; prod "A" [ tm "a" ] ]
  in
  let gn = Grammar.normalize gc in
  check "unit cycle removed" (not (has_prod gn "A" [ nt "B" ]));
  check "unit cycle grammar keeps A->a" (has_prod gn "A" [ tm "a" ])

let () =
  let gu =
    g "S" [ prod "S" [ nt "A" ]; prod "A" [ nt "B" ]; prod "B" [ tm "a" ] ]
  in
  let gn = Grammar.normalize gu in
  check "unit productions are preserved" (has_prod gn "S" [ nt "A" ]);
  check "unit productions chain preserved" (has_prod gn "A" [ nt "B" ])

let () =
  List.iter
    (fun (a, b, c) ->
      let gu =
        g "S"
          [ prod "S" [ nt a ]; prod a [ nt b ]; prod b [ nt c ];
            prod c [ tm "a" ] ]
      in
      let counts, probability = Parse.expected_counts (Parse.prepare gu) [ "a" ] in
      check "unit chain probability" (approx probability 1.0);
      Array.iter
        (fun count -> check "unit chain expected count" (approx count 1.0))
        counts)
    [ ("A", "B", "C"); ("X", "Y", "Z"); ("Q", "R", "T") ]

let () =
  let cfg = { Scoring.default_config with alpha = 1.0; em_iters = 5 } in
  let g1 = g "S" [ prod "S" [ tm "a" ] ] in
  let m1, _, _, _ =
    Scoring.approximate_log_evidence ~config:cfg g1 [ sample [ "a" ] 1.0 ]
  in
  check "evidence(S->a, {a}, alpha=1) = 0" (approx m1 0.0);
  let g2 = g "S" [ prod "S" [ tm "a" ]; prod "S" [ tm "b" ] ] in
  let m2, _, _, _ =
    Scoring.approximate_log_evidence ~config:cfg g2 [ sample [ "a" ] 1.0 ]
  in
  check "evidence(S->a|b, {a}, alpha=1) = log 1/2"
    (approx m2 (log 0.5))

let paper_initial () =
  g "S"
    [
      prod "S" [ nt "A"; nt "B" ];
      prod "S" [ nt "A"; nt "A"; nt "B"; nt "B" ];
      prod "S" [ nt "A"; nt "A"; nt "A"; nt "B"; nt "B"; nt "B" ];
      prod "A" [ tm "a" ];
      prod "B" [ tm "b" ];
    ]

let () =
  let g0 = paper_initial () in
  let gc1 = Grammar.normalize (Transform.apply g0 (Transform.Chunk [ nt "A"; nt "B" ])) in
  check "chunk(AB): S->X" (has_prod gc1 "S" [ nt "X" ]);
  check "chunk(AB): S->AXB" (has_prod gc1 "S" [ nt "A"; nt "X"; nt "B" ]);
  check "chunk(AB): S->AAXBB"
    (has_prod gc1 "S" [ nt "A"; nt "A"; nt "X"; nt "B"; nt "B" ]);
  check "chunk(AB): X->AB" (has_prod gc1 "X" [ nt "A"; nt "B" ]);
  check "chunk preserves language"
    (Grammar.language_up_to g0 6 = Grammar.language_up_to gc1 6)

let () =
  let g0 = paper_initial () in
  let gc1 = Grammar.normalize (Transform.apply g0 (Transform.Chunk [ nt "A"; nt "B" ])) in
  let gc2 =
    Grammar.normalize (Transform.apply gc1 (Transform.Chunk [ nt "A"; nt "X"; nt "B" ]))
  in
  check "chunk(AXB): S->Y" (has_prod gc2 "S" [ nt "Y" ]);
  check "chunk(AXB): S->AYB" (has_prod gc2 "S" [ nt "A"; nt "Y"; nt "B" ]);
  check "chunk(AXB): Y->AXB" (has_prod gc2 "Y" [ nt "A"; nt "X"; nt "B" ]);
  let gm = Grammar.normalize (Transform.apply gc2 (Transform.Merge ("S", "Y"))) in
  let gf = Grammar.normalize (Transform.apply gm (Transform.Merge ("S", "X"))) in
  check "final: S->AB" (has_prod gf "S" [ nt "A"; nt "B" ]);
  check "final: S->ASB" (has_prod gf "S" [ nt "A"; nt "S"; nt "B" ]);
  let expected =
    [
      [ "a"; "b" ];
      [ "a"; "a"; "b"; "b" ];
      [ "a"; "a"; "a"; "b"; "b"; "b" ];
      [ "a"; "a"; "a"; "a"; "b"; "b"; "b"; "b" ];
    ]
    |> List.sort compare
  in
  check "final grammar generates a^n b^n"
    (Grammar.language_up_to gf 8 = expected)

let () =
  let g0 =
    g "S"
      [ prod "S" [ nt "A" ]; prod "S" [ nt "B" ]; prod "A" [ tm "a" ];
        prod "B" [ tm "b" ] ]
  in
  let gm = Grammar.normalize (Transform.apply g0 (Transform.Merge ("A", "B"))) in
  check "merge unifies terminals into one nonterminal"
    (List.length (Grammar.terminals gm) = 2
    && List.length
         (List.filter (fun p -> Grammar.symbol_is_nonterm (List.hd p.Grammar.rhs))
            gm.Grammar.productions)
       >= 1);
  check "merge keeps both terminal productions" (has_prod gm "A" [ tm "a" ] && has_prod gm "A" [ tm "b" ])

let () =
  let cfg =
    {
      Scoring.default_config with
      em_iters = 5;
      max_chunk = 3;
      prior_weight = 1.0;
    }
  in
  let corpus = [ sample [ "a"; "b" ] 1.0; sample [ "a"; "a"; "b"; "b" ] 1.0; sample [ "a"; "a"; "a"; "b"; "b"; "b" ] 1.0 ] in
  let result =
    Search.run ~config:cfg ~beam_width:3 ~max_steps:12 ~patience:3
      (paper_initial ()) corpus
  in
  check "search improves the posterior"
    (result.Search.best_score > result.Search.initial_score);
  check "search returns accepted steps"
    (List.length result.Search.steps > 0);
  check "search output generates training strings"
    (List.for_all
       (fun s ->
         List.mem s (Grammar.language_up_to result.Search.best 8))
       [ [ "a"; "b" ]; [ "a"; "a"; "b"; "b" ]; [ "a"; "a"; "a"; "b"; "b"; "b" ] ])

let () =
  let g0 =
    g "S"
      [ prod "S" [ nt "A"; nt "S"; nt "A" ]; prod "S" [ tm "c" ];
        prod "S" [ nt "A"; nt "A"; nt "S"; nt "A"; nt "A" ];
        prod "A" [ tm "a" ] ]
  in
  let gn = Grammar.normalize g0 in
  check "redundant production pruned"
    (not (has_prod gn "S" [ nt "A"; nt "A"; nt "S"; nt "A"; nt "A" ]));
  check "recursive production kept" (has_prod gn "S" [ nt "A"; nt "S"; nt "A" ]);
  check "pruning preserves the language"
    (Grammar.language_up_to g0 5 = Grammar.language_up_to gn 5)

let () =
  let gr =
    g "S" [ prod "S" [ nt "A"; nt "B" ]; prod "A" [ tm "a" ]; prod "B" [ tm "b" ] ]
  in
  let prep = Parse.prepare gr in
  let _, tree = Parse.viterbi prep [ "a"; "b" ] in
  match tree with
  | Some t ->
      check "parse tree yield" (Parse.tree_yield t = [ "a"; "b" ]);
      check "parse tree root" (match t with Parse.Node ("S", _) -> true | _ -> false)
  | None -> check "parse tree yield" false

let () =
  let gr =
    g "S" [ prod "S" [ nt "A"; nt "B" ]; prod "A" [ tm "a" ]; prod "B" [ tm "b" ] ]
  in
  let corpus = [ sample [ "a"; "b" ] 1.0 ] in
  let heldout = Scoring.heldout gr ~train:corpus corpus in
  check "heldout loglik per token = 0"
    (approx heldout.Scoring.average_loglik_per_token 0.0);
  check "heldout parseable" (heldout.Scoring.unparseable_mass = 0.0)

let () =
  let gr = g "S" [ prod "S" [ tm "a" ] ] in
  let train = [ sample [ "a" ] 1.0 ] in
  let test = [ sample [ "a" ] 1.0; sample [ "b" ] 7.0 ] in
  let heldout = Scoring.heldout gr ~train test in
  check "heldout counts weighted unparseable mass"
    (approx heldout.Scoring.unparseable_mass 7.0);
  check "heldout counts all token mass"
    (approx heldout.Scoring.total_tokens 8.0);
  check "heldout reports partial coverage"
    (approx
       (heldout.Scoring.parsed_mass /. heldout.Scoring.total_mass)
       0.125);
  check "unparseable heldout mass has infinite cross entropy"
    (heldout.Scoring.average_loglik_per_token = neg_infinity)

let contains hay needle =
  let n = String.length hay and m = String.length needle in
  let rec go i = if i + m > n then false else if String.sub hay i m = needle then true else go (i + 1) in
  m = 0 || go 0

let () =
  let g0 = g "S" [ prod "S" [ nt "S"; nt "S" ]; prod "S" [ tm "a" ] ] in
  let d = Dot.dot_grammar g0 in
  check "dot numbers repeated rhs symbols in order"
    (contains d "pr_0 -> nt_S [label=\"1\"];"
    && contains d "pr_0 -> nt_S [label=\"2\"];");
  check "dot labels production probability" (contains d "p=0.500");
  check "dot marks the start symbol" (contains d "shape=doublecircle");
  let tree_dot = Dot.dot_tree (Parse.Node ("S", [ Parse.Leaf "a" ])) in
  check "parse tree dot has an edge" (contains tree_dot "->")

let () =
  check "digamma(1)" (approx (Scoring.digamma 1.0) (-0.5772156649015329) ~tol:1e-9);
  check "digamma(2)" (approx (Scoring.digamma 2.0) 0.42278433509846713 ~tol:1e-9)

let () =
  let mk mode =
    { Scoring.default_config with alpha = 1.0; em_iters = 10; mode }
  in
  let corpus = [ sample [ "a" ] 1.0 ] in
  let g1 = g "S" [ prod "S" [ tm "a" ] ] in
  let d1 = Scoring.details ~config:(mk Scoring.Variational) g1 corpus in
  check "variational ELBO (single production) = 0"
    (approx d1.Scoring.posterior 0.0 ~tol:1e-6);
  let g2 = g "S" [ prod "S" [ tm "a" ]; prod "S" [ tm "b" ] ] in
  let dm =
    Scoring.details ~config:(mk Scoring.Approximate_evidence) g2 corpus
  in
  let dv = Scoring.details ~config:(mk Scoring.Variational) g2 corpus in
  check "variational matches approximate evidence (unambiguous)"
    (approx dv.Scoring.posterior dm.Scoring.posterior ~tol:1e-6)

let () =
  let g0 =
    g "S"
      [ prod "S" [ nt "A"; nt "B"; nt "A"; nt "B" ]; prod "A" [ tm "a" ];
        prod "B" [ tm "b" ] ]
  in
  let all =
    Grammar.normalize (Transform.apply g0 (Transform.Chunk [ nt "A"; nt "B" ]))
  in
  let first =
    Grammar.normalize
      (Transform.apply ~occurrence:Scoring.First_occurrence g0
         (Transform.Chunk [ nt "A"; nt "B" ]))
  in
  check "chunk all replaces every occurrence"
    (has_prod all "S" [ nt "X"; nt "X" ]);
  check "chunk first replaces only the leftmost"
    (has_prod first "S" [ nt "X"; nt "A"; nt "B" ])

let () =
  let g0 =
    g "S"
      [ prod "S" [ nt "A"; nt "S"; nt "A" ]; prod "S" [ tm "c" ];
        prod "S" [ nt "A"; nt "A"; nt "A"; nt "S"; nt "A"; nt "A"; nt "A" ];
        prod "A" [ tm "a" ] ]
  in
  let gn = Grammar.normalize g0 in
  check "deeply redundant production pruned"
    (not
       (has_prod gn "S"
          [ nt "A"; nt "A"; nt "A"; nt "S"; nt "A"; nt "A"; nt "A" ]));
  check "deep redundancy preserves language"
    (Grammar.language_up_to g0 7 = Grammar.language_up_to gn 7)

let () =
  let g0 =
    g "S"
      [ prod "S" [ nt "A"; nt "B" ]; prod "S" [ nt "A"; nt "S"; nt "B" ];
        prod "S" [ nt "A"; nt "A"; nt "B" ]; prod "A" [ tm "a" ];
        prod "B" [ tm "b" ] ]
  in
  let gn = Grammar.normalize g0 in
  check "non-redundant production kept"
    (has_prod gn "S" [ nt "A"; nt "A"; nt "B" ])

let () =
  let recursive =
    g "S"
      [ prod "S" [ tm "a"; nt "S" ];
        { Grammar.lhs = "S"; rhs = [ tm "a" ]; count = 999.0 } ]
  in
  let prep = Parse.prepare recursive in
  let tokens = List.init 120 (fun _ -> "a") in
  let log_probability, tree = Parse.log_viterbi prep tokens in
  check "log Viterbi retains an underflowing parse score"
    (approx log_probability ((119.0 *. log 0.001) +. log 0.999));
  check "log Viterbi retains an underflowing parse tree"
    (Option.map Parse.tree_yield tree = Some tokens);
  let probability, tree = Parse.viterbi prep tokens in
  check "probability Viterbi retains the tree when its score underflows"
    (probability = 0.0 && Option.map Parse.tree_yield tree = Some tokens);
  let log_probability, tree = Parse.log_viterbi prep [ "b" ] in
  check "log Viterbi distinguishes an impossible parse"
    (log_probability = neg_infinity && tree = None);
  let amb = g "S" [ prod "S" [ nt "S"; nt "S" ]; prod "S" [ tm "a" ] ] in
  let prep = Parse.prepare amb in
  let tokens = [ "a"; "a"; "a" ] in
  let log_probability, tree = Parse.log_viterbi prep tokens in
  check "log Viterbi chooses one derivation of an ambiguous string"
    (approx (exp log_probability) (1.0 /. 32.0)
     && Option.map Parse.tree_yield tree = Some tokens)

let () =
  let grammar =
    g "S"
      [ prod "S" [ nt "A"; nt "A" ]; prod "S" [ nt "A" ];
        prod "A" [ tm "a" ]; prod "A" [ tm "a"; nt "A" ] ]
  in
  let corpus = [ sample [ "a"; "a" ] 2.0 ] in
  let prep = Parse.prepare grammar in
  let initial_probs = Array.copy prep.Parse.probs in
  let counts, ll = Parse.fit_em prep corpus ~iters:0 ~tol:1e-9 in
  check "zero EM updates retain the initial parameters"
    (prep.Parse.probs = initial_probs);
  check "zero EM updates report the initial likelihood and counts"
    (approx ll (2.0 *. log 0.25)
     && Array.for_all2 approx counts [| 1.0; 1.0; 3.0; 1.0 |]);
  let counts, ll = Parse.fit_em prep corpus ~iters:1 ~tol:1e-9 in
  check "one EM update reports the updated likelihood"
    (approx ll (2.0 *. log 0.375));
  let expected = [| 1.5; 0.5; 3.5; 0.5 |] in
  check "one EM update reports counts under the updated parameters"
    (Array.for_all2 approx counts expected);
  let prep = Parse.prepare grammar in
  let counts, ll = Parse.fit_em prep corpus ~iters:10 ~tol:1e6 in
  let fresh_counts, fresh_ll = Parse.expected_counts_log prep [ "a"; "a" ] in
  check "EM convergence returns statistics for the retained parameters"
    (approx ll (2.0 *. fresh_ll)
     && Array.for_all2 (fun count fresh -> approx count (2.0 *. fresh)) counts fresh_counts);
  let prep = Parse.prepare (g "S" [ prod "S" [ tm "a" ] ]) in
  let _, ll = Parse.fit_em prep [ sample [ "a" ] 1.0; sample [ "b" ] 1.0 ]
      ~iters:1 ~tol:1e-9 in
  check "EM likelihood includes unparseable corpus mass" (ll = neg_infinity)

let () =
  let grammars =
    [ g "A" [ prod "A" [ nt "B" ]; prod "B" [ nt "A" ]; prod "B" [ tm "b" ] ];
      g "A"
        [ prod "A" [ nt "B" ]; prod "B" [ nt "C" ]; prod "C" [ nt "A" ];
          prod "A" [ tm "a" ]; prod "B" [ nt "D" ]; prod "C" [ tm "c" ];
          prod "D" [ tm "d" ] ];
      g "A"
        [ prod "A" [ nt "B" ]; prod "B" [ nt "A" ];
          prod "A" [ tm "a"; nt "B" ]; prod "B" [ tm "b" ] ];
      g "A" [ prod "A" [ nt "B" ]; prod "B" [ nt "A" ] ] ]
  in
  List.iteri
    (fun i grammar ->
      let normalized = Grammar.normalize grammar in
      check (Printf.sprintf "unary cycle %d preserves terminal derivations" i)
        (Grammar.language_up_to grammar 5 = Grammar.language_up_to normalized 5);
      ignore (Parse.prepare normalized);
      let reordered = { grammar with Grammar.productions = List.rev grammar.Grammar.productions } in
      check (Printf.sprintf "unary cycle %d preserves exits after reordering" i)
        (Grammar.language_up_to normalized 5
         = Grammar.language_up_to (Grammar.normalize reordered) 5))
    grammars;
  let normalized = Grammar.normalize (List.hd grammars) in
  check "a unary cycle retains an exit owned only by the other member"
    (has_prod normalized "A" [ tm "b" ]
     && approx (Parse.inside (Parse.prepare normalized) [ "b" ]) 1.0)

let () =
  let initial =
    g "S" [ prod "S" [ nt "A"; nt "B" ]; prod "A" [ tm "a" ]; prod "B" [ tm "a" ] ]
  in
  let corpus = [ sample [ "a"; "a" ] 1.0 ] in
  let config = Scoring.default_config in
  let expected = Grammar.normalize (Transform.apply initial (Transform.Merge ("A", "B"))) in
  List.iter
    (fun frontier_cap ->
      let result = Search.run_best_first ~config ~frontier_cap ~max_expansions:1
          ~patience:1 initial corpus in
      check "best-first retains an improvement found in the last expansion"
        (result.Search.best_score > result.Search.initial_score
         && Grammar.equal_structure result.Search.best expected);
      check "best-first retains the history of the unexpanded winner"
        (match result.Search.steps with
         | [ step ] -> Grammar.equal_structure step.Search.result result.Search.best
             && approx step.Search.score result.Search.best_score
         | _ -> false);
      check "best-first records the retained proposal as accepted"
        (List.exists (fun p -> p.Search.accepted && approx p.Search.score result.Search.best_score)
           result.Search.proposals))
    [ 0; 1; 8 ];
  let result = Search.run_best_first ~config ~frontier_cap:8 ~max_expansions:0
      ~patience:1 initial corpus in
  check "zero best-first expansions retain the initial grammar"
    (result.Search.iterations = 0 && result.Search.steps = []
     && result.Search.proposals = [] && Grammar.equal_structure result.Search.best initial)

let () =
  if !failures = 0 then Printf.printf "\nAll tests passed.\n"
  else begin
    Printf.printf "\n%d test(s) failed.\n" !failures;
    exit 1
  end
