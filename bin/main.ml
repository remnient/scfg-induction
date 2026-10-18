open Scfg

let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let mkdir_p dir = ignore (Sys.command ("mkdir -p " ^ Filename.quote dir))

let parse_args rest =
  let rec go opts = function
    | [] -> opts
    | x :: v :: tl
      when String.length x > 2
           && String.sub x 0 2 = "--"
           && String.length v > 0
           && v.[0] <> '-' ->
        go ((String.sub x 2 (String.length x - 2), v) :: opts) tl
    | x :: tl when String.length x > 2 && String.sub x 0 2 = "--" ->
        go ((String.sub x 2 (String.length x - 2), "true") :: opts) tl
    | _ :: tl -> go opts tl
  in
  go [] rest

let opt opts k d = match List.assoc_opt k opts with Some v -> v | None -> d

let float_opt opts k d =
  match List.assoc_opt k opts with
  | Some v -> (match float_of_string_opt v with Some f -> f | None -> d)
  | None -> d

let int_opt opts k d =
  match List.assoc_opt k opts with
  | Some v -> (match int_of_string_opt v with Some i -> i | None -> d)
  | None -> d

let flag opts k = List.mem_assoc k opts

let config_of_opts opts =
  {
    Scoring.default_config with
    alpha = float_opt opts "alpha" Scoring.default_config.alpha;
    prior_weight = float_opt opts "prior" Scoring.default_config.prior_weight;
    em_iters = int_opt opts "em-iters" Scoring.default_config.em_iters;
    max_chunk = int_opt opts "max-chunk" Scoring.default_config.max_chunk;
    mode =
      (match opt opts "mode" "approximate" with
      | "ml" -> Scoring.Maximum_likelihood
      | "variational" -> Scoring.Variational
      | "approximate" | "marginal" -> Scoring.Approximate_evidence
      | mode -> invalid_arg ("unknown scoring mode: " ^ mode));
    chunk_occurrence =
      (if opt opts "chunk-occurrence" "all" = "first" then
         Scoring.First_occurrence
       else Scoring.All_occurrences);
  }

let usage () =
  print_endline
    "SCFG induction by Bayesian model merging (Stolcke & Omohundro 1994)\n\n\
     Usage: scfg-induction <command> [options]\n\n\
     Commands:\n\
    \  induce       --corpus FILE [--out DIR] [--beam N] [--max-steps N]\n\
    \               [--patience N] [--alpha A] [--prior W] [--max-chunk N]\n\
    \               [--em-iters N] [--mode approximate|ml|variational]\n\
    \               [--chunk-occurrence all|first] [--render]\n\
    \               [--search beam|bestfirst] [--frontier N] [--max-expansions N]\n\
    \  score        --grammar FILE --corpus FILE [--alpha A] [--prior W]\n\
    \  parse        --grammar FILE --input \"a b c\" [--dot FILE]\n\
    \  dot          --grammar FILE --out FILE [--svg FILE] [--title T]\n\
    \  experiments  [--out DIR] [--seed N] [--beam N] [--max-steps N]\n\
    \               [--patience N] [--max-len N] [--only NAME] [--quick]\n\n\
     Corpus format: one sequence per line, whitespace-separated tokens.\n\
     An optional \"count:\" prefix sets the sample count, e.g. \"3: a b c\".\n\
     Grammar format: \"S -> A B [0.5]\"; uppercase-initial symbols are\n\
     nonterminals, other symbols are terminals."

let cmd_induce opts =
  let corpus_path = opt opts "corpus" "" in
  if corpus_path = "" then (prerr_endline "induce: --corpus is required"; exit 2);
  let out_dir = opt opts "out" "out" in
  mkdir_p out_dir;
  let steps_dir = Filename.concat out_dir "steps" in
  mkdir_p steps_dir;
  let render = flag opts "render" in
  let config = config_of_opts opts in
  let beam = int_opt opts "beam" 4 in
  let max_steps = int_opt opts "max-steps" 25 in
  let patience = int_opt opts "patience" 5 in
  let corpus = Corpus.of_file corpus_path in
  let initial =
    Grammar.initial_grammar
      (List.map (fun s -> (s.Corpus.tokens, s.Corpus.count)) corpus)
  in
  Printf.printf "corpus: %d distinct samples, total count %g\n"
    (List.length corpus) (Corpus.total_count corpus);
  Printf.printf "initial grammar: %d nonterminals, %d productions\n"
    (List.length (Grammar.nonterminals initial))
    (List.length initial.Grammar.productions);
  let result =
    if opt opts "search" "beam" = "bestfirst" then
      Search.run_best_first ~config
        ~frontier_cap:(int_opt opts "frontier" 200)
        ~max_expansions:(int_opt opts "max-expansions" 300)
        ~patience initial corpus
    else Search.run ~config ~beam_width:beam ~max_steps ~patience initial corpus
  in
  List.iteri
    (fun i (s : Search.step) ->
      let ch = Transform.change_of s.Search.parent s.Search.transform s.Search.result in
      let base =
        Filename.concat steps_dir (Printf.sprintf "step%03d" (i + 1))
      in
      let dot_before =
        Dot.dot_grammar ~highlight_nts:ch.Transform.before_nts
          ~highlight_prods:ch.Transform.before_prods
          ~title:
            (Printf.sprintf "step %d before: %s" (i + 1)
               (Transform.describe s.Search.transform))
          s.Search.parent
      in
      let dot_after =
        Dot.dot_grammar ~highlight_nts:ch.Transform.after_nts
          ~highlight_prods:ch.Transform.after_prods
          ~title:
            (Printf.sprintf "step %d after: %s" (i + 1)
               (Transform.describe s.Search.transform))
          s.Search.result
      in
      let svg_before = if render then Some (base ^ "-before.svg") else None in
      let svg_after = if render then Some (base ^ "-after.svg") else None in
      ignore
        (Dot.render ?out_svg:svg_before ~out_dot:(base ^ "-before.dot") dot_before);
      ignore
        (Dot.render ?out_svg:svg_after ~out_dot:(base ^ "-after.dot") dot_after);
      Printf.printf "  accepted step %d: %s  score %.4f -> %.4f\n" (i + 1)
        (Transform.describe s.Search.transform)
        s.Search.parent_score s.Search.score)
    result.Search.steps;

  let details = Scoring.details ~config result.Search.best corpus in
  Dot.write_file (Filename.concat out_dir "grammar-final.dot")
    (Dot.dot_grammar ~title:"induced grammar" result.Search.best);
  if render then
    ignore
      (Dot.render ~out_svg:(Filename.concat out_dir "grammar-final.svg")
         ~out_dot:(Filename.concat out_dir "grammar-final.dot")
         (Dot.dot_grammar ~title:"induced grammar" result.Search.best));
  Dot.write_file (Filename.concat out_dir "grammar-initial.dot")
    (Dot.dot_grammar ~title:"initial grammar" initial);
  Dot.write_file (Filename.concat out_dir "grammar-final.txt")
    (Grammar.to_string result.Search.best);
  Dot.write_file (Filename.concat out_dir "search-steps.tsv")
    (Search.steps_to_tsv result);
  Dot.write_file (Filename.concat out_dir "search-proposals.tsv")
    (Search.proposals_to_tsv result);
  Printf.printf "\nsearch: %d iterations, %d accepted steps\n"
    result.Search.iterations (List.length result.Search.steps);
  Printf.printf "posterior: %.4f -> %.4f\n" result.Search.initial_score
    result.Search.best_score;
  Printf.printf "structure prior %.4f, objective %.4f, dl %.1f bits\n"
    details.Scoring.prior details.Scoring.objective details.Scoring.dl_bits;
  Printf.printf "final grammar: %d nonterminals, %d productions\n"
    details.Scoring.num_nonterminals details.Scoring.num_productions;
  print_endline "\nfinal grammar:";
  print_endline (Grammar.to_string result.Search.best);
  Printf.printf "\nwrote %s\n" out_dir

let cmd_score opts =
  let grammar_path = opt opts "grammar" "" in
  let corpus_path = opt opts "corpus" "" in
  if grammar_path = "" || corpus_path = "" then
    (prerr_endline "score: --grammar and --corpus are required"; exit 2);
  let config = config_of_opts opts in
  let g = Grammar.of_string (read_file grammar_path) in
  let corpus = Corpus.of_file corpus_path in
  let d = Scoring.details ~config g corpus in
  Printf.printf "posterior            %.6f\n" d.Scoring.posterior;
  Printf.printf "structural prior     %.6f\n" d.Scoring.prior;
  Printf.printf "objective             %.6f\n" d.Scoring.objective;
  Printf.printf "approximate evidence  %.6f\n"
    d.Scoring.approximate_evidence;
  Printf.printf "ML corpus loglik     %.6f\n" d.Scoring.ml_loglik;
  Printf.printf "description length   %.2f bits\n" d.Scoring.dl_bits;
  Printf.printf "nonterminals         %d\n" d.Scoring.num_nonterminals;
  Printf.printf "productions          %d\n" d.Scoring.num_productions

let cmd_parse opts =
  let grammar_path = opt opts "grammar" "" in
  let input = opt opts "input" "" in
  if grammar_path = "" || input = "" then
    (prerr_endline "parse: --grammar and --input are required"; exit 2);
  let g = Grammar.normalize (Grammar.of_string (read_file grammar_path)) in
  let tokens =
    String.split_on_char ' ' (String.trim input)
    |> List.filter (fun s -> String.length s > 0)
  in
  let prep = Parse.prepare g in
  let p = Parse.inside prep tokens in
  let log_vp, tree = Parse.log_viterbi prep tokens in
  Printf.printf "tokens:      %s\n" (String.concat " " tokens);
  Printf.printf "P(string):   %.10g\n" p;
  Printf.printf "best parse:  %.10g\n" (exp log_vp);
  Printf.printf "log best parse: %.10g\n" log_vp;
  (match tree with
  | Some t -> Printf.printf "%s\n" (Parse.tree_to_string t)
  | None -> print_endline "(no parse)");
  (match List.assoc_opt "dot" opts with
  | Some path -> (
      match tree with
      | Some t ->
          Dot.write_file path (Dot.dot_tree ~title:"Viterbi parse" t);
          Printf.printf "wrote %s\n" path
      | None -> ())
  | None -> ())

let cmd_dot opts =
  let grammar_path = opt opts "grammar" "" in
  let out = opt opts "out" "" in
  if grammar_path = "" || out = "" then
    (prerr_endline "dot: --grammar and --out are required"; exit 2);
  let g = Grammar.normalize (Grammar.of_string (read_file grammar_path)) in
  let title = opt opts "title" "grammar" in
  let svg = List.assoc_opt "svg" opts in
  let res =
    Dot.render ?out_svg:svg ~out_dot:out (Dot.dot_grammar ~title g)
  in
  Printf.printf "wrote %s%s\n" out
    (match res with Some s -> " and " ^ s | None -> "")

let cmd_experiments opts =
  let out_dir = opt opts "out" "experiments" in
  mkdir_p out_dir;
  mkdir_p (Filename.concat out_dir "steps");
  let render = flag opts "render" in
  let quick = flag opts "quick" in
  let config = config_of_opts opts in
  let seed = int_opt opts "seed" 1 in
  let beam = int_opt opts "beam" 3 in
  let max_steps = int_opt opts "max-steps" (if quick then 12 else 25) in
  let patience = int_opt opts "patience" (if quick then 3 else 5) in
  let max_len = int_opt opts "max-len" (if quick then 6 else 7) in
  let only = List.assoc_opt "only" opts in
  let results =
    Experiment.run_all
      ~export_dir:(if render then Some (Filename.concat out_dir "steps") else None)
      ~config ~beam_width:beam ~max_steps ~patience ~seed ~max_len ~only ()
  in
  if render then
    List.iter
      (fun (r : Experiment.result) ->
        let base = Filename.concat out_dir r.Experiment.target.Experiment.name in
        ignore
          (Dot.render ~out_svg:(base ^ "-final.svg") ~out_dot:(base ^ "-final.dot")
             (Dot.dot_grammar
                ~title:(Printf.sprintf "%s (induced)" r.Experiment.target.Experiment.name)
                r.Experiment.final_grammar)))
      results;
  Dot.write_file (Filename.concat out_dir "results.tsv")
    (Experiment.to_tsv results);
  Dot.write_file (Filename.concat out_dir "report.md")
    (Experiment.report_markdown results);
  List.iter
    (fun (r : Experiment.result) ->
      let base = Filename.concat out_dir r.Experiment.target.Experiment.name in
      Dot.write_file (base ^ "-final.dot")
        (Dot.dot_grammar
           ~title:(Printf.sprintf "%s (induced)" r.Experiment.target.Experiment.name)
           r.Experiment.final_grammar);
      Dot.write_file (base ^ "-final.txt")
        (Grammar.to_string r.Experiment.final_grammar))
    results;
  print_endline (Experiment.to_tsv results);
  Printf.printf "\nwrote %s\n" out_dir

let () =
  match Array.to_list Sys.argv with
  | _ :: cmd :: rest -> (
      let opts = parse_args rest in
      match cmd with
      | "induce" -> cmd_induce opts
      | "score" -> cmd_score opts
      | "parse" -> cmd_parse opts
      | "dot" -> cmd_dot opts
      | "experiments" -> cmd_experiments opts
      | "help" | "-h" | "--help" -> usage ()
      | other ->
          Printf.eprintf "unknown command: %s\n\n" other;
          usage ();
          exit 2)
  | _ -> usage ()
