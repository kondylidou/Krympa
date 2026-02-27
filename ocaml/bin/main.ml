open Printf
open Ocaml

let () =
  if Array.length Sys.argv < 3 then begin
    prerr_endline "Usage: main <vampire_proof_file> <mode>";
    prerr_endline "  mode = big-step   (alias: single)    -> axioms + lemma_i";
    prerr_endline "  mode = small-step (alias: history)   -> axioms + lemmas 1..(i-1) + lemma_i";
    prerr_endline "  mode = abstracted (alias: abstract)  -> axioms + lemma_i with nested op(...) replaced by variables";
    exit 1
  end;

  let filename = Sys.argv.(1) in
  let mode =
    match Sys.argv.(2) with
    | "single" | "big-step" -> "single"
    | "history" | "small-step" -> "history"
    | "abstract" | "abstracted" -> "abstract"
    | other -> other
  in

  let (axioms, lemmas) =
    Tptp_parser.read_axioms_and_lemmas_from_file filename
  in

  printf "[INFO] Extracted %d axioms.\n%!" (List.length axioms);
  List.iter (fun ax -> printf "%s\n%!" ax) axioms;

  printf "[INFO] Extracted %d lemmas from the proof file.\n%!"
    (List.length lemmas);

  match mode with
  | "single" ->
      Lemma_extractor.generate_all_files_single axioms lemmas;
      printf "[INFO] Generated %d TPTP big-step (single) .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | "history" ->
      Lemma_extractor.generate_all_files_history axioms lemmas;
      printf "[INFO] Generated %d TPTP small-step (history) .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | "abstract" ->
      Lemma_extractor.generate_all_files_abstract axioms lemmas;
      printf "[INFO] Generated %d TPTP abstracted (abstract) .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | _ ->
      eprintf "[ERROR] Unknown mode: %s (expected 'big-step'/'single', 'small-step'/'history', or 'abstracted'/'abstract')\n%!"
        mode;
      exit 1
