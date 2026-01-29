open Printf
open Ocaml

let () =
  if Array.length Sys.argv < 3 then begin
    prerr_endline "Usage: main <vampire_proof_file> <mode>";
    prerr_endline "  mode = single    -> axioms + lemma_i";
    prerr_endline "  mode = history   -> axioms + lemmas 1..(i-1) + lemma_i";
    prerr_endline "  mode = abstract  -> axioms + lemma_i with nested op(...) replaced by variables";
    exit 1
  end;

  let filename = Sys.argv.(1) in
  let mode = Sys.argv.(2) in

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
      printf "[INFO] Generated %d TPTP single-mode .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | "history" ->
      Lemma_extractor.generate_all_files_history axioms lemmas;
      printf "[INFO] Generated %d TPTP history-mode .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | "abstract" ->
      Lemma_extractor.generate_all_files_abstract axioms lemmas;
      printf "[INFO] Generated %d TPTP abstract-mode .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | _ ->
      eprintf "[ERROR] Unknown mode: %s (expected 'single', 'history', or 'abstract')\n%!"
        mode;
      exit 1
