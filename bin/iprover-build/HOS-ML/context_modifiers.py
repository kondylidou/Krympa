"""
File containing the context modifiers for the heuristics and the clausifier
"""
from typing import Dict, List

# Heuristic context modifier for various competition requirements.
HEURISTIC_CONTEXT_MODIFIERS: Dict[str, List[str]] = {
    "none": [],  # Empty is no modification
    "preprocess": ["--preprocessed_out true", "--tptp_safe_out true"],
    "debug": ["--stats_out none", "--out_options none", "--dbg_just_parse true"],
    "default": ["--stats_out none", "--tptp_safe_out true", "--out_options none"],
    #    "default": ["--stats_out none", "--tptp_safe_out true", "--out_options all"],
    "smt": ["--sup_smt_interval 1000", "--smt_ac_axioms fast"],
    "ltb": ["--suppress_sat_res true"],
    "isabelle": ["--sup_smt_interval 500", "--smt_ac_axioms fast"],
    "smtcomp": [
        "--sub_typing false",
        "--stats_out none",
        "--out_options none",
        "--smt_ac_axioms fast",
        "--suppress_sat_res true"
    ],
   "smtcomp_uf": [
        "--sub_typing false",
        "--stats_out none",
        "--out_options none",
        "--smt_ac_axioms fast",
    ],
    "fnt": [
        "--suppress_unsat_res true",
        "--stats_out none",
        "--preprocessing_flag false",
        "--sat_out_model pos",
        # "--out_options none",
        "--out_options all",
    ],
#    "casc_unsat": ["--suppress_sat_res true", "--tptp_safe_out true", "--stats_out none", "--out_options all"],
    "casc_unsat": ["--suppress_sat_res true", "--tptp_safe_out true", "--stats_out none", "--out_options none"],
}

CLAUSIFIER_CONTEXT_MODIFIERS: Dict[str, List[str]] = {"fnt": ["-updr off"]}
