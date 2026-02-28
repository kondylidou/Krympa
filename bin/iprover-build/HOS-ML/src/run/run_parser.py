import argparse
import logging
from typing import List

import config_schedules
import run.ltb
from context_modifiers import HEURISTIC_CONTEXT_MODIFIERS
from run.problem import ProblemFormat


def _get_base_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--no_cores",
        type=int,
        help="No cores available for proving (and embedding)",
        default=8,
    )

    parser.add_argument(
        "--heuristic_context",
        "--context",
        help="The context used to alter the heuristics",
        default="default",
        type=str,
        choices=list(HEURISTIC_CONTEXT_MODIFIERS.keys()),
    )

    # Set loglevel
    parser.add_argument(
        "-d",
        "--debug",
        help="Print debug logs",
        action="store_const",
        dest="loglevel",
        const=logging.DEBUG,
        default=logging.WARNING,
    )
    parser.add_argument(
        "-v",
        "--verbose",
        help="Print info logs",
        action="store_const",
        dest="loglevel",
        const=logging.INFO,
    )

    return parser


def get_single_problem_args(args: List[str]) -> argparse.Namespace:
    parser = _get_base_parser()

    parser.add_argument("problem_path", help="Path to problem")
    parser.add_argument("wc_timeout", type=float, help="WC time limit for problem")

    parser.add_argument(
        "--ltb_problem",
        action="store_true",
        help="Set flag to treat the problem as an LTB problem",
    )

    parser.add_argument(
        "--schedule",
        help="The schedule to run",
        default="default",
        choices=list(config_schedules.SCHEDULES.keys()),
    )

    parser.add_argument(
        "--problem_version",
        choices=list(ProblemFormat),
        type=ProblemFormat,
        default=None,
        help="Give the type of the problem (inferred if not set)",
    )
    parser.add_argument(
        "--suppress_proof_out",
        help="Turn off proof reconstruction",
        action="store_true",
    )

    parser.add_argument(
        "--preprocessing_heuristic",
        default=None,
        help="The heuristic to run as a pre-processor",
    )
    parser.add_argument(
        "--preprocessing_timelimit",
        type=float,
        default=None,
        help="Timeout for preprocessing (None if using WC)",
    )

    return parser.parse_args(args=args)


def get_ltb_args(args: List[str]) -> argparse.Namespace:
    parser = _get_base_parser()

    parser.add_argument(
        "batch_file", help="The path to the file containing the batch information"
    )
    parser.add_argument("proof_out_dir", help="Output directory of the proofs")

    parser.add_argument(
        "--schedule",
        nargs="*",
        choices=list(config_schedules.SCHEDULES.keys()),
        help="List of schedules to run",
    )

    parser.add_argument(
        "--version",
        nargs="*",
        choices=run.ltb.VERSIONS,
        type=str,
        help="List of the problem versions to attempt",
    )

    parser.add_argument(
        "--max_timelimit",
        nargs="*",
        type=float,
        help="List of max timelimit of each problem (-1) is unbounded",
    )

    return parser.parse_args(args=args)
