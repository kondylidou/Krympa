#!/usr/bin/env python
import atexit
import sys
import logging
import time

import config
import run.problem
from run import utils
from run.preprocess import preprocess_problem
from run.schedule import run_schedule
from run.problem import Problem, output_proof
from run.run_parser import get_single_problem_args
from run.schedule import get_schedule

logging.basicConfig(
    stream=sys.stdout, level=logging.WARNING, format="%(levelname)s - %(message)s"
)
log = logging.getLogger()


def main() -> None:
    args = get_single_problem_args(sys.argv[1:])
    # Set the loglevel
    log.setLevel(args.loglevel)
    log.debug(str(args))

    # Register clean up if receiving kill signal
    utils.register_functions_and_signals()

    # Check that problem exists and exit if it does not
    problem = Problem(args.problem_path, args.ltb_problem, args.problem_version)
    log.debug(str(problem))

    prep_time = 0.0
    if args.preprocessing_heuristic is not None:
        # Compute the time used on preprocessing
        prep_start = time.time()

        problem = preprocess_problem(
            problem,
            args.preprocessing_heuristic,
            args.preprocessing_timelimit or args.wc_timeout,
        )
        prep_time = time.time() - prep_start
        log.info(
            f"Preprocessing finished in {prep_time:.2f}s. new problem: {str(problem)}"
        )

    # Get the schedule
    schedule = get_schedule(
        args.schedule,
        args.heuristic_context,
        args.no_cores,
        **{"proof_out": not args.suppress_proof_out, "pformat": problem.pformat},
    )
    log.debug(str(schedule))

    # Get the current time as start time and add grace
    time_limit = args.wc_timeout + config.PROBLEM_ATTEMPT_GRACE - prep_time
    log.info(
        f"Added {config.PROBLEM_ATTEMPT_GRACE}s grace, new timelimit is: {time_limit}"
    )

    print(f"% SZS status Started for {problem.name}")
    run_schedule(problem, schedule, time_limit)

    # Handle the result
    handle_problem_post_attempt(problem)
    log.info("Finished problem attempt")

    # Clean up after the attempts
    utils.graceful_exit()


def handle_problem_post_attempt(problem: Problem) -> None:
    if problem.solved:
        print(f"% SZS status {problem.szs_status} for {problem.name}")
        if problem.proof is None:
            raise ValueError("Problem is solved but proof file is not set!")
        # Print the proof
        output_proof(problem.proof)
        # Proof is outputted: unregister - this was set in the problem
        atexit.unregister(run.problem.output_proof)

    else:
        print(f"% SZS status Unknown for {problem.name}")


if __name__ == "__main__":
    main()
