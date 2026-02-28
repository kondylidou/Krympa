import time
import logging

import config
from run.problem import Problem
from run.heuristic import get_heuristic
from run.process import ProverProcess, process_has_finished

log = logging.getLogger()


def preprocess_problem(problem: Problem, heur_file: str, timelimit: float) -> Problem:
    heuristic = get_heuristic(
        heur_file, heuristic_context="preprocess", pformat=problem.pformat
    )
    log.info(f"Preprocessing with heuristic: {heuristic} for time {timelimit}")

    # Make and start the process
    prep_proc = ProverProcess(heuristic, problem, timelimit)
    prep_proc.start()
    time.sleep(0.2)

    # Wait for the process to finish
    while not process_has_finished(prep_proc):
        time.sleep(config.PROVER_PROC_SLEEP_TIME)
    log.debug("Preprocessing finished")

    # Check for errors - use the original problem if issues occurred
    if prep_proc.check_errors():
        log.error("Error occurred while preprocessing. Returning the original problem")
        return problem

    # Handle post-processing
    handle_post_preprocess(problem, prep_proc)
    return problem


def handle_post_preprocess(problem: Problem, prep_proc: ProverProcess):
    # Check if successful
    if prep_proc.success():
        assert prep_proc.szs_status is not None
        # Set as solved - will get picked up later
        log.info("Problem solved during preprocessing")
        problem.set_solved(prep_proc.out_file, prep_proc.szs_status)
    else:
        # Update the path with the preprocessed problem
        problem.path = prep_proc.out_file
        log.debug(f"Problem path updated to preprocessed file: {problem.path}")


'''
def clausify_smt2(problem: Problem, time_limit: float) -> Problem:
    """
    Clausify smt2 problems into a format supported by iProver.
    Not used in the new version of iProver.
    """

    # Get the clausifier
    clausifier = Clausifier(
        options=f"--input_syntax smtlib2 --mode tclausify -t {time_limit}",
        clausifier_mode=ClausifierMode.TFF,
    )

    claus_proc = ClausifierProcess(clausifier, problem, time_limit)
    claus_proc.start()
    time.sleep(0.2)

    # Wait for the process to finish
    while not process_has_finished(claus_proc):
        time.sleep(config.PROVER_PROC_SLEEP_TIME)
    log.debug("Clausification finished")

    # Report any errors
    claus_proc.check_errors()

    problem.path = claus_proc.out_file
    log.debug(f"Problem path updated to clausified file: {problem.path}")
    return problem
'''
