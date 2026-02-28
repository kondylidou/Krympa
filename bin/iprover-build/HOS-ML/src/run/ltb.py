import shutil
import os
import re
import time
from typing import List, Set, Optional

import logging

import config
from run import utils
from run.problem import ProblemFormat

log = logging.getLogger()

# VERSIONS = ["+1", "_1"]
VERSIONS = ["_1"]
DEFAULT_VERSION = "_1"
PROBLEM_POSTFIX_TO_PROBLEM_FORMAT = {
    "+1": ProblemFormat.FOF,
    "_1": ProblemFormat.TF0,
}


class LTBProblem:
    def __init__(self, general_path: str, name: str):
        self.__general_path = general_path  # The path with asterix
        self.__name = name

        self.solved: bool = False
        self.proof: str | None = None
        self.szs_status: str = "Unknown"

        #  Want to make sure the user actively sets the path before use
        self.path: str
        self.set_path(DEFAULT_VERSION)  # Initialise path

    @property
    def is_ltb(self):
        # LTB problems are always LTB
        return True

    @property
    def general_path(self) -> str:
        return self.__general_path

    @property
    def name(self) -> str:
        return self.__name

    def set_solved(self, proof_file: str, szs_status: str) -> None:
        self.solved = True
        self.proof = proof_file
        self.szs_status = szs_status

    def set_path(self, version: str) -> str:
        if version not in VERSIONS:
            log.error(
                f"Version {version} not recognised. Returning default version {DEFAULT_VERSION}"
            )
            version = DEFAULT_VERSION

        self.path = self.general_path.replace("*", version, 1)
        return self.path

    def __str__(self):
        return f"LTBProblem -> Name: {self.name} Path: {self.general_path} Versions: {', '.join(VERSIONS)}"


class LTBBatch:
    def __init__(
        self,
        batch_dir: str,
        time_limit: int,
        output_dir: str,
        batch_problems: Optional[Set[LTBProblem]] = None,
    ):
        self.__batch_dir = batch_dir
        self.__time_limit = time_limit + config.LTB_ATTEMPT_GRACE

        self.__output_dir = output_dir

        if batch_problems is None:
            self.unsolved: Set[LTBProblem] = set()
        else:
            self.unsolved = batch_problems

        self.solved: Set[LTBProblem] = set()
        self.no_problems = len(self.unsolved)

        self.__start_time = time.time()

    @property
    def output_dir(self) -> str:
        return self.__output_dir

    @property
    def start_time(self) -> float:
        return self.__start_time

    @property
    def time_limit(self) -> int:
        return self.__time_limit

    def batch_dir(self) -> str:
        return self.__batch_dir

    def get_no_unsolved_problems(self) -> int:
        return len(self.unsolved)

    def get_unsolved_problems(self) -> Set[LTBProblem]:
        return self.unsolved

    def get_no_solved_problems(self) -> int:
        return len(self.solved)

    def get_solved_problems(self) -> Set[LTBProblem]:
        return self.solved

    def set_problem_solved(self, prob: LTBProblem):
        self.unsolved.remove(prob)
        self.solved.add(prob)

    def __len__(self):
        return self.get_no_solved_problems() + self.get_no_unsolved_problems()

    def __str__(self):
        return (
            f"LTBBatch -> batch_dir: {self.batch_dir()} timelimit: {self.time_limit} "
            f"no_solved: {self.get_no_solved_problems()} no_unsolved: {self.get_no_unsolved_problems()}"
        )


def get_batch_overall_wc(batch_spec: List[str]) -> int:
    for line in batch_spec:
        if re.match("limit.time.overall.wc", line):
            time_limit = int(line.split()[1])
            return time_limit
    return -1  # Could not find the time limit


def get_batch_problems(batch_dir: str, batch_spec: List[str]) -> List[LTBProblem]:
    # List for holding the problems in the batch
    problems = []

    # Whether problem listings have started
    read_problem = False

    # Get A tuple of the problems
    for line in batch_spec:
        # Set starting to read batch
        if line == "% SZS start BatchProblems":
            read_problem = True
        # Set stopping to read batch
        elif line == "% SZS end BatchProblems":
            break  # There is only one batch in a file
        elif read_problem:
            # Get subdirectory path and problem name
            prob_path, prob_name = line.split()
            problems += [LTBProblem(os.path.join(batch_dir, prob_path), prob_name)]
        else:
            pass

    return list(problems)


def validate_problem_version(version_path: str) -> bool:
    if not os.path.exists(version_path):
        log.error(f"Cannot find problem version: {version_path}")
        return False

    return True


def validate_problem_version_paths(ltb_problems: Set[LTBProblem]) -> bool:
    """
    Check if all problem versions exists, or can be found
    """
    valid = True  # Initially we assume all exists
    for prob in ltb_problems:
        for version in VERSIONS:
            problem_version = prob.set_path(version)
            if not validate_problem_version(problem_version):
                valid = False

    return valid


def process_batch_file(batch_file_path: str, output_dir: str) -> LTBBatch:
    # This function implements a few shortcuts according to the J10 instruction
    # - Problems are unordered
    # - output.required Proof
    # - limit.time.problem.wc 0  # No problem timelimit
    #  - Only one batch of problems

    # Get contents of the batch file #
    with open(batch_file_path, "r") as bf:
        batch_spec = bf.read().splitlines()

    batch_dir = os.path.dirname(os.path.realpath(batch_file_path))
    # Get overall batch time limit
    time_limit = get_batch_overall_wc(batch_spec)

    # Read the problems and validate
    problems = set(get_batch_problems(batch_dir, batch_spec))
    validate_problem_version_paths(problems)

    utils.create_dir_if_not_exists(output_dir)

    ltb_batch = LTBBatch(batch_dir, time_limit, output_dir, batch_problems=problems)

    return ltb_batch


def output_proof_to_file(output_dir: str, name: str, proof_file: str):
    # Still want to continue proving!
    proof_file_dest = os.path.join(output_dir, name)
    log.debug(f"Outputting proof of {name} to {proof_file_dest}")
    try:
        shutil.copyfile(proof_file, proof_file_dest)
    except Exception as err:
        log.error(
            f"Could not copy proof file {proof_file} to {proof_file_dest} due to: {str(err)}"
        )


def handle_solved_problem(batch: LTBBatch, problem: LTBProblem) -> LTBBatch:
    # Print to file
    assert problem.proof is not None
    output_proof_to_file(batch.output_dir, problem.name, problem.proof)

    # Set problems as solved in the batch
    batch.set_problem_solved(problem)

    # Return the new batch
    return batch
