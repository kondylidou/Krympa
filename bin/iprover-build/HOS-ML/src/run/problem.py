import atexit
import re
import os.path
from enum import Enum
from pathlib import Path
from typing import Optional, Protocol
import logging

log = logging.getLogger()


class ProblemFormat(Enum):
    CNF = "cnf"
    FOF = "fof"
    TF0 = "tf0"
    # TX0 = "tx0"
    SMT2 = "smt2"

    def __str__(self):
        return self.value


class _Problem(Protocol):
    path: str
    solved: bool
    szs_status: str

    @property
    def is_ltb(self) -> bool:
        ...

    def set_solved(self, proof_file: str, szs_status: str) -> None:
        ...


class Problem:
    def __init__(
        self, path: str, is_ltb: bool, pformat: Optional[ProblemFormat] = None
    ):
        self.path = path
        self._check_file_path_existence()

        self.name = Path(self.path).name
        self.proof: str | None = None
        self._is_ltb = is_ltb
        self.solved: bool = False
        self.szs_status: str = "Unknown"

        if pformat is None:
            self.pformat = infer_problem_version(self.path)
        else:
            self.pformat = pformat
        log.info(f"Problem pformat is set to: {self.pformat}")

        if self.pformat is ProblemFormat.SMT2:
            if check_if_uf_logic(self.path):
                self._is_ltb = False
                log.info("SMT2 problem uses UF logic. Normal SZS Interpretation")
            else:
                self._is_ltb = True
                log.info("SMT2 problem does not use UF logic. LTB SZS Interpretation")

    @property
    def is_ltb(self) -> bool:
        return self._is_ltb

    @property
    def is_tff(self) -> bool:
        return problem_version_is_tff(self.pformat)

    def set_solved(self, proof_file: str, szs_status: str) -> None:
        self.solved = True
        self.proof = proof_file
        self.szs_status = szs_status

        # Register proof output in case something goes wrong
        atexit.register(output_proof, self.proof)

    def _check_file_path_existence(self) -> None:
        if not os.path.exists(self.path):
            raise ValueError(f"Could not find problem file: {self.path}")

    def __str__(self):
        return f"Problem:{self.name}:{self.pformat}"


def infer_problem_version(problem_path: str) -> ProblemFormat:
    """Function that tries to infer the problem type based on its contents."""

    # Get the contents of the problem
    with open(problem_path, "r") as f:
        problem = f.read()

    if re.search(r"cnf\(", problem):
        return ProblemFormat.CNF
    elif re.search(r"fof\(", problem):
        return ProblemFormat.FOF
    elif re.search(r"tff\(", problem):
        return ProblemFormat.TF0
    elif re.search(r"\(set-logic|\(declare-sort|\(declare-fun", problem):
        return ProblemFormat.SMT2
    else:
        # Log a warning message
        log.warning("Could not infer the problem pformat. Setting FOF as default")
        return ProblemFormat.FOF


def check_if_uf_logic(problem_path: str) -> bool:
    # Get the contents of the problem
    with open(problem_path, "r") as f:
        problem = f.read()

    if re.search(r"\(set-logic UF\)", problem):
        return True
    else:
        return False


def problem_version_is_tff(version: ProblemFormat) -> bool:
    return version == ProblemFormat.TF0


def output_proof(proof_file: str) -> None:
    with open(proof_file, "r", newline=None) as f:
        proof = f.read()

    log.debug(f"Outputting proof from {proof_file}")
    print(proof)
