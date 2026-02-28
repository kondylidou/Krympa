import os
import signal
import subprocess
import time
import logging
from typing import Optional

from run import utils
from run.heuristic import Heuristic, Clausifier
from run.problem import _Problem
import config
from run.utils import check_prover_success, PROVER_PROCESSES

log = logging.getLogger()

PROCESS_GRACE = 3.0


def is_time_left(start_time: float, time_limit: float) -> bool:
    return time.time() - start_time < time_limit


def get_time_left(start_time: float, time_limit: float) -> float:
    return max((start_time + time_limit) - time.time(), 0)


class Process:
    def __init__(self, timeout: float):
        self.out_file: str = utils.get_tmp_out_file()
        self.out_file_errs = self.out_file + "_error"
        self.out_err: Optional[str] = None

        self.proc: Optional[subprocess.Popen] = None  # type:  ignore
        self.cmd: Optional[str] = None

        self.start_time: Optional[float] = None
        self.timeout: float = timeout

    @property
    def id(self) -> str:
        return "ProcessBaseClass"

    def _get_cmd(self) -> str:
        raise NotImplementedError()

    def start(self):
        self.cmd = self._get_cmd()
        log.debug(f"Running cmd: {self.cmd}")
        proc = subprocess.Popen(self.cmd, shell=True, preexec_fn=os.setsid)
        self.proc = proc
        self.start_time = time.time()

    def kill(self) -> None:
        # If a process is still active
        if self.is_running():
            # Get process group id and kill the group
            assert self.proc is not None

            try:
                pgrp = os.getpgid(self.proc.pid)
                os.killpg(pgrp, signal.SIGKILL)
                log.debug(f"Killed process: {pgrp}")
            except ProcessLookupError:
                # In case there is a race condition on the termination, in which case
                # process has terminated as it doesn't exist anymore.
                log.debug("Process already killed, skipping ...")

            _ = self.proc.communicate()  # Empty buffer

    def remove_out_files(self):
        utils.remove_file(self.out_file)
        utils.remove_file(self.out_file_errs)

    def _empty_buffers(self):
        assert self.proc is not None
        # The buffers sometimes hangs - need to be shut down
        # The clausifier is usually the root of this problem.
        try:
            # Attempt to empty
            _ = self.proc.communicate(timeout=3)
        except subprocess.TimeoutExpired:
            self.kill()  # Something is wrong (e.g. hanging) kill and go again.
            _ = self.proc.communicate()

    def _check_out_errs(self):
        # Empty buffers so file is read correctly
        self._empty_buffers()

        with open(self.out_file_errs, "r") as f:
            out_err = f.read().strip().rstrip()

        if out_err != "":
            self.out_err = out_err

    def is_running(self) -> bool:
        assert self.proc is not None
        if self.proc.poll() is None:
            return True
        else:
            return False

    def is_finished(self):
        return not self.is_running()

    def check_errors(self) -> bool:
        assert self.proc is not None
        self._check_out_errs()

        # If out error is not empty or non-valid exit code is given.
        # Processes can be killed with SIGKILL so -9 is also considered valid.
        if self.out_err is not None or self.proc.returncode not in [0, -9]:
            log.error(
                f'"{self}" ran with exit code {self.proc.returncode} and error: {self.out_err}'
            )
            log.error(f"cmd was: {self.cmd}")
            return True  # There are errors!

        return False


class ProverProcess(Process):
    def __init__(self, heuristic: Heuristic, problem: _Problem, timeout: float):
        super().__init__(timeout)

        self.heuristic = heuristic
        self.problem = problem

        self.szs_status: Optional[str] = None

    @property
    def id(self):
        return self.heuristic.heur_file

    def _get_cmd(self) -> str:
        return (
            f"{get_starexec_max_mem_cmd_str()}{config.PROVER} {self.heuristic.get_heuristic_cmd(self.timeout)} "
            f"{self.problem.path} 1>> {self.out_file} 2>> {self.out_file_errs}"
        )

    def success(self) -> bool:
        self.szs_status = utils.get_prover_output_status(self.out_file)
        return check_prover_success(self.szs_status, ltb_mode=self.problem.is_ltb)

    def __str__(self):
        return f"ProverProcess:{self.id}:{self.timeout}"


class ClausifierProcess(Process):
    def __init__(self, clausifier: Clausifier, problem: _Problem, timeout: float):
        super().__init__(timeout)

        self.clausifier = clausifier
        self.problem = problem

    @property
    def id(self):
        return f"{self.clausifier}:{self.timeout}:{self.problem}"

    def _get_cmd(self) -> str:
        return (
            f"./{config.CLAUSIFIER_PATH} {self.clausifier.get_options_str(self.timeout)} {self.problem.path} "
            f"1>> {self.out_file} 2>> {self.out_file_errs}"
        )

    def __str__(self):
        return f"ClausifierProcess:{self.id}:{self.timeout}"


def get_starexec_max_mem_cmd_str() -> str:
    # functon uses check for system cores and not no_cores specified by the schedule

    # Get the memory limit (if set) and enforce it
    max_mem = os.getenv("STAREXEC_MAX_MEM")

    if max_mem is None:
        log.debug("No max memory found")
        return ""

    log.debug(f"Max memory found to be: {max_mem}")
    max_mem_kbytes = int(max_mem) * 1000  # Convert
    log.debug(f"Megabyte to kilobyte conversion yields: {max_mem_kbytes}")

    # Divide by the number of system cores
    cpu_count = os.cpu_count()
    if cpu_count is None:
        log.warning("Could not determine the cpu count")
        return ""
    log.debug(f"CPU count is: {cpu_count}")

    # Enforce the memory limit
    mem_limit = max_mem_kbytes // cpu_count
    log.debug(f"Process memory limit is: {mem_limit}")
    return f" ulimit -v {mem_limit}; "


def process_has_finished(process: Process) -> bool:
    assert process.start_time is not None
    if process.is_finished():
        log.info(f"Process {process.id} has terminated")
        return True
    elif process.start_time + PROCESS_GRACE + process.timeout < time.time():
        log.info(f"Process {process.id} has ran past grace.")
        process.kill()
        return True
    else:
        return False


def check_prover_processes_terminated(problem: _Problem) -> _Problem:
    proc_list = list(PROVER_PROCESSES.items())
    for key, process in proc_list:
        # check if the process has finished
        if process_has_finished(process):
            # Handle run has finished
            del PROVER_PROCESSES[key]

            # Check for errors - reported on the error log
            process.check_errors()

            # Check if successful
            if process.success():
                log.info(f"Problem solved by {process}")
                problem.set_solved(process.out_file, process.szs_status)
                return problem  # Finished with success - not checking other processes
            else:
                # Do not remove files if debugging
                if logging.root.level > logging.DEBUG:
                    process.remove_out_files()

    return problem


def start_prover_process(
    heuristic: Heuristic, problem: _Problem, runtime: float
) -> None:
    # Create the process
    prover_process = ProverProcess(heuristic, problem, timeout=runtime)

    # Start it
    prover_process.start()
    log.info(f"Started process: {prover_process}")

    # Put it on the process dict
    assert prover_process.id not in PROVER_PROCESSES
    PROVER_PROCESSES[prover_process.id] = prover_process
