import glob
import os
import re
import logging
import shutil
import signal
import sys
import tempfile
from typing import Optional, TYPE_CHECKING, Dict

log = logging.getLogger()

if TYPE_CHECKING:
    from process import ProverProcess

# Global dict used to store the processes currently running
# the global scope enables process elimination upon interruption
PROVER_PROCESSES: Dict[str, "ProverProcess"] = {}


# TMP dir used to store tmp prover output
TMP_DIR = tempfile.mkdtemp(prefix="iprover_out_")


def check_prover_success(szs_status: str, ltb_mode: bool) -> bool:
    # Function for returning whether a terminated prover run was successfull or not
    if ltb_mode:
        # LTB mode check (uses axiom selector)
        if re.match("(Theorem|Unsatisfiable)", szs_status):
            return True
        else:
            return False
    # Standard zsz ontology success check
    else:
        if re.match(
            "(Theorem|Unsatisfiable|Satisfiable|CounterSatisfiable)", szs_status
        ):
            return True
        else:
            return False


def get_prover_output_status(prover_output_file_path: str) -> str:
    with open(prover_output_file_path, "r") as f:
        prover_out = f.read()

    try:
        # Get the SZS status
        szs_line = re.search("% SZS status.*", prover_out)
        if szs_line is None:
            return "Stopped"

        szs_status = szs_line.group(0).split()[3]

    except IndexError:
        szs_status = "Stopped"

    return szs_status


def get_tmp_out_file():
    # Create the tmp file in the current tmp directory and return the file name
    fd, filepath = tempfile.mkstemp(prefix=TMP_DIR + "/")
    os.close(fd)  # Close the open file descriptor
    return filepath


def remove_file(file):
    try:
        os.remove(file)
    except FileNotFoundError:
        pass


def register_functions_and_signals():
    log.debug("Registering signals SIGINT and SIGTERM")
    signal.signal(signal.SIGINT, graceful_exit)  # type: ignore
    signal.signal(signal.SIGTERM, graceful_exit)  # type: ignore


def graceful_exit(signal_number: Optional[signal.Signals] = None, frame=None, **kwargs):
    if signal_number is not None:
        log.warning(
            f"Received signal {signal_number}, killing processes and removing temp files"
        )

    # Kill all processes
    kill_all_prover_processes()

    # Cleanup all folders
    if logging.root.level > logging.DEBUG:  # Only clean tmp dir if not debugging
        clean_tmp_dir()
    sys.exit(0)


def kill_all_prover_processes():
    proc_list = list(PROVER_PROCESSES.items())
    for key, process in proc_list:
        process.kill()
        del PROVER_PROCESSES[key]


def clean_tmp_dir():
    # Clean tmp folder
    try:
        shutil.rmtree(TMP_DIR)
        log.debug(f"Removed tmp dir: {TMP_DIR}")
    except FileNotFoundError:
        pass


def clean_tmp_folder_contents():
    try:
        files = glob.glob(TMP_DIR + "/*")
        for f in files:
            os.remove(f)
    except Exception as err:
        log.warning("Could not remove some file within the tmp dir: {0}".format(err))


def create_dir_if_not_exists(dir_path):
    try:
        os.makedirs(dir_path)
    except FileExistsError:
        # directory already exists
        pass
