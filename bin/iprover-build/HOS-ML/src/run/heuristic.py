import re
import logging
from enum import Enum
from typing import Union, Dict, Optional

from config import CLAUSIFIER_PATH
from context_modifiers import HEURISTIC_CONTEXT_MODIFIERS, CLAUSIFIER_CONTEXT_MODIFIERS
from run.problem import ProblemFormat

log = logging.getLogger()


class ClausifierMode(Enum):
    FOF = "fof"
    TFF = "tff"
    SMT = "smt"


class Clausifier:
    def __init__(
        self,
        options: str | None,
        clausifier_mode: ClausifierMode,
        context: Optional[str] = None,
    ):
        self.__path = CLAUSIFIER_PATH
        if options is None:
            self.options = "--mode clausify -t 30"
        else:
            self.options = options
        self.clausifier_mode = clausifier_mode

        self._initialise_clausifier()
        if context is not None:
            self._set_context(context)

    @property
    def path(self):
        return self.__path

    def _initialise_clausifier(self):
        self._set_clausifier_mode()
        self._add_fool_terms()
        self._ensure_timelimit_option()
        self._set_input_syntax()

    def _set_context(self, context: Optional[str]):
        if context in CLAUSIFIER_CONTEXT_MODIFIERS:
            log.debug(f"Setting clausifier context: {context}")
            self.options += " " + " ".join(CLAUSIFIER_CONTEXT_MODIFIERS[context])

    def _ensure_timelimit_option(self):
        if "-t" not in self.options:
            self.options += " -t 10.0"  # Add a dummy time

    def _set_clausifier_mode(self):
        # Set the clausifier mode
        self.options = re.sub(
            "clausify|tclausify", self._get_clausifier_mode_str(), self.options
        )

    def _get_clausifier_mode_str(self):
        if self.clausifier_mode is ClausifierMode.FOF:
            return "clausify"
        elif self.clausifier_mode in [ClausifierMode.TFF, ClausifierMode.SMT]:
            return "tclausify"
        else:
            raise ValueError(
                f"Clausifier string not implemented for {self.clausifier_mode}"
            )

    def _set_input_syntax(self):
        param = "--input_syntax"

        # Remove from options if exists
        self.options = re.sub(rf"{param} \S+", "", self.options)

        if self.clausifier_mode is ClausifierMode.SMT:
            self.options += f" {param} smtlib2"

    def _add_fool_terms(self):
        # Add FOOL terms if not in the option, and the CMode is TFF or SMT
        fool_term_opt = "show_fool"
        if (
            self.clausifier_mode in [ClausifierMode.TFF, ClausifierMode.SMT]
            and fool_term_opt not in self.options
        ):
            # Insert inside the quoted string
            log.debug(f"Added {fool_term_opt}")
            self.options += f" --{fool_term_opt} true"

    def get_options_str(self, timeout: float) -> str:
        # Compute the time
        options = re.sub(
            "-t [0-9]+([,.][0-9]+)?", "-t {0:.2f}".format(timeout), self.options
        )
        return f"{options}".strip()

    def get_cmd(self, timeout: float) -> str:
        # Quote options
        return f'--clausifier {self.path} --clausifier_options "{self.get_options_str(timeout)}"'.strip()

    def __str__(self) -> str:
        return f"{self.__class__} {self.path} {self.options}"


class Heuristic:
    def __init__(
        self,
        heur_file: str,
        context: str,
        clausifier: Optional[Clausifier],
#KK 2025
#        preprocessing_flag: bool = True,
         preprocessing_flag: bool = False,

        proof_out: bool = True,
    ):
        self.heur_file = heur_file
        self.options = process_heuristic_file(self.heur_file)

        self.clausifier = clausifier

        self.preprocessing_flag = preprocessing_flag
#        self._set_preprocessing_flag()

        self.context = context
        self._set_context_parameters()

        self.proof_out = proof_out
        self._set_proof_model_out()

#    def _set_preprocessing_flag(self):
#        self.options["preprocessing_flag"] = (
#KK            
#            "true" if self.preprocessing_flag else "false"
#            
#        )

    def _set_proof_model_out(self):
        self.options["proof_out"] = "true" if self.proof_out else "false"
        self.options["sat_out_model"] = "pos" if self.proof_out else "none"

    def _set_context_parameters(self):
        # Remove context parameters if set
        context_parameters = HEURISTIC_CONTEXT_MODIFIERS[self.context]
        log.debug(
            f"Setting context {self.context} for heuristic {self.heur_file} with values: {context_parameters}"
        )

        for parameter in context_parameters:
            option, value = parameter.split(" ", 1)
            option = option[2:]  # Remove double dash
            self.options[option] = value

    def get_no_options(self) -> int:
        return len(self.options)

    def get_heuristic_cmd(self, timeout: float) -> str:
        options = " ".join(f"--{opt} {val}" for opt, val in self.options.items())
#scale clausifier timeout to 1/3
        if self.clausifier is not None:
            options += " " + self.clausifier.get_cmd(timeout/3)

        options += f" --time_out_real {timeout:.2f}"
        return options

    def get_option_value(self, op: str) -> Union[str, float, None]:
        return self.options.get(op, None)

    def __str__(self) -> str:
        return f"{self.__class__} file:{self.heur_file} Options:{self.get_no_options()}"


def read_parameters(heuristic_path: str) -> Dict[str, str]:
    options = {}
    with open(heuristic_path, "r") as fp:
        parameters = fp.read().splitlines()

    for par in parameters:
        option, value = par.split(" ", 1)
        option = option[2:]  # Remove double dash
        if option in options:
            log.error(f"Option {option} already exists in heuristic {heuristic_path}")
        options[option] = value.strip()  # Remove whitespace before and after

    return options


def quote_list_options(options: Dict[str, str]) -> Dict[str, str]:
    for option, value in options.items():
        if value[0] == "[" and value[-1] == "]":
            options[option] = '"' + value + '"'  # Quote

    return options


def remove_unwanted_options(options: Dict[str, str]) -> Dict[str, str]:
    # Remove amended and legacy options
    remove_options = [
        "time_out_real",
        "clausifier",
        "clausifier_options",
        "res_out_proof",
        "inst_out_proof",
        "sat_out_model",
        "sup_out_proof",
    ]
    for opt in remove_options:
        options.pop(opt, None)
    return options


def process_clausifier_file(heuristic_file_path: str) -> Optional[str]:
    # Want to extract the clausifier option - if it exists
    with open(heuristic_file_path, "r") as f:
        conf = f.read().splitlines()

    options = None
    for line in conf:
        if "clausifier_options" in line:
            _, options = line.split(" ", 1)
            break
    return options


def process_heuristic_file(heuristic_file_path: str) -> Dict[str, str]:
    # Load the heuristic parameters
    options = read_parameters(heuristic_file_path)

    # Remove unwanted heuristic options
    options = remove_unwanted_options(options)

    # Quote list options (with brackets)
    options = quote_list_options(options)

    return options


def get_clausifier_mode(pformat: ProblemFormat) -> ClausifierMode:
    if pformat in [ProblemFormat.FOF, ProblemFormat.CNF]:
        return ClausifierMode.FOF
    elif pformat in [ProblemFormat.TF0]:
        return ClausifierMode.TFF
    elif pformat in [ProblemFormat.SMT2]:
        return ClausifierMode.SMT
    else:
        raise NotImplementedError()


def get_heuristic(
    heuristic_file_path: str, heuristic_context: str, pformat: ProblemFormat, **kwargs
) -> Heuristic:
    # Infer clausifier mode
    clausifier_mode = get_clausifier_mode(pformat)
    clausifier_options = process_clausifier_file(heuristic_file_path)
    if clausifier_options is None:
        log.warning(
            f'Clausifier option not provided in the heuristic config "{heuristic_file_path}", setting default options.'
        )
    claus = Clausifier(clausifier_options, clausifier_mode, heuristic_context)

    heur = Heuristic(
        heuristic_file_path, context=heuristic_context, clausifier=claus, **kwargs
    )
    return heur
