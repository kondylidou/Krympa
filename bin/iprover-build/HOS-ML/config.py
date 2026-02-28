# Configuration file for a few of the program constants

# The prover executables path - could be made into a dict?
PROVER = "./res/iproveropt"
#PROVER = "./res/iproveropt_static_z3"
# PROVER = "./res/iproveropt_static"
# PROVER_Z3 = "./res/iproveropt_2021_12_15_z3"


# VClausifier executable
# CLAUSIFIER_PATH = "res/vclausify_rel_safe"
CLAUSIFIER_PATH = "res/vclausify_rel"

# The time limit grace when attempting a single problem
PROBLEM_ATTEMPT_GRACE = 5

# The grace associated with an LTB batch
LTB_ATTEMPT_GRACE = 10

# The time for sleeping between checking the prover processes
PROVER_PROC_SLEEP_TIME = 0.5

# Time limit for the parsing test (currently unused)
PARSE_TEST_TIMEOUT = 2
