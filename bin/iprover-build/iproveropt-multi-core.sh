#!/bin/bash
# part of iProver (c) Konstantin Korovin
# multi core execution of a pretrained schedule

# sets STAREXEC_WALLCLOCK_LIMIT=timelimit
# add checks

set -o pipefail

#set -x

#START_DIR=$(dirname $0)
START_DIR=$(pwd)

HERE=$( dirname -- "$( readlink -f -- "$0"; )"; )
#IPROVER_DIR=$(dirname "${BASH_SOURCE[0]}")

IPROVER_DIR=$HERE

SCRIPT_NAME=$(basename "$0")


#HERE=$( dirname -- "$( readlink -f -- "$0"; )"; )

#HERE=$(realpath "$0")


# Compares two version numbers.
#
# Exit status: 0 if the first version number is greater or equal to
# the second one, and 1 otherwise.
version_geq()
{
    test $(echo -e "$1\n$2" | sort  -V | head -n 1) != $2
}

#--------

echo ""
echo "% ======== iProver multi-core TPTP/SMT ========="
echo ""

# default values; can be changed by options



#-------------

#LANG=tptp # tptp|smt
LANG=

CORES=8
# defined below
SCHEDULE=
STAREXEC_WALLCLOCK_LIMIT=300 # redefined by -t

SCHEDULE_MODE="mixed"

usage_msg="$SCRIPT_NAME [-h] [-v] [-t n] [-c n] [-] [-s {fof_schedule|fnt_schedule|ueq_schedule|tfa_schedule}]] problem.p

-h      help

-t      time limit 
        default: $STAREXEC_WALLCLOCK_LIMIT

-c      number of cores; 
        default: $CORES

-l      tptp|smt|prover9
        Prover9 format requires TranslatorX to be installed
        https://gitlab.com/cfmsousa/TranslatorX

-s
        leave unspecified for a defualt mixed sat/unsat schedule
        fof_schedule: general fof problems (tptp)
        fnt_schedule: model finding (tptp)
        ueq_schedule: unit equality (tptp)
        tfa_schedule: tff including tfa (arithmetic) (tptp)
        epr_schedule: epr (tptp)
        default: $SCHEDULE

-n      skip checks

-d      deploy mode when scripts are complied with python
        used in CASC/SMT-COMP after deploy scripts

-v      verbose

Examples:

./$SCRIPT_NAME -t 300 -s fof_schedule Examples/problem.p
./$SCRIPT_NAME -t 300 -c 8 -s ueq_schedule Examples/problem.smt2

"

if [[ $# -eq 0 ]]
then
    echo "$usage_msg"
    exit 1
fi

#---------- problem

# PROBLEM="${@: -1}"
# "${@: -1}" does not work in StarExec bash
# check that works in Starexec

PROBLEM=${@:${#@}}

#full path 
if [ ! "${PROBLEM:0:1}" = "/" ] && [ ! "${PROBLEM:0:1}" = "~" ]
then # relative  path
    PROBLEM="$(pwd)/$PROBLEM"    
fi

if [ ! -f "$PROBLEM" ]; then
    echo "error: problem does not exists: usage: -h"
    exit 1
fi


#-------- define default schedule

#case $LANG in
#    tptp)
        
#    ;;
#    smt)
#        ulimit -s $ULIMIT
#    
#          grep "(set-logic UF)" $PROBLEM &> /dev/null
#          is_UF=$?
#          
#          if [ $is_UF -eq 0 ]; 
#          then
#              SCHEDULE="smt_comp_2024_starexec_uf"
#              CONTEXT="smtcomp_uf"
#    else
#        SCHEDULE="smt_comp_2024_starexec"
#        CONTEXT="smtcomp"
#    fi
    
CHECK_FLAG=1

DEPLOY_MODE=0

# if option -t 300 is supplied
while getopts ":hndt:c:l:s:m:v" option; do      
    case "${option}" 
        in
        h)  echo "$usage_msg" 
            exit 1
            ;;
        t) STAREXEC_WALLCLOCK_LIMIT=${OPTARG}
            ;;
        c) CORES=${OPTARG}
            ;;
        l) LANG=${OPTARG}           
            ;;
        s) SCHEDULE=${OPTARG} # convert smt_schedule to ...
           ;;
        v) VERBOSE="-d" # use -d for dbg rather -v as it more informative
           ;;
        n) CHECK_FLAG=0
           ;;
        d) DEPLOY_MODE=1
           ;;
#        m) SCHEDULE_MODE=${OPTARG}
#            ;;
        ?) echo "Error: unsupported options"
            echo ""
            echo "$usage_msg"
            exit 1
            ;;
    esac    
done    

#-------- Deploy mode -- python complied in; non-deployed call python3

if [[ $DEPLOY_MODE -ne 0 ]]
then
    RUN_PROBLEM="./run_problem"
else
    #----- check if python3 is installed and  >= $MIN_PYTHON_VER
    
    MIN_PYTHON_VER="3.11"
    PYTHON_VER=$(python3 --version | awk '{print $2}')

    if [[ $? -ne 0 ]] || version_geq $PYTHON_VER $MIN_PYTHON_VER -ne 0 ;
    then    
        echo "Error: please install python3 >= 3.11"
        exit 1
    fi
    
    HOS_ML="$IPROVER_DIR/HOS-ML"
    if [ ! -d "$HOS_ML" ]; then
        echo "error: should be run from iprover top directory containing HOS-ML"
        exit 1
    fi
    cd "$HOS_ML"
    
    export PYTHONPATH=$HERE/HOS-ML/src
    RUN_PROBLEM="python3 ./run_problem.py"
    
fi


#------------- detecting lang
#

if [ -z "$LANG" ]; then
    if grep -q "cnf(\|fof(\|tff(" $PROBLEM; then
        LANG=tptp
    else
        if grep -q "(assert\|(declare-fun" $PROBLEM; then
            LANG=smt
        else
            if grep -q "^formulas" $PROBLEM; then
                LANG=prover9
            else
                echo "problem language could not be auto detected: specify problem lang using -l"
                exit 1
            fi
        fi
    fi
fi

echo "% Detected problem language: $LANG"


#------ 



# Increase the soft ulimit

SYS=$(uname -s)

if [ "$SYS" = "Darwin" ]; 
then     
    ULIMIT=60000
else
    ULIMIT=200000
fi

#ulimit -s $ULIMIT


if [ -z "$STAREXEC_WALLCLOCK_LIMIT" ]; then
    #  echo 	"error: time limit should be provided by setting e.g. env: export STAREXEC_WALLCLOCK_LIMIT=600"
    echo 	"error: time limit should be provided; usage: -h"
  exit 1
fi


# used in SMT/Prover9 only
TCF_TMP=$(mktemp /tmp/iprover.tmp.tcf.XXXXXX)
OUT_TMP1=$(mktemp /tmp/iprover.tmp.out.XXXXXX)
OUT_TMP2=$(mktemp /tmp/iprover.tmp.out.XXXXXX)
OUT_TMP3=$(mktemp /tmp/iprover.tmp.out.XXXXXX)
OUT_SPLIT_PREF="/tmp/iprover.tmp.out.split.xx"

function rm_tmp_files {
    rm -f "$TCF_TMP"
    rm -f "$OUT_TMP1" "$OUT_TMP2" "$OUT_TMP3"   
    rm -f "${OUT_SPLIT_PREF}00" "${OUT_SPLIT_PREF}01" 
}

function terminate {
#    killChildProcesses
    #dbg
    #    cat "$OUT_TMP1" "$OUT_TMP2" "$OUT_TMP3"
    CHILDREN=$($HERE/get_children.sh $$)

    # kill all children processes
    kill -9 ${CHILDREN} >/dev/null 2>&1
    wait ${CHILDREN} 2>/dev/null
    
    rm_tmp_files
    cd $START_DIR
    exit $1
}

function interrupted {
#       echo "interrupted" >> $LOGFILE
        echo "Interrupted"
        terminate 1
}

trap interrupted SIGINT SIGQUIT SIGTERM

#------------ end kill children

#
function check_success {
    grep -q '% SZS status \(Theorem\|Unsatisfiable\|Satisfiable\|CounterSatisfiable\)' $1    
}

# checks if at least one of the files has success then cat first one
function check_success_files {
    local FILES=$1
    for file in $FILES; do
        check_success $file
        if [ $? -eq 0 ]; then
            cat $file
            return 0
        fi
    done
    return 1
}

# 0 if running 
function check_process {
local    PID=$1
#    echo "dbg:  check_process: $PID"
    kill -0 "$PID" >/dev/null 2>&1
    return 
}

# 0 if at least one is running
function check_processes {
    local PIDs=$1
    for pid in $PIDs; do
        check_process $pid
        if [ $? -eq 0 ]; then
            return 0
        fi      
    done
    return 1
}


# runs "PID1,OUT_FILE1 PID2,OUT_FILE2 ..." with corresponding OUT_ FILES until success

function run_until_success {
    
    RUNNING=0
    while [[ $RUNNING -eq 0 ]]; do
        RUNNING=1
        for arg in "$@"; do 
            PID=${arg%,*}; # before ","
            OUT_FILE=${arg#*,}; # after ","
            check_process "$PID"
            if [ $? -eq 0 ]; then                
                RUNNING=0
            fi
            check_success_files $OUT_FILE
            if [ $? -eq 0 ]; then
                return 0
            fi        
        done
        sleep 0.1
    done
    return 1
}


#--------- TPTP

function run_tptp {
    local PROBLEM=$1
    
    ulimit -s $ULIMIT
    if [ ! -z "$SCHEDULE" ]; then # SCHEDULE set in cmd line	
	if [ "$SCHEDULE" = "epr_schedule" ]; then

	        nohup $RUN_PROBLEM $VERBOSE --no_cores $CORES --heuristic_context casc_unsat --schedule epr_unsat_schedule  $PROBLEM $STAREXEC_WALLCLOCK_LIMIT  > $OUT_TMP2  2>/dev/null&
	        PID_UNSAT=$!

		nohup $RUN_PROBLEM $VERBOSE --no_cores 3 --heuristic_context fnt --schedule epr_sat_schedule  $PROBLEM $STAREXEC_WALLCLOCK_LIMIT > $OUT_TMP1 2>/dev/null&
        	PID_SAT=$!

	        nohup $RUN_PROBLEM $VERBOSE --no_cores 3 --heuristic_context default --schedule default_sched_complete  $PROBLEM $STAREXEC_WALLCLOCK_LIMIT  > $OUT_TMP3  2>/dev/null&
                PID_DEF=$!

              	run_until_success "$PID_UNSAT,$OUT_TMP2" "$PID_SAT,$OUT_TMP1" "$PID_DEF,$OUT_TMP3"
	        if [ $? -eq 0 ]; then
	            return 0 
        	fi        
	else	
	    if [ "$SCHEDULE" = "fnt_schedule" ]; then
		context="fnt"
	    else 
		context="casc_unsat"
	    fi	
	    nohup $RUN_PROBLEM $VERBOSE --no_cores $CORES --schedule $SCHEDULE --heuristic_context $context $PROBLEM $STAREXEC_WALLCLOCK_LIMIT > $OUT_TMP1  2>/dev/null&
            run_until_success "$!,$OUT_TMP1"
	    if [ $? -eq 0 ]; then
        	return 0
	    fi
	fi	
    else
        # schedule was not set run in parallel sat and unsat
        nohup $RUN_PROBLEM $VERBOSE --no_cores $CORES --heuristic_context fnt --schedule fnt_schedule  $PROBLEM $STAREXEC_WALLCLOCK_LIMIT > $OUT_TMP1  2>/dev/null&
        PID_SAT=$!
        nohup $RUN_PROBLEM $VERBOSE --no_cores $CORES --heuristic_context casc_unsat --schedule fof_schedule  $PROBLEM $STAREXEC_WALLCLOCK_LIMIT  > $OUT_TMP2  2>/dev/null&
        PID_UNSAT=$!
        
        run_until_success "$PID_SAT,$OUT_TMP1" "$PID_UNSAT,$OUT_TMP2"
        if [ $? -eq 0 ]; then
            return 0
        fi
    fi
    echo "SZS status Unknown"
}


#----------- SMT

function run_smt {
    local PROBLEM=$1
    
    ulimit -s $ULIMIT
    
    grep "(set-logic UF)" $PROBLEM &> /dev/null
    is_UF=$?
    
    if [ $is_UF -eq 0 ]; 
    then
        CONTEXT="smtcomp_uf"
        # schedule not set in cmd line
        if [ -z "$SCHEDULE" ]; then
            SCHEDULE="smt_comp_2024_starexec_uf"
        fi
    else
        CONTEXT="smtcomp"
        # schedule not set in cmd line
        if [ -z "$SCHEDULE" ]; then
            SCHEDULE="smt_comp_2024_starexec"
        fi
    fi
    

            #            python3 prover_driver.py --no_cores $CORES --schedule_mode $SCHEDULE_MODE --schedule $SCHEDULE $TCF_TMP $STAREXEC_WALLCLOCK_LIMIT > $OUT_TMP  2>/dev/null

    #python3 prover_driver.py --no_cores $CORES --schedule_mode $SCHEDULE_MODE --schedule $SCHEDULE $PROBLEM $STAREXEC_WALLCLOCK_LIMIT > $OUT_TMP  2>/dev/null
#    python3 run_problem.py --no_cores $CORES --heuristic_context casc_unsat --schedule $SCHEDULE  $PROBLEM $STAREXEC_WALLCLOCK_LIMIT    
#    cat $OUT_TMP
    out=$($RUN_PROBLEM $VERBOSE $PROBLEM $STAREXEC_WALLCLOCK_LIMIT --heuristic_context $CONTEXT --no_cores $CORES \
                  --schedule $SCHEDULE --problem_version smt2 )
    
    if echo $out | grep -q "SZS status Theorem\|SZS status Unsatisfiable"
    then
        echo "unsat"
        #exit 20
    else
        if echo $out | grep -q "SZS status CounterSatisfiable\|SZS status Satisfiable"
        then
            echo "sat"
            #       exit 10
        else
            echo "unknown"
            #        exit 0
        fi
    fi
}


#-------- test

if [[ $CHECK_FLAG -ne 0 ]]
then
    echo "% Checking..."
    out=$($RUN_PROBLEM --no_cores 2 --schedule fof_schedule $IPROVER_DIR/Examples/PUZ001-1.p 5.)
    if echo $out | grep -q "SZS status Theorem\|SZS status Unsatisfiable"
    then
        echo "% Check passed"
    else
        echo "Error: something is wrong: please check your set up and options"
        exit 1
    fi    
fi

#------- Translate from Prover9 to TPTP
if [[ $LANG = "prover9" ]]; then
    # check if TranslatorX is installed    
    TranslatorX &> /dev/null
    if [[ $? -ne 0 ]]
    then
        echo "Error: for processing Prover9 format TranslatorX should be installed:"
        echo "       https://gitlab.com/cfmsousa/TranslatorX"
        exit 1
    fi
    TranslatorX -t $PROBLEM | $IPROVER_DIR/scripts/translatorx_wrapper.sh > $TCF_TMP
    PROBLEM=$TCF_TMP
fi

#-------------------
echo "% Proving..."
#-------------------

#---------------

case $LANG in 
    tptp)
        run_tptp $PROBLEM
#        if [ "$SCHEDULE" = "tff_schedule" ]; then 
#            run_tff 
#        else
#            run_tptp
#        fi
        ;;
    smt) run_smt $PROBLEM
         ;;
    prover9) run_tptp $PROBLEM
             ;;
esac 


terminate 0


#=================== OLD ===============


#-----------kill children: first need to collect all then kill
#function allChildren {
#   local ppid=$1
#    if [ "$SYS" = "Darwin" ]; 
#    then
#        local CHILDREN=`ps xao pid,ppid | awk -v ppid=$ppid '$2 == ppid' | awk '{printf "%s ",$1;}'`
##        local CHILDREN=`ps -o pid,ppid | awk -v ppid=$ppid '$2 ~ ppid' | awk '{printf "%s ",$1;}'`
##        local CHILDREN=`pstree -p $ppid | tr "\n" " " |sed "s/[^0-9]/ /g" |sed "s/\s\s*/ /g"`
##        local CHILDREN=`ps -o pid,ppid | grep '^[0-9]' | grep ' '$ppid | cut -f 1 -d ' '`
#    else
#        local CHILDREN=`ps -o pid --no-heading --ppid $ppid`
#    fi
#
#    if [ ! -z "$CHILDREN" ];
#    then
#        for child_pid in ${CHILDREN}; 
#        do
#            allChildren ${child_pid}
#        done
#    fi
#    echo $ppid      
#}



#function killChildProcesses {
##    echo "dbg: killChildProcesses: main PID: $$"
#    local CHILDREN=$(allChildren $$)
#    # remove $$ process itself from childern
#    local CHILDREN=$(echo $CHILDREN | sed "s/$$//g") 
# #   echo "dbg: killChildProcesses: CHILDREN:$CHILDREN"
#    kill -9 ${CHILDREN} 2>/dev/null
# #   killtree "$$"
#}

#

#--------- TFF
#function run_tff {
#    ulimit -s $ULIMIT
#    ./res/vclausify_rel --mode tclausify --show_fool true $PROBLEM |sed -e "s/[']\+/'/g" | sed -e "s/\([^[:blank:](),~]\)\('\)\([^[:blank:](),:]\)\([^']*\)\('\)/\1\3\4\5/g" > $TCF_TMP  
 
#    vclausify_exit_status=$?
#    
#    if [ $vclausify_exit_status -ne 0 ]; then
#        cat $TCF_TMP
#        echo "error: clausifier exit with status: $vclausify_exit_status"
#        echo unknown        
#        terminate 1    
#    else        
#        if [ "$SCHEDULE" = "tff_schedule" ]; then
#            #redefine schedule
#            SCHEDULE="fof_schedule"
#        fi
#        
#        python3 prover_driver.py --no_cores $CORES --schedule_mode $SCHEDULE_MODE --schedule $SCHEDULE $TCF_TMP $STAREXEC_WALLCLOCK_LIMIT > $OUT_TMP  2>/dev/null
#        if cat $OUT_TMP | grep -q "SZS status Theorem\|SZS status Unsatisfiable"
#        then
#            # add clausifier outpout after % SZS output start
#            csplit -f $OUT_SPLIT_PREF $OUT_TMP -sk  /'% SZS output start'/+1
#            cat ${OUT_SPLIT_PREF}00 $TCF_TMP ${OUT_SPLIT_PREF}01
#            cat $OUT_TMP
#        else        
#	    if cat $OUT_TMP | grep -q "SZS status Satisfiable\|SZS status CounterSatisfiable"
#	    then
#	        echo "Incomplete SAT"
#	        echo "SZS status Unknown"
#	    fi	
#        fi          
#    fi
#}


# if echo $out | grep -q "SZS status Theorem\|SZS status Unsatisfiable"
#    then
#        echo "unsat"
#    else        
#        cat $OUT_TMP
#	if cat $OUT_TMP | grep -q "SZS status Satisfiable\|SZS status CounterSatisfiable"
#	then
#	    echo "sat"
#	else
#	    echo "unknown"
#	fi	
#   fi 
#
#
#
#-s         
#        fof_schedule: general fof problems (tptp)
#        fnt_schedule: model finding (tptp)
#        ueq_schedule: unit equality (tptp)
#        tff_schedule: tff including tfa (arithmetic) (tptp)
#        smt_schedule: smt  
#        default: $SCHEDULE
