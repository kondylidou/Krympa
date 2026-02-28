#!/bin/bash
# part of iProver (c) Konstantin Korovin

#set -x

# Examples: 
# ./tests_run.sh
# ./tests_run.sh tests_basic.csv
# ./tests_run.sh -c ./iproveropt-multi-core.sh -t 5 -o " "


FILE=tests_basic.csv
CMD_PATH=$(dirname $0)

PASSED=0
FAILED=0

glb_start_time=`date +%s`

usage_msg="$SCRIPT_NAME [-h] [-c cmd] [-o opts] [-t timeout] [-p PATH] FILE.csv

-h      help
-p      path to test directory
-c      override cmds in FILE.csv
-o      override options in FILE.csv    
-t      override timeout in FILE.csv

FILE.csv is the file with the test description in the form:

test_file,exec_name,exec_options,pass_string,test_goal

 Examples: 
 ./tests_run.sh
 ./tests_run.sh tests_basic.csv
 ./tests_run.sh -c ./iproveropt-multi-core.sh -t 5 -o \" \"
        
"


while getopts ":hp:c:o:t:" option; do      
    case "${option}" 
    in
        h)  echo "$usage_msg" 
            exit 1
            ;;
        p) TEST_PATH=${OPTARG}
           ;;
        c) CMD_IN=${OPTARG}
           ;;
        o) OPT_IN=${OPTARG}
           ;;
        t) TIMEOUT_IN=${OPTARG}
           ;;
        ?) echo "Error: unsupported options"
           echo ""
           echo "$usage_msg"
           exit 1
        ;;
    esac    
done


# remaining args
shift $(($OPTIND - 1))
if [[ "$@" != "" ]] ; then
    FILE="$@"
fi


#--------- processes

timeout_code=2

# 0 if running 
function check_process {
    local PID=$1
#    echo "dbg:  check_process: $PID"
    kill -0 "$PID" >/dev/null 2>&1
    return 
}

function run_process_timeout {
    local PID=$1
    local timeout=$2
    local lcl_start_time=`date +%s`

    check_process $PID
    local is_running=$!
    while [[ $is_running -eq 0 ]]; do
                
        local lcl_current_time=`date +%s`
        lcl_runtime=$((lcl_current_time - lcl_start_time))
        if [[ $lcl_runtime -ge $timeout ]]; then
            return $timeout_code
        fi
        sleep 0.1
        check_process $PID
        is_running=$!
    done
}


#--------------

echo 
echo "======= Benchmarks: $FILE =========="
echo
#echo "test_id cmd opts problem timeout exp_result descr"

while IFS="," read -r test_id cmd opts problem timeout exp_result descr
do
    if [[ ${test_id:0:1} == "#" ]] ; then
        continue # skip comments 
    fi
    
# override if given in cmd line    
    if [ ! -z "$CMD_IN" ]; then
        cmd=$CMD_IN
    fi
    if [ ! -z "$OPT_IN" ]; then
        opts=$OPT_IN
    fi
    if [ ! -z "$TEST_PATH" ]; then
        problem=$TEST_PATH/$problem
    fi
    if [ ! -z "$TIMEOUT_IN" ]; then
        timeout=$TIMEOUT_IN
    fi   
       
    cmd=$CMD_PATH/$cmd
    
 #   echo "------ test $test_id"    
    echo "$test_id, $cmd, $opts, $problem, $timeout, $exp_result, $descr"
    
    lcl_start_time=`date +%s`
    echo "$cmd $opts $problem"
    #$cmd $opts $problem 2>&1 | grep -q "$exp_result"  > /dev/null 2>&1
    res=$(nohup $cmd $opts $problem 2>&1 &)
#    echo "res: $res"
    run_process_timeout $! $timeout
    lcl_end_time=`date +%s`
    lcl_runtime=$((lcl_end_time - lcl_start_time))
      
    echo "$res" | grep -q "$exp_result"  > /dev/null 2>&1    
    passed=$?
    if [ $passed -eq 0 ]; then
        echo "PASSED: ${lcl_runtime}s"
        ((PASSED++))
    else
        echo "FAILED: ${lcl_runtime}s"
        ((FAILED++))
    fi
    echo ""
done < $FILE

glb_end_time=`date +%s`

glb_runtime=$((glb_end_time - glb_start_time))

echo
echo "======= Time: ${glb_runtime}s"
echo "PASSED: $PASSED"
echo "FAILED: $FAILED"



exit $FAILED
