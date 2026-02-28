#!/bin/bash
# stop_children.sh pid
# all children processes of pid excliding pid itself

#set -x

PID=$1

SYS=$(uname -s)

#-----------kill children: first need to collect all then kill
function allChildren {
    local ppid=$1
    if [ "$SYS" = "Darwin" ]; 
    then
        local CHILDREN=`ps xao pid,ppid | awk -v ppid=$ppid '$2 == ppid' | awk '{printf "%s ",$1;}'`
#        local CHILDREN=`ps -o pid,ppid | awk -v ppid=$ppid '$2 ~ ppid' | awk '{printf "%s ",$1;}'`
#        local CHILDREN=`pstree -p $ppid | tr "\n" " " |sed "s/[^0-9]/ /g" |sed "s/\s\s*/ /g"`
#        local CHILDREN=`ps -o pid,ppid | grep '^[0-9]' | grep ' '$ppid | cut -f 1 -d ' '`
    else
        local CHILDREN=`ps -o pid --no-heading --ppid $ppid`
    fi

    if [ ! -z "$CHILDREN" ];
    then
        for child_pid in ${CHILDREN}; 
        do
            allChildren ${child_pid}
        done
    fi
    echo $ppid      
}



CHILDREN=$(allChildren $PID)
CHILDREN=$(echo $CHILDREN | sed "s/$$//g" | sed "s/$PID//g")
echo $CHILDREN

#kill all childern
#kill -9 ${CHILDREN} 2>/dev/null





