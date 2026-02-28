#!/usr/bin/bash

# init submission
#CASC_SCRIPTS_DIR=starexec/casc24/

# important to specify PYTHONPATH, otherwise some files will be silently picked up from the old installations
# e.g. new context modifiers  in context_modifiers.py ignored

export PYTHONPATH=$PWD:$PWD/src

# Edvard's
CASC_SCRIPTS_DIR=starexec/cascj12/

SMT_SCRIPTS_DIR=starexec/smtcomp24/

function create_description() {

  DESC="bin/starexec_description.txt"

  touch $DESC
  date >> $DESC
  echo "" >> $DESC

  echo "Current branch:  $(git branch --show-current)" >> $DESC
  echo "Latest Commit" >> $DESC
  git log -n 1 >> $DESC
}

# Delete bin.zip and bin/ if it exists
rm -rf bin.zip bin/

# Make bin dir
mkdir bin

# Copy over heuristics
cp -r ./heur bin/
cp -r ./heur_sat bin/
cp -r ./heur_smt bin/
cp -r ./heur_smt_sat bin/


# Check if cx_freeze exists
python3 -c 'import cx_Freeze' 2> /dev/null ;
if [ $? -ne 0 ]
then
    echo "cx_Freeze not found! Installing.."
    python3 -m pip install cx_Freeze
fi

python3 -m cx_Freeze -c run_problem.py --target-dir dist -s && echo "Compiled program"
cp -r dist/* bin


# Copy over the prover and clausifier specified in res
mkdir bin/res
PROVER_PATH=$(grep -oP "^PROVER = \"\K.*(?=\")" config.py)
CLAUSIFIER_PATH=$(grep -oP "^CLAUSIFIER_PATH = \"\K.*(?=\")" config.py)
cp $PROVER_PATH bin/res/ && echo "Copied prover: $PROVER_PATH"
cp $CLAUSIFIER_PATH bin/res/ && echo "Copied clausifier: $CLAUSIFIER_PATH"

# Copy over star_exec specifics
cp starexec/starexec_build bin/
cp starexec/get_tptp_variable.sh bin/


# this could be improved and maybe be used a provided argument?

#cp starexec/smtcomp23/starexec_run_* bin/
#cp starexec/casc29/starexec_run_* bin/
#cp starexec/cascj12/starexec_run_* bin

cp ${SMT_SCRIPTS_DIR}/starexec_run_* bin/
cp ${SMT_SCRIPTS_DIR}/iprover* bin/
cp ${SMT_SCRIPTS_DIR}/README* bin/

cp ${CASC_SCRIPTS_DIR}/starexec_run_* bin/
cp ${CASC_SCRIPTS_DIR}/README bin/
cp ${CASC_SCRIPTS_DIR}/iprover_*zip bin/
cp ${CASC_SCRIPTS_DIR}/LICENSE bin/

# Create Description
create_description

# Create the zip file
zip -r -q bin bin  && echo "zip success" || echo "zip failure"
echo "Created \`bin.zip\` (upload this file to StarExec)"

# Clean up - remove bin
#rm -r bin #
