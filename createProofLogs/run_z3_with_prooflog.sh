#!/bin/bash

# Usage
# run_z3_with_proof.sh input.smt2
#
# which creates as outpu
#     input-prooflogaux.smt2 and input-prooflog.txt

# Check for correct number of arguments
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <input_file.smt2>"
    exit 1
fi

INPUT_FILE="$1"
BASENAME="${INPUT_FILE%.smt2}"
PROOF_LOG_AUX="${BASENAME}-prooflogaux.smt2"
PROOF_LOG="${BASENAME}-prooflog.txt"

echo rm $PROOF_LOG_AUX
rm $PROOF_LOG_AUX
echo rm $PROOF_LOG
rm $PROOF_LOG

echo z3 $INPUT_FILE sat.euf=true tactic.default_tactic=smt solver.proof.log=$PROOF_LOG_AUX
z3 $INPUT_FILE sat.euf=true tactic.default_tactic=smt solver.proof.log=$PROOF_LOG_AUX

python3 check_proof.py $PROOF_LOG_AUX >> $PROOF_LOG
