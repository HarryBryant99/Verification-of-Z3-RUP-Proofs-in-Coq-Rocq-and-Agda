#!/bin/bash

# Usage:
# ./run_z3_with_prooflog-standalone.sh input.smt2
# This creates:
#   input-prooflogaux.smt2
#   input-prooflog.txt

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

# Run Z3 and generate the proof log
echo "Running Z3 on $INPUT_FILE..."
z3 "$INPUT_FILE" sat.euf=true tactic.default_tactic=smt solver.proof.log="$PROOF_LOG_AUX"

# Run embedded Python to check the proof and append output to log
echo "Checking proof with embedded Python..."
python3 - "$PROOF_LOG_AUX" >> "$PROOF_LOG" <<EOF
import sys
from z3 import *

if len(sys.argv) != 2:
    print("Usage: python3 <script> <proof_file.smt2>")
    sys.exit(1)

proof_file = sys.argv[1]
set_param("solver.proof.check", True)
s = Solver()
onc = OnClause(s, print)
s.from_file(proof_file)
EOF

echo "Done. Proof log saved to $PROOF_LOG"
