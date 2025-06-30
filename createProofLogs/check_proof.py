import sys
from z3 import *

# usage
# python3 check_proof.py anton_prooflogaux.smt2


if len(sys.argv) != 2:
    print("Usage: python3 check_proof.py <proof_file.smt2>")
    sys.exit(1)

proof_file = sys.argv[1]

set_param("solver.proof.check", True)
s = Solver()
onc = OnClause(s, print)
s.from_file(proof_file)
