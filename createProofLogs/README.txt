This directory contains Linux bash scripts for creating the proof log for Z3
in the new format.
Below there are instructions what to do if using other operating systems.

There are two versions
  run_z3_with_prooflog.sh
     uses python script check_proof.py
  run_z3_with_prooflog-standalone.sh
     has the check_proof.py hardcoded.

Execute:

run_z3_with_prooflog.sh <file>.smt2
or
run_z3_with_prooflog-standalone.sh <file>.smt2

which creates from
  <file>.smt2
files
  <file>-prooflog.txt
  <file>-prooflogaux.smt2

<file>-prooflogaux.smt2 is a general proof log
<file>-prooflog.txt
is the one used in this repository for proof checking using Rocq and Agda

An example is
example.smt2
from which
example-prooflog.txt
example-prooflogaux.smt2
were created.


Adaption to other operating systems.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For other operating system it might be possible to automatically
translate the shell script into a script for your shell/powershell/terminal
using tools available online.

You cdan as well execute manually

z3 <file.smt2 sat.euf=true tactic.default_tactic=smt solver.proof.log=<file>-prooflogaux.smt2
python check_proof.py <file>_prooflogaux.smt2 >> <file>-prooflog.txt

With the >> command in python replaced by whatever you use to convert the output into
a file <file>-prooflog.txt
