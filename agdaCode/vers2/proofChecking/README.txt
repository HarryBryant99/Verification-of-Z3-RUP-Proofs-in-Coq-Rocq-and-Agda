Checking of a proof log
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Requirements:
   you need to have Agda and the standard library installed
     we are using Agda vers 2.7.0.1
     and standard library agda-stdlib-2.1.1
   you need to have added the agda-lib file
      agda-stdlib-2.1.1/standard-library.agda-lib
        from the standard library
      and
     ../agdaCode/rup.agda-lib
     as absolute paths to
   ~/.agda/libraries
    and
    standard-library-2.1.1
   to
   ~/.agda/defaults

Assume a proof log <file>-prooflog.txt
created from a Z3 file  <file>.smt2

Execute (you might need to replace python by your version of it
  e.g. python3)
python createAgdaCheckFileZ3.py <file>-prooflog.txt

This parses a proof output, and creates a file
<file>-proofCheck.agda

That agda file contains a parsed version of the proof log
in a format suitable for agda and at the end commands for extracting the
assumptions, conclusions, and checking the proof.

To check that the proof is a correct proof from assumptions to conclusions
  evaluate using C-c C-n
      checkProof
To check that the proof is a correct proof of usatisfiability
  evaluate using C-c C-n
      checkProofUnSat
To obtain the assumptions and conclusions used
   evaluate the corresponding variables.
If
   checkProofUnSat = true
then

UnSatCurrentProof tt : UnSat (ZProof2Assumption currentProof)

However don't evaluate it to normal form, that might be too big.
But you can use it as a proof of the underlying Sat problem

Example
~~~~~~~
An example is  the smt2 file
example.smt2
from which the prooflogs
example-prooflog.txt
example-prooflogaux.smt2
were generated
and then by using

python createAgdaCheckFileZ3.py example-prooflog.txt
the file
example-proofCheck.agda
was obtained
