Rup_verification.v
~~~~~~~~~~~~~~~~~~~~
   is Rocq code which has a rup checker and a checker for proofs
   having rup rule and assertions only
   Proofs from formulas in CNF are usually of this form.

RupProofChecker.ml RupProofChecker.mli
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
were extracted from Rup_verification.v using Rocq

Compilation
~~~~~~~~~~~~
ocamlc -o parserFull RupProofChecker.ml parserFullProofsWithExtractedRupChecker.ml
ocamlc -o parserCNF RupProofChecker.ml parserCNFfullyExtractedFromRocq.ml


Examples
~~~~~~~~~
exampleCNF1.smt2
exampleCNF2.smt2
exampleUsingTseitin.smt2
are 3 examples
the following
  exampleCNF1.smt2
  exampleCNF2.smt2
are in CNF
exampleUsingTseitin.smt2
is not in CNF

The files
exampleCNF1-prooflogaux.smt2
exampleCNF1-prooflog.txt
exampleCNF2-prooflogaux.smt2
exampleCNF2-prooflog.txt
exampleUsingTseitin-prooflogaux.smt2
exampleUsingTseitin-prooflog.txt
were the proof logs created by Z3


Execution
~~~~~~~~~
parserCNF file-prooflog.txt
for the CNF parser

parserFull file-prooflog.txt
for the Full parser
where file-prooflog.txt
is the prooflog obtained from a file.smt2


Results of checking examples
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
parserCNF exampleUsingTseitin-prooflog.txt
    fails because of use of Tseitin
          the parser supports only CNF at the moment
parserCNF exampleCNF1-prooflog.txt
parserCNF exampleCNF2-prooflog.txt
     both succeeds

parserFull exampleUsingTseitin-prooflog.txt
parserFull exampleCNF1-prooflog.txt
parserFull exampleCNF2-prooflog.txt
     all three succeed
