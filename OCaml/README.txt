OCaml Tseitin Checker
~~~~~~~~~~~~~~~~~~~~~
  OCaml translation of the python code, part of the Agda version 2 code, that checks 
  whether Tseitin steps match their revelant pattern.

  Note: The current implementation does not approve optimised tseitin steps where 
  the conclusion is a subset of the antecedent because one or more of the literals 
  in the antecedent is already false by an exciting unit clause.

Example
~~~~~~~
An example is the smt2 file
example.smt2
from which the prooflogs
example-prooflog.txt
example-prooflogaux.smt2
were generated
