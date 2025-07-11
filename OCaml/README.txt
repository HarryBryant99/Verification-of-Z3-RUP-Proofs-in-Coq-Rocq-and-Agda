OCaml Tseitin Checker
~~~~~~~~~~~~~~~~~~~~~
  OCaml translation of the python code, part of the Agda version 2 code, that checks 
  whether Tseitin steps match their revelant pattern.

  Note: The current implementation does not approve optimised tseitin steps where 
  the conclusion is a subset of the antecedent because one or more of the literals 
  in the antecedent is already false by an exciting unit clause.
