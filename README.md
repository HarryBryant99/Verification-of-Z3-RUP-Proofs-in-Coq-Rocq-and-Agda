# Verification-of-Z3-RUP-Proofs-in-Coq-Rocq-and-Agda
This git repository contains
- In 
  [agdaCode/vers1Types2025Workshop/](agdaCode/vers1Types2025Workshop/)<br>
  the Agda code used in the short article:<br>
  Harry Bryant, Andrew Lawrence, Monika Seisenberger, and Anton Setzer: Verifying Z3 RUP proofs with the interactive theorem provers Coq/Rocq and Agda, which appeared in the abstracts of TYPES 2025. [Types 2025](https://msp.cis.strath.ac.uk/types2025/), pdf at [Types Book of Abstracts](https://msp.cis.strath.ac.uk/types2025/TYPES2025-book-of-abstracts.pdf)
- In
  [agdaCode/vers1Types2025Workshop/html/](agdaCode/vers1Types2025Workshop/html/)<br>
  an html version 1 of the Agda code.<br>
  In order to view it download that directory and load from a webbrowser the file<br>
  [agdaCode/vers1Types2025Workshop/html/loadAll.html](agdaCode/vers1Types2025Workshop/html/loadAll.html) <br>
  from which you can load the respective files by clicking on the import statements.
- In
  [agdaCode/vers2/agdaCode/html](agdaCode/vers2/agdaCode/html)<br>
  an html version 2 of the Agda code which includes full SAT proof checking.<br>
  In order to view it download that directory and load from a webbrowser the file<br>
  [agdaCode/vers2/agdaCode/html/loadAll.html](agdaCode/vers2/agdaCode/html/loadAll.html)<br>
  from which you can load the respective files by clicking on the import statements.
- In
  [RailwayCaseStudy/](RailwayCaseStudy/)<br>
  an example of a railway with Z3 code for verificatoin
- In
  [agdaCode/vers2/](agdaCode/vers2/)<br>
  a checker for Z3 proofs of propositional formulas
- In
  [Rocq/vers1](Rocq/vers1) a RUP checker developed in Rocq.<br>
  This tool generates an extracted checker for formulas in CNF and a proof checker for propositional formulae. In the case of RUP, it uses the extracted RUP checker.
- In
  [Rocq/vers2](Rocq/vers2) a RUP checker developed in Rocq with a non-verified Tseitin checker.<br>
  This tool generates an extracted checker for formulas in CNF and a proof checker for propositional formulae. In the case of RUP, it uses the extracted RUP checker.
  In case of non-CNF Tseitin steps it uses an OCaml checker.
- In
  [createProofLogs/](createProofLogs/) scripts for generating the proof logs.
- In
  [OCaml/vers1](OCaml/vers1)<br>
  OCaml translation of the python code, part of the Agda version 2 code, that checks whether Tseitin steps match their revelant pattern.
- In
  [OCaml/vers2](OCaml/vers2)<br>
  Extracted Z3 SAT checker using the proven code in [Rocq/vers2](Rocq/vers2)


# Note on Operating System Used
This code has been developed using Linux
- Sometimes during the development process we had problems with files in dos format.<br>
  We haven't discovered it in the final version but it might still occur.<br>
  If it occurs try converting the files in question from dos to unix (e.g. using dos2unix) to fix the problem.
- The shell scripts in<br>
  [createProofLogs/](createProofLogs/)<br>
  are written for the bash shell of Linux.<br>
  You can either convert it to the terminal/shell/powershell
  of your operating system using tools available online
  or run the commands given in the README.txt file manually.
