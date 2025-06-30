# Verification-of-Z3-RUP-Proofs-in-Coq-Rocq-and-Agda
This git repository contains
- In
  [link](agdaCode/vers1Types2025Workshop/)
  the Agda code used in the short article:
  Harry Bryant, Andrew Lawrence, Monika Seisenberger, and Anton Setzer: Verifying Z3 RUP proofs with the interactive theorem provers Coq/Rocq and Agda, which appeared in the abstracts of TYPES 2025. [Types 2025](https://msp.cis.strath.ac.uk/types2025/)
- In
  [link](agdaCode/vers1Types2025Workshop/html/)
  an html version of the Agda code
  In order to view it download that directory and load from a webbrowser the file
  [link](agdaCode/vers1Types2025Workshop/html/loadAll.html)
  which loads the respective agda files
- In
  [link](RailwayCaseStudy/)
  an example of a railway with Z3 code for verificatoin
- In
  [link](agdaCode/vers2/)
  a checker for Z3 proofs of propositional formulas
- In
  [link](Rocq/) a RUP checker developed in Rocq is given.
  This creates an extracted checker for formulas in CNF and a checker which checks proofs with propositional formulae,
  and uses in case of Rup the extracted Rup checker.
- In
  [link](createProofLogs/) scripts for creating the prooflogs are given.

# Note on use of operating system
This code has been developed using Linux
- Sometimes during the development process we had problems with files in dos format.
  We haven't discovered it in the final version but it might still occur.
  If it occurs converting a file from dos to unix (e.g. using dos2unix) can fix that problem.
- The shell scripts in
  [link](createProofLogs/)
  is for the bash shell of Linux.
  You can either convert it to the termainl/shell/powershell
  of your operating system using tools available online,
  or run the commands given in the README.txt file manually.
