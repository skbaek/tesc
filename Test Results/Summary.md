The Problem Set

The TESC toolchain is designed to generate and verify proofs for TPTP problems in 
first-order logic with equality. More specifically, it works with problems in the 
FOF/CNF language with theorem/unsatisfiable status. In the TPTP-v7.3.0 problem library,
there are 13191 such problems. Out of these problems, the TESC toolchain rejects 
116 problems as invalid input due to non-unique formula names. (Almost all of the duplicates
are from the LCL domain, and are caused by the use of the `substitution_of_equivalents` axiom.
I believe it is reasonable to require unique formula names since the issue can be easily 
fixed, and allowing duplicates makes it significantly more difficult to unambiguously
refer to hypotheses in the context. But this point is debatable.) The remaining 13075
problems form the problem set used for the following tests.




E Test Results

Out of the 13075 problems in the problem set, E produced TSTP solutions for 4887 problems. 
TTC compiled 4519 E-produced TSTP solutions to TESC proofs, with a success rate of 92.47%.
All of the TESC proofs were succefully verified with TTV. The breakdown of compilation 
failure patterns are as follows:

- Timeouts in the 'solution phase', in which TTC tries to guess the intermediate formulas 
in chains of inferences, caused an overwhelming majority (283 problems) of compilation failures.
Almost all of them involved long chains of `rw` steps, where the number of candidate
intermediate formulas can quickly explode depending on the position and direction of
rewriting. Breaking down the length of `rw`-chains will have the single largest impact
on increasing the compilation success rate for E.

- Of the 85 remaining failures, most (63 problems) were caused by 'axiom steps', where TTC tries 
to verify that each axiom used in a TSTP solution is actually present in the original TPTP problem.
These steps would be trivial if either (1) the original name of the axiom (which it had in the 
TPTP problem), were

or 

(2) retained the axiom in the exact form as it appears in the TPTP problem. When neither holds, 
axiom steps can be occasionally quite demanding.




Timeouts from reconstruction of large AVATAR steps was the leading cause (26 problems) of 
compilation failures. Unless Vampire can be modified to use smaller AVATAR steps, there 
does not seem to be an good remedy for these cases, other than optimization of TTC itself.




Vampire Test Results

Out of the 13075 problems in the problem set, Vampire produced TSTP solutions for 7882 problems. 
4 of those solutions contained what I believe to be errors, and were excluded. The remaining 7878 
problems were used for testing the TESC toolchain. TTC successfully compiled 7815 Vampire-produced 
TSTP solutions to TESC proofs, with a success rate of 99.20%. All of the TESC proofs were 
succefully verified with TTV. The breakdown of compilation failure patterns are as follows:

- Timeouts from reconstruction of large AVATAR steps was the leading cause (26 problems) of 
compilation failures. Unless Vampire can be modified to use smaller AVATAR steps, there 
does not seem to be an good remedy for these cases, other than optimization of TTC itself.

- The axiom steps, where TTC tries to verify that each axiom used in a TSTP solution is actually 
present in the original TPTP problem, accounted for 6 failures. These steps would be trivial if 
either Vampire (1) provided the the original name which the axiom had in the TPTP problem, or 
(2) retained the axiom in the exact form as it appears in the TPTP problem. When neither holds, 
axiom steps can be occasionally quite demanding.

- Skolemization steps also caused 6 compilation failures. Again, the problem is small changes 
in formula structures: when the premise is rewritten using the choice axiom instances provided,
there is slight difference between the result of rewriting and the desired conclusion, e.g., a
permutation in the quantifier order. 

- There are a number of other inferences (pure predicate removal, avatar split clause, etc.) 
that caused 3 or less compilation failures, but they do not seem worth prioritizing at the moment.



- 











using the remaining 7931 solutions. The full list of Vampire solutions can be found in 
vsol.txt.  


