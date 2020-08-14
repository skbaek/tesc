# The Problem Set

The TESC toolchain is designed to generate and verify proofs for TPTP problems in 
first-order logic with equality. More specifically, it works with problems in the 
FOF/CNF language with theorem/unsatisfiable status. In the TPTP-v7.3.0 problem library,
there are 13191 such problems. Out of these problems, the TESC toolchain rejects 
116 problems as invalid input due to non-unique formula names. (Almost all of the duplicates
are from the LCL domain, and are caused by the use of the `substitution_of_equivalents` axiom.
I believe it is reasonable to require unique formula names since the issue can be easily 
fixed, and allowing duplicates makes it significantly more difficult to unambiguously
refer to hypotheses in proofs.) The remaining 13075 problems are the problem set used in this test.
The full list of problems, annotated with their test results data, can be found in [probs.csv](https://github.com/skbaek/tesc/blob/master/Test%20Results/probs.csv).
The tarballs of all TSTP solutions and TESC proofs used in the test can also be found in the same [directory](https://github.com/skbaek/tesc/blob/master/Test%20Results/). 

# E Test Results

Out of the 13075 problems in the problem set, E produced TSTP solutions for 4887 problems. 
TTC compiled 4587 E-produced TSTP solutions to TESC proofs, with a success rate of 93.86%.
All of the TESC proofs were succefully verified with TTV. An overwhelming majority of 
compilation failures (270 out of 300) were caused by timeouts in the 'solution phase', 
where TTC tries to guess the implicit intermediate formulas in chains of inferences.
Almost all of the solution phase failures involved long chains of `rw` steps, where the 
number of candidate intermediate formulas can quickly explode depending on the position 
and direction of rewriting. Breaking down the length of `rw`-chains will have the single 
largest impact on increasing the compilation success rate for E.

# Vampire Test Results

Out of the 13075 problems in the problem set, Vampire produced TSTP solutions for 7882 problems. 
4 of those solutions were excluded as they contained (what I believe to be) errors. The remaining 
7878 problems were used for testing the TESC toolchain. TTC successfully compiled 7815 of these
TSTP solutions to TESC proofs, with a success rate of 99.20%. All of the TESC proofs were 
succefully verified with TTV. The breakdown of compilation failure patterns are as follows:

- Timeouts from reconstruction of large AVATAR steps was the leading cause (26 problems) of 
compilation failures. Unless Vampire can be modified to use smaller AVATAR steps, there 
does not seem to be an ready solution for these cases, other than optimization of TTC itself.

- The axiom steps, where TTC tries to verify that each axiom used in a TSTP solution is actually 
present in the original TPTP problem, accounted for 6 failures. These steps would be trivial if 
either Vampire (1) provided the the original name which the axiom had in the TPTP problem, or 
(2) retained the axiom in the exact form as it appears in the TPTP problem. When neither holds, 
axiom steps can be difficult in rare occasions.

- Skolemization steps also caused 6 compilation failures. Again, the problem is small changes 
in formula structures: when the premise is rewritten using the choice axiom instances provided,
there is slight difference between the result of rewriting and the desired conclusion, e.g., a
permutation in the quantifier order. 

- There are a number of other inferences (pure predicate removal, avatar split clause, etc.) 
that caused 3 or less compilation failures, but they do not seem worth prioritizing at the moment.

# Note on Versions 

The tests were performed using TPTP-v7.3.0 problem library, 
E 2.4 Sandakphu (1fa8840d748f8781007680abbfdab27e96fa5648), and
Vampire 4.4.0 (commit d98a3d53 on 2020-01-14 21:02:12 +0100), 
all of which are now outdated.  
