


The Problem Set

The TESC toolchain is designed to work with TPTP input problems in the FOF and CNF language. 
In the TPTP problem library, there are 13191 problems in the FOF/CNF language that have 
theorem/unsatisfiable status. Out of these problems, the TESC toolchain rejects 23 problems 
(more specifically, the LCL-domain problems that use the 'substitution_of_equivalents' axiom)
due to non-unique formula names. I think it is reasonable to require that every formula in 
an input problem should have a unique name, so that solutions and proofs can unambiguously 
indicate the formulas used in each step. The remaining 13168 problems are the problem set
used for this test, and their full list can be found in problems.txt.


Vampire Test Results

Using the problem set, Vampire successfully produced TSTP solutions for 7935 problems. 
4 of those solutions contained what I believe to be errors, so tests were carried out
using the remaining 7931 solutions. The full list of Vampire solutions can be found in 
vsol.txt.  


