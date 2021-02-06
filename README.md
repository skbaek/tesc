# The TESC proof format & T3P tool for first-order ATPs

Theory-Extensible Sequent Calculus (TESC) is a low-level, mechanically
checkable proof format for first-order ATPs. Simple independent verifiers 
can check an input pair of a TPTP problem and a TESC proof, using the 
latter to verify that the former is unsatisfiable.

You can generate TESC proof files by compiling them from TSTP solution files
using the TPTP-TSTP-TESC Processor (T3P) tool. T3P can also verify TESC proofs
using one of three backend checkers: a formally verified checker written and
verified in Agda, a performance-optimized checker written in Rust, and a 
debugging/backup checker written in Prolog.

## Installation & Usage 

T3P can be compiled using `make`. The following programs and variables 
should be available on the path for successful compilation and usage:

- [swipl](https://www.swi-prolog.org/) for compiling the main T3P script.
- [cargo](https://github.com/rust-lang/cargo#compiling-from-source) (with
  [Rust](https://www.rust-lang.org/)) for compilation of the TPTP parser 
  and optimized TESC verifier.
- [agda](https://github.com/agda/agda) 
  (with its [standard library](https://github.com/agda/agda-stdlib)) 
  for compiling the verified TESC verifier.
  You may need to use the [exact version](https://github.com/agda/agda-stdlib/commit/9c56155ffdc1930b6c33caa38ef384ab8cc2dba1) 
  of the standard library for correct compilation.
- [cadical](https://github.com/arminbiere/cadical) and 
  [drat-trim](https://github.com/marijnheule/drat-trim) for 
  handling AVATAR steps used in Vampire's TSTP solutions.
- Environment variables `$TPTP` and `$TESC` should be set to the TPTP and 
  TESC directory paths, respectively. 

Installation and usage was only tested on Linux.

`t3p compile [SOLVER] [PROBLEM] [SOLUTION] [PROOF]` compiles a TPTP problem 
`[PROBLEM]` and its TSTP solution `[SOLUTION]` to a new TESC proof `[PROOF]`, 
where `[SOLVER]` is the ATP used to generate `[SOLUTION]`. Currently supported 
options for `[SOLVER]` are `vampire` and `eprover`.

`t3p verify [VERIFIER] [PROBLEM] [PROOF]` uses the TESC proof `[PROOF]` 
to check that the TPTP problem `[PROBLEM]` is unsatisfiable. Currently
supported options for `[VERIFIER]` are `vtv`,  `otv`, and `dtv` for the 
Agda, Rust, and Prolog verifiers, respectively. `[VERIFIER]` may be 
omitted, in which case T3P default `otv`.