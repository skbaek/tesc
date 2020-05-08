#!/usr/bin/env swipl

:- initialization(main, main).

:- [check].
  
main([TPTP, TESC]) :- check(TPTP, TESC).