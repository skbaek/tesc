#!/usr/bin/env swipl

:- initialization(main, main).

:- [prove].

main([PRVR, TPTP, TSTP, TXTX]) :- 
  prove(PRVR, TPTP, TSTP, TXTX).