#!/usr/bin/env swipl
:- initialization(main, main).

:- consult('../tesc/basic.pl').
:- consult('../tesc/sol_trace.pl').
:- consult('../tesc/esolve.pl').

main :- 
  guitracer,
  trace, 
  debug_ctx(CTX), 
  debug_ant(ANT), 
  tup_insts(CTX, ANT, INSTS),
  write_list(INSTS).

