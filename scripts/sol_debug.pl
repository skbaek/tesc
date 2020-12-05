#!/usr/bin/env swipl
:- initialization(main, main).

:- ['../basic.pl'].
:- ['../sol_trace.pl'].
:- ['../esolve.pl'].

main :- 
  trace, 
  debug_ctx(CTX), 
  debug_ant(ANT), 
  tup_insts(CTX, ANT, INSTS),
  writeln_list(INSTS).

