#!/usr/bin/env swipl
:- initialization(main, main).

:- [basic, esolve, sol_trace].

main :- 
  debug_ctx(CTX), 
  debug_ant(ANT), 
  guitracer,
  trace, 
  tup_insts(CTX, ANT, INSTS),
  write_list(INSTS).

