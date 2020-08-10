#!/usr/bin/env swipl
:- initialization(main, main).

:- [check].
  
main([TPTP, TESC | OPTS]) :-
  set_prolog_flag(stack_limit, 4_294_967_296),
  trace_if_debug(OPTS),
  check_term(TPTP, TESC).