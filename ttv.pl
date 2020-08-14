% #!/usr/bin/env swipl
% :- initialization(main, main).

:- [check].
  
% main([TPTP, TESC | OPTS]) :-
main :-
  current_prolog_flag(argv, [_, TPTP, TESC | OPTS]), 
  set_prolog_flag(stack_limit, 4_294_967_296),
  trace_if_debug(OPTS),
  check_strm(TPTP, TESC),
  write("Proof verified.\n").