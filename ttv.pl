#!/usr/bin/env swipl
:- initialization(main, main).

:- [check].
  
main([TPTP, TESC]) :-
  set_prolog_flag(stack_limit, 4_294_967_296),
  check_debug(TPTP, TESC).

% main :- 
%   current_prolog_flag(argv, [_, TPTP, TESC]), 
%   check(TPTP, TESC).
