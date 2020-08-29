#!/usr/bin/env swipl
:- initialization(main, main).

:- [check].
  
main([TPTP, TESC | OPTS]) :-
  trace_if_debug(OPTS),
  set_prolog_flag(stack_limit, 4_294_967_296),
  check_strm(TPTP, TESC),
  write("Proof verified.\n"),
  true.

% % main :-
% %   current_prolog_flag(argv, [_, TPTP, TESC | OPTS]), 
% main([TPTP, TESC | OPTS]) :-
%   trace_if_debug(OPTS),
%   set_prolog_flag(stack_limit, 4_294_967_296),
%   check_strm(TPTP, TESC),
%   true.
