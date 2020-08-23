#!/usr/bin/env swipl
:- initialization(main, main).

:- [check].
  
main([TPTP, TESC | OPTS]) :-
  trace_if_debug(OPTS),
  pose_path(TPTP, 'temp.ttp'),
  write("Conversion complete.\n"),
  concat_shell(["./rttv ", TESC], RST),
  format("Verification result = ~w\n", RST),
  true.

% % main :-
% %   current_prolog_flag(argv, [_, TPTP, TESC | OPTS]), 
% main([TPTP, TESC | OPTS]) :-
%   trace_if_debug(OPTS),
%   set_prolog_flag(stack_limit, 4_294_967_296),
%   check_strm(TPTP, TESC),
%   true.
