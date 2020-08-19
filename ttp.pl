#!/usr/bin/env swipl
:- initialization(main, main).

:- [tptp].

 main([TPTP, TTP | OPTS]) :-
  trace_if_debug(OPTS),
  set_prolog_flag(stack_limit, 4_294_967_296),
  pose_path(TPTP, TTP),
  true.

% main :- 
%   current_prolog_flag(argv, [_, PROVER, TPTP, TSTP, TXTX]), 
%   atom_firstchar(PROVER, PRVR),
%   set_prolog_flag(stack_limit, 2_147_483_648),
%   style_check(-singleton),
%   pose(TPTP, PIDS, PROB),
%   solve(PRVR, PIDS, TSTP, SOL),
%   open(TXTX, write, STRM, [encoding(octet)]),
%   prove(STRM, none, PRVR, SOL, PROB),
%   close(STRM).