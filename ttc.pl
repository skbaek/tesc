#!/usr/bin/env swipl
:- initialization(main, main).

:- [prove, solve].

main([PROVER, TPTP, TSTP, TXTX]) :-  
  abrv_prover(PROVER, PRVR),
  set_prolog_flag(stack_limit, 2_147_483_648),
  style_check(-singleton),
  pose(TPTP, PIDS, PROB),
  solve(PRVR, PIDS, TSTP, SOL),
  open(TXTX, write, STRM, [encoding(octet)]),
  prove(STRM, none, PRVR, SOL, PROB),
  close(STRM).

% main :- 
%   current_prolog_flag(argv, [_, PROVER, TPTP, TSTP, TXTX]), 
%   abrv_prover(PROVER, PRVR),
%   set_prolog_flag(stack_limit, 2_147_483_648),
%   style_check(-singleton),
%   pose(TPTP, PIDS, PROB),
%   solve(PRVR, PIDS, TSTP, SOL),
%   open(TXTX, write, STRM, [encoding(octet)]),
%   prove(STRM, none, PRVR, SOL, PROB),
%   close(STRM).