#!/usr/bin/env swipl
:- initialization(main, main).

:- [basic].
:- [tptp].
:- [solve].
:- [prove].


main([PROVER, TPTP, TSTP, TESC]) :-
  set_prolog_flag(stack_limit, 4_294_967_296),
  style_check(-singleton),
  prover_abrv(PROVER, PRVR),
  write("Posing...\n\n"),
  pose(verbose, TPTP, OHYPS, OCLAS, PROB), !,
  write("Solving...\n\n"),
  solve(PRVR, TSTP, SOL), !,
  open(TESC, write, STRM, [encoding(octet)]),
  write("Proving...\n\n"),
  prove((PROB, SOL, _, 0, STRM, PRVR, OHYPS, OCLAS, nil)),
  close(STRM),
  true.

% main :- 
%   current_prolog_flag(argv, [_, PROVER, TPTP, TSTP, TXTX]), 
%   prover_abrv(PROVER, PRVR),
%   set_prolog_flag(stack_limit, 2_147_483_648),
%   style_check(-singleton),
%   pose(TPTP, PIDS, PROB),
%   solve(PRVR, PIDS, TSTP, SOL),
%   open(TXTX, write, STRM, [encoding(octet)]),
%   prove(STRM, none, PRVR, SOL, PROB),
%   close(STRM).