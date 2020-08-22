#!/usr/bin/env swipl
:- initialization(main, main).

:- [basic].
:- [tptp].
:- [solve].
:- [prove].

main([PROVER, TPTP, TSTP, TESC | OPTS]) :-
% main :- 
%   current_prolog_flag(argv, [_, PROVER, TPTP, TSTP, TESC | OPTS]), 
  (
    member('-debug', OPTS) -> 
    guitracer,
    trace 
  ;
    true 
  ),
  set_prolog_flag(stack_limit, 4_294_967_296),
  style_check(-singleton),
  atom_firstchar(PROVER, PRVR),
  pose(verbose, TPTP, OHYPS, OCLAS, PROB), !,
  solve(PRVR, TSTP, SOL), !,
  open(TESC, write, STRM, [encoding(octet)]),
  prove((PROB, SOL, _, STRM, PRVR, OHYPS, OCLAS, nil), 0),
  close(STRM),
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