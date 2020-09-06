#!/usr/bin/env swipl
:- initialization(main, main).

:- [basic].
:- [vsolve, esolve].
:- [prove].

solve(e, TSTP, SOL) :- esolve(TSTP, SOL).
solve(v, TSTP, SOL) :- vsolve(TSTP, SOL).

% ttc(SLVR, TPTP, TSTP, TESC) :-
%   writeln("Fetching problem..."),
%   tptp_prob(TPTP, PROB), !,
%   writeln("Generating solution..."),
%   solve(SLVR, TSTP, SOL), !,
%   open(TESC, write, STRM, [encoding(octet)]),
%   empty_assoc(EMP),
%   writeln("Constructing proof..."),
%   % prove((EMP, SOL, PROB, STRM, SLVR, nil), 0),
%   prove(STRM, SLVR, PROB, SOL, EMP, 0), 
%   writeln("Proof complete."),
%   close(STRM).

% main :- 
%   current_prolog_flag(argv, [_, PROVER, TPTP, TSTP, TESC | OPTS]), 
main([SOLVER, TPTP, TSTP, TESC | OPTS]) :-
  trace_if_debug(OPTS),
  set_prolog_flag(stack_limit, 4_294_967_296),
  style_check(-singleton),
  atom_firstchar(SOLVER, SLVR),
  writeln("Fetching problem..."),
  tptp_prob(TPTP, PROB), !,
  writeln("Generating solution..."),
  solve(SLVR, TSTP, SOL), !,
  open(TESC, write, STRM, [encoding(octet)]),
  empty_assoc(EMP),
  writeln("Constructing proof..."),
  prove(STRM, SLVR, PROB, SOL, EMP, 0), 
  writeln("Proof complete."),
  close(STRM).
