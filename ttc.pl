#!/usr/bin/env swipl
:- initialization(main, main).

:- [basic].
:- [vsolve, esolve].
:- [prove].

solve(e, TSTP, SOL) :- esolve(TSTP, SOL).
solve(v, TSTP, SOL) :- vsolve(TSTP, SOL).

main([SOLVER, TPTP, TSTP, TESC | OPTS]) :-
  trace_if_debug(OPTS),
  inc_mem, 
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
