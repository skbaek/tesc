#!/usr/bin/env swipl
:- initialization(main, main).

:- [basic].
:- [vsolve, esolve].
:- [prove].

solve(e, TSTP, SOL) :- esolve(TSTP, SOL).
solve(v, TSTP, SOL) :- vsolve(TSTP, SOL).% main :- 

%   current_prolog_flag(argv, [_, PROVER, TPTP, TSTP, TESC | OPTS]), 
main([PROVER, TPTP, TSTP, TESC | OPTS]) :-
  trace_if_debug(OPTS),
  set_prolog_flag(stack_limit, 4_294_967_296),
  style_check(-singleton),
  atom_firstchar(PROVER, PRVR),
  tptp_prob(TPTP, PROB), !,
  solve(PRVR, TSTP, SOL), !,
  open(TESC, write, STRM, [encoding(octet)]),
  empty_assoc(EMP),
  prove((EMP, SOL, PROB, STRM, PRVR, nil), 0),
  close(STRM).
