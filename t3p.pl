#!/usr/bin/env swipl

:- initialization(main, main).

:- [basic].

main(['verify', PROB, PROOF]) :-
  writeln("verification mode not implemented yet."),
  true.

main(['compile', SOLVER, TPTP, TSTP, TESC]) :-
  set_mem_gb(14), !,
  style_check(-singleton), !,
  writeln("Fetching problem..."), !,
  tptp_prob(TPTP, PROB), !,
  write(PROB).
