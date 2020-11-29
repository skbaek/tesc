#!/usr/bin/env swipl

:- initialization(main, main).
:- [misc, problems].

gen_sol(SVR, NAME) :- 
  format("Solving problen = ~w\n", NAME), 
  name_probpath(NAME, PROB_PATH),
  name_solpath(SVR, NAME, SOL_PATH), !,
  call_solver(SVR, PROB_PATH, SOL_PATH), !.

main([SOLVER, DROP_ATOM, TAKE_ATOM | OPTS]) :- 
  trace_if_debug(OPTS),
  atom_firstchar(SOLVER, SVR),
  findall(PROB, target(PROB), ALL),
  length(ALL, LTH),
  format("Total number of applicable problems = ~w\n", LTH), 
  atom_number(DROP_ATOM, DROP),
  atom_number(TAKE_ATOM, TAKE),
  slice(DROP, TAKE, ALL, PROBS),
  writeln_list(PROBS),
  maplist_count(gen_sol(SVR), 0, 0, PROBS, CNT, TTL), 
  format("SOLVED/TOTAL = ~w/~w\n", [CNT, TTL]),
  true.