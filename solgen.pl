#!/usr/bin/env swipl

:- initialization(main, main).
:- [misc, problems].

gen_sol(SVR, NAME) :- 
  format("Solving problen = ~w\n", NAME), 
  name_probpath(NAME, PROB_PATH),
  name_solpath(SVR, NAME, SOL_PATH), !,
  call_solver(SVR, PROB_PATH, SOL_PATH), !.

random_select_num(0, _, []) :- !.
random_select_num(NUM, LIST, [SEL | SELS]) :- 
  random_select(SEL, LIST, TEMP), 
  num_pred(NUM, PRE),
  random_select_num(PRE, TEMP, SELS).

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

% main([SOLVER]) :-
%   atom_firstchar(SOLVER, SVR),
%   findall(PROB, target(PROB), ALL),
%   random_select_num(100, ALL, SEL),
%   length(SEL, LTH),
%   format("Total number of selected problems = ~w\n", LTH), 
%   writeln_list(SEL),
%   maplist_count(gen_sol(SVR), 0, 0, SEL, CNT, TTL), 
%   format("SOLVED/TOTAL = ~w/~w\n", [CNT, TTL]),
%   true.