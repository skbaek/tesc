#!/usr/bin/env swipl
:- initialization(main, main).
:- [prelude, common, proofs].

check_name(SOLVER, KERNEL, NAME) :- 
  format("Checking problem = ~w\n", [NAME]), !,
  name_probpath(NAME, PROB_PATH),
  format(string(CMD), "$TESC/t3p verify --kernel ~w ~w proofs/~w/~w.tesc", [KERNEL, PROB_PATH, SOLVER, NAME]), !,
  (
    goal_time(shell(CMD, 0), TIME) ->
    add_entry('verifications.pl', verification(SOLVER, KERNEL, NAME, TIME))
  ;
    add_entry('verifications.pl', verification(SOLVER, KERNEL, NAME, failed))
  ).

main([SOLVER, KERNEL]) :- 
  findall(NAME, proof(SOLVER, NAME, passed(_, _)), NAMES), !,
  cmap(check_name(SOLVER, KERNEL), NAMES), !.

main([]) :- 
  shell("echo \"\" > verifications.pl", 0),
  main([vampire,fast]),
  main([vampire,verified]),
  main([eprover,fast]),
  main([eprover,verified]).