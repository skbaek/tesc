#!/usr/bin/env swipl

:- initialization(main, main).
:- [prelude, common, problems, solutions, proofs].

call_prover(SOLVER, NAME) :-
  name_probpath(NAME, PROB), 
  name_solpath(SOLVER, NAME, SOL), 
  name_prfpath(SOLVER, NAME, PRF), 
  format(string(CMD), "$TESC/t3p compile ~w ~w ~w ~w", [SOLVER, PROB, SOL, PRF]), 
  format("Using command = ~w\n", [CMD]), !,
  ( 
    goal_time(shell(CMD, 0), TIME) ->
    expand_file_name(PRF, [EXP_PRF]),
    size_file(EXP_PRF, SIZE), 
    add_entry('proofs.pl', proof(SOLVER, NAME, passed(TIME, SIZE)))
  ;
    add_entry('proofs.pl', proof(SOLVER, NAME, failed))
  ).

proof_result_exists(SOLVER, PROB) :- proof(SOLVER, PROB, _), !.

main([SOLVER, SIZE_ATOM]) :- 
  atom_number(SIZE_ATOM, SIZE),
  member(SOLVER, [vampire, eprover]), !,
  format("Solver = ~w\n", SOLVER), !,
  findall(PROB, solution(SOLVER, PROB, passed(_, _)), ALL), !,
  writeln("Excluding..."), !,
  exclude(proof_result_exists(SOLVER), ALL, TEMP), !,
  take_upto(SIZE, TEMP, PROBS), !,
  write("Problems =\n"), !,
  write_list(PROBS), !,
  cmap(call_prover(SOLVER), PROBS), !,
  true.