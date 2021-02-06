#!/usr/bin/env swipl

:- initialization(main, main).
:- [prelude, common, problems, solutions].

solver_success_marker(eprover, "# Proof found!").
solver_success_marker(vampire, "% Refutation found. Thanks to Tanya!").

solver_prob_cmd(eprover, PROB, CMD) :- 
  name_probpath(PROB, PROB_PATH),
  format(
    string(CMD),
    "eprover --cpu-limit=60 -p ~w > temp.s", 
    [PROB_PATH]
  ).

solver_prob_cmd(vampire, PROB, CMD) :- 
  name_probpath(PROB, PROB_PATH),
  format(
    string(CMD),
    "vampire --output_axiom_names on --proof tptp --include $TPTP ~w > temp.s", 
    [PROB_PATH]
  ).

call_solver(SOLVER, PROB) :- 
  solver_prob_cmd(SOLVER, PROB, CMD),
  goal_time(shell(CMD, _), TIME),
  solver_success_marker(SOLVER, MARKER),
  (
    any_line_path('temp.s', =(MARKER)) ->
    format_shell("cat temp.s | sed '/\\(^%\\|^#\\|^\\$\\)/d' > solutions/~w/~w.s", [SOLVER, PROB], 0),
    size_file('temp.s', SIZE), 
    add_entry('solutions.pl', solution(SOLVER, PROB, passed(TIME, SIZE))),
    delete_file('temp.s')
  ;
    add_entry('solutions.pl', solution(SOLVER, PROB, failed)),
    delete_file('temp.s'),
    false
  ).

bench(_, _, _, _, []).
bench(GOAL, TIME, PASSED, TRIED, [ELEM | LIST]) :- 
  format("Solving problem = ~w\n", [ELEM]), !, 
  ( 
    goal_time(call(GOAL, ELEM), ADD_TIME) ->
    num_suc(PASSED, NEW_PASSED),
    NEW_TIME is TIME + ADD_TIME 
  ; 
    NEW_PASSED = PASSED,
    NEW_TIME = TIME
  ), !,
  num_suc(TRIED, NEW_TRIED), 
  format("PASSED/TRIED = ~w/~w\n", [NEW_PASSED, NEW_TRIED]),
  format("CUMULATIVE TIME (ms) = ~w\n", [NEW_TIME]), !,
  bench(GOAL, NEW_TIME, NEW_PASSED, NEW_TRIED, LIST).

solution_result_exists(SOLVER, PROB) :- solution(SOLVER, PROB, _), !.

main([SOLVER, SIZE]) :- 
  member(SOLVER, [vampire, eprover]),
  findall(PROB, target(PROB), ALL), !,
  format("Solver = ~w\n", SOLVER),
  exclude(solution_result_exists(SOLVER), ALL, TEMP),
  take_upto(SIZE, TEMP, PROBS),

  write("Problems = ~w\n"),
  write_list(PROBS),
  bench(call_solver(SOLVER), 0, 0, 0, PROBS), 
  true.