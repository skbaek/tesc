#!/usr/bin/env swipl

:- initialization(main, main).
:- [misc, problems, vsolve, esolve, results].

add_entry(FILE, ENTRY) :- 
  open(FILE, append, STM),
  write_term_punct(STM, ENTRY),
  close(STM).

format_shell_time(PATTERN, ARGS, TIME, STATUS) :- 
  format(string(CMD), PATTERN, ARGS),
  goal_time(shell(CMD, STATUS), TIME), !.

format_shell(PATTERN, ARGS, STATUS) :- 
  format(string(CMD), PATTERN, ARGS),
  shell(CMD, STATUS), !.

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
  tptp_folder(TPTP),
  name_probpath(PROB, PROB_PATH),
  format(
    string(CMD),
    "vampire --output_axiom_names on --proof tptp --include ~w ~w > temp.s", 
    [TPTP, PROB_PATH]
  ).

call_solver(SOLVER, PROB) :- 
  solver_prob_cmd(SOLVER, PROB, CMD),
  goal_time(shell(CMD, _), TIME),
  solver_success_marker(SOLVER, MARKER),
  (
    any_line_path('temp.s', =(MARKER)) -> 
    format_shell("cat temp.s | sed '/\\(^%\\|^\\$\\)/d' > solutions/~w/~w.s", [SOLVER, PROB], 0), 
    size_file('temp.s', SIZE), 
    add_entry('results.pl', solution(SOLVER, PROB, passed(TIME, SIZE))),
    delete_file('temp.s')
  ;
    add_entry('results.pl', solution(SOLVER, PROB, failed)),
    delete_file('temp.s'),
    false
  ).

solvers([vampire, eprover]).

is_prefix(PFX, ATOM) :- 
  sub_atom(ATOM, 0, _, _, PFX).

select_by_prefix(PFX, ATOMS, ATOM) :- 
  include(is_prefix(PFX), ATOMS, [ATOM]).
  
select_arg(IDENT, ARGS, ARG) :- append(_, [IDENT, ARG | _], ARGS).

args_size(ARGS, SIZE) :- 
  select_arg('--size', ARGS, ARG), 
  atom_number(ARG, SIZE).

args_solver(ARGS, SOLVER) :- 
  append(_, ['--solver', SOLVER_ARG | _], ARGS), 
  solvers(SOLVERS), 
  select_by_prefix(SOLVER_ARG, SOLVERS, SOLVER), !.

args_drop_take(ARGS, DROP, TAKE) :- 
  append(_, ['--slice', DROP_ATOM, TAKE_ATOM | _], ARGS), 
  atom_number(DROP_ATOM, DROP),
  atom_number(TAKE_ATOM, TAKE), !.

args_outpath(ARGS, OUTPATH) :-
  append(_, ['-o', OUTPATH | _], ARGS), !. 

goal_time(GOAL, TIME) :- 
  statistics(walltime, [START | _]),
  call(GOAL),
  statistics(walltime, [END | _]),
  TIME is END - START.

bench(_, _, _, _, []).
bench(GOAL, TIME, PASSED, TRIED, [ELEM | LIST]) :- 
  format("Solving problem = ~w\n", [ELEM]), !, 
  ( 
    goal_time(call(GOAL, ELEM), ADD_TIME) ->
    num_succ(PASSED, NEW_PASSED),
    NEW_TIME is TIME + ADD_TIME 
  ; 
    NEW_PASSED = PASSED,
    NEW_TIME = TIME
  ), !,
  num_succ(TRIED, NEW_TRIED), 
  format("PASSED/TRIED = ~w/~w\n", [NEW_PASSED, NEW_TRIED]),
  format("CUMULATIVE TIME (ms) = ~w\n", [NEW_TIME]), !,
  bench(GOAL, NEW_TIME, NEW_PASSED, NEW_TRIED, LIST).

solution_result_exists(SOLVER, PROB) :- solution(SOLVER, PROB, _), !.

main(ARGS) :- 
  args_size(ARGS, SIZE),
  args_solver(ARGS, SOLVER),
  findall(PROB, applicable(PROB), ALL), !,
  format("Solver = ~w\n", SOLVER),
  exclude(solution_result_exists(SOLVER), ALL, TEMP),
  take_upto(SIZE, TEMP, PROBS),

  format("Problems = ~w\n", SOLVER),
  writeln_list(PROBS),
  bench(call_solver(SOLVER), 0, 0, 0, PROBS), 
  true.