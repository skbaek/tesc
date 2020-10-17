#!/usr/bin/env swipl

:- initialization(main, main).
:- consult("../tesc/vsolve.pl").
:- consult("../tesc/esolve.pl").
:- [misc, problems].
% :- consult("../tesc/solve.pl").
% :- consult("../tesc/solve.pl").
% :- consult("../tescn_list(NAMES),

gen_sol(SVR, NAME) :- 
  format("Solving problen = ~w\n", NAME), 
  name_probpath(NAME, PROB_PATH),
  name_solpath(SVR, NAME, SOL_PATH), !,
  call_solver(SVR, PROB_PATH, SOL_PATH), !.

main([SOLVER, NUM_ATOM | OPTS]) :- 
  trace_if_debug(OPTS),
  atom_firstchar(SOLVER, SVR),
  findall(PROB, applicable(PROB), ALL),
%   get_problem_names(ALL),
  length(ALL, LTH),
  format("Total number of applicable problems = ~w\n", LTH), 
  atom_number(NUM_ATOM, NUM),
  random_n(NUM, ALL, PROBS),
  writeln_list(PROBS),
  maplist_count(gen_sol(SVR), 0, 0, PROBS, CNT, TTL), 
  format("SOLVED/TOTAL = ~w/~w\n", [CNT, TTL]).
%   names_archived(PRVR, NAS),
%   length(NAS, NAS_NUM),
%   format("- Number of archived problems = ~w\n", NAS_NUM), 
%   names_failed(PRVR, NFS),
%   length(NFS, NFS_NUM),
%   format("- Number of failed problems = ~w\n", NFS_NUM), 
%   subtract(ALL, NAS, TEMP),
%   subtract(TEMP, NFS, NEW),
%   write("---------------------------------------\n"),
%   length(NEW, NEW_NUM),
%   format("Number of unattempted problems = ~w\n", NEW_NUM),
%   (
%     member('-count', OPTS) -> 
%     true
%   ;
%     msg("Enter solution genaration loop"),
%     gen_sols(PRVR, NUM, NEW), 
%     msg("Exit solution generation loop")
%   ).
