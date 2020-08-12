#!/usr/bin/env swipl

:- initialization(main, main).
% :- use_module(library(shell)).

:- [basic].

mv_temp(PRVR, NAME) :- 
  atomic_list_concat([PRVR, "s/", NAME, ".tstp"], OLD),
  atomic_list_concat(["temp/", NAME, ".tstp"], NEW),
  mv(OLD, NEW). 

main([PRVR]) :- 
  get_solution_names(PRVR, X), 
  names_proven(PRVR, Y), 
  subtract(X, Y, Z), 
  length(Z, NUM),
  format("Moving ~w solutions\n", NUM), 
  maplist(mv_temp(PRVR), Z).

