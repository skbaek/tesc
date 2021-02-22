#!/usr/bin/env swipl
:- initialization(main, main).
:- ['$HOME/scripts/prelude', solutions, proofs, verifications].

proven_names(SOLVER,NAMES) :-
  findall(NAME, proof(SOLVER, NAME, passed(_, _)), NAMES). 

solution_time(SOLVER,TIME) :- 
  proven_names(SOLVER,NAMES), 
  fa_elem_cut([NAME, TIME]>>(solution(SOLVER, NAME, passed(TIME,_))), NAMES, TIMES), 
  sum_list(TIMES,TIME).

get_sol_size(SOLVER, NAME, SIZE) :- 
  format(string(STR), "$ITP/solutions/~w/~w.s", [SOLVER, NAME]),
  expand_file_name(STR, [FILE]),
  size_file(FILE, SIZE).

solutions_size(SOLVER, SIZE) :-   
  proven_names(SOLVER, NAMES), 
  fa_elem_cut(get_sol_size(SOLVER), NAMES, SIZES), 
  sum_list(SIZES, SIZE).

% solutions_size(SOLVER, SIZE) :-   
%   proven_names(SOLVER, NAMES), 
%   fa_elem_cut([NAME, SIZE]>>(solution(SOLVER, NAME, passed(_, SIZE))), NAMES, SIZES), 
%   sum_list(SIZES, SIZE).

proof_time(SOLVER,TIME) :- 
  proven_names(SOLVER,NAMES), 
  fa_elem_cut([NAME, TIME]>>(proof(SOLVER, NAME, passed(TIME,_))), NAMES, TIMES), 
  sum_list(TIMES,TIME).

proofs_size(SOLVER, SIZE) :- 
  proven_names(SOLVER, NAMES), 
  fa_elem_cut([NAME, SIZE]>>(proof(SOLVER, NAME, passed(_, SIZE))), NAMES, SIZES), 
  sum_list(SIZES, SIZE).

verif_time(SOLVER,TIME) :- 
  proven_names(SOLVER,NAMES), 
  fa_elem_cut([NAME, TIME]>>(verification(SOLVER, otv, NAME, passed(TIME,_))), NAMES, TIMES), 
  sum_list(TIMES,TIME).

main([SOLVER]) :- 
  solutions_size(SOLVER, SSIZE),
  proofs_size(SOLVER, PSIZE),
  % proof_time(SOLVER, PTIME),
  % verif_time(SOLVER, VTIME),
  format("Solutions size for ~w = ~w\n", [SOLVER, SSIZE]),
  format("Proofs size for ~w = ~w\n", [SOLVER, PSIZE]),
  % format("Compilation time for ~w = ~w\n", [SOLVER, PTIME]),
  % format("Verification time for ~w = ~w\n", [SOLVER, VTIME]),
  PS is PSIZE / SSIZE,
  % VS is VTIME / STIME,
  format("PRF / SOL = ~w\n", PS).
  % format("VERIF / SOL = ~w\n", VS).