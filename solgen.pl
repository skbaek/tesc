#!/usr/bin/env swipl

:- initialization(main, main).
:- [solve, prove, check, probsel].

is_fol_prob(PATH) :- 
  \+ sub_string(PATH, _, _, _, "="),
  \+ sub_string(PATH, _, _, _, "^"), 
  \+ sub_string(PATH, _, _, _, "_"), 
  string_concat(_, ".p", PATH).

e_check(STRM) :- 
  read_line_to_string(STRM, LINE), 
  (
    LINE = "# Proof found!" -> true  
  ;
    LINE = end_of_file -> false  
  ;
    e_check(STRM) 
  ).
  
call_prover(e, TPTP, TSTP) :- 
  atomic_list_concat(["eprover --cpu-limit=60 -p ", TPTP, " > ", TSTP], CMD), 
  shell(CMD, _), 
  open(TSTP, read, STRM), 
  e_check(STRM), 
  close(STRM).

call_prover(v, TPTP, TSTP) :- 
  atomic_list_concat(["vampire_rel --proof tptp ", TPTP, " > ", TSTP], CMD),  
  shell(CMD, _), 
  open(TSTP, read, STRM), 
  read_line_to_string(STRM, LINE), 
  close(STRM), 
  LINE = "% Refutation found. Thanks to Tanya!".

call_prover(m, TPTP, TSTP) :- 
  atomic_list_concat(["timeout 60s metis --time-limit 60 --show proof ", TPTP, " > ", TSTP], CMD), 
  shell(CMD, _),
  open(TSTP, read, STRM), 
  read_line_to_string(STRM, _), 
  read_line_to_string(STRM, LINE), 
  close(STRM), 
  string_concat("% SZS status Unsatisfiable for", _, LINE).

solution_archived(PRVR, NAME) :-
  names_archived(PRVR, NAMES),
  member(NAME, NAMES).

solution_failed(PRVR, NAME) :-
  names_failed(PRVR, NAMES),
  member(NAME, NAMES).

check_solution_attempt(PRVR, NAME) :-
  names_archived(PRVR, NAS),
  names_failed(PRVR, NFS),
  (
    member(NAME, NAS) -> 
    msg("Solution already archived"),
    false
  ;
    member(NAME, NFS) -> 
    msg("Solution already attmpted and failed"),
    false
  ; 
    true
  ).

record_failure(PRVR, NAME) :-
  atomic_list_concat(["echo ", NAME, " >> ", PRVR, f], CMD),
  shell(CMD, _).

gen_sol(PRVR, NAME) :-
  name_tptp(NAME, TPTP),
  msg('Problem chosen = ~w', [NAME]),
  atomics_to_string(["./", PRVR, "s/", NAME, ".tstp"], TSTP),
  msg("Begin solution search, solver = ~w", PRVR),
  (
    call_prover(PRVR, TPTP, TSTP) -> 
    msg("Proof search successful.")
  ;
    msg("Proof search failed, deleting solution file, recording failure"),
    delete_file(TSTP),
    record_failure(PRVR, NAME),
    false
  ).

gen_sols(_, 0, _).
gen_sols(PROVER, NUM, NAMES) :- 
  msg('Starting bench : ~w more problems to go', NUM),
  num_pred(NUM, PRED), 
  msg("Choosing random problem"), 
  random_pluck(NAMES, NAME, REST), 
  (
    gen_sol(PROVER, NAME) ->
    gen_sols(PROVER, PRED, REST) ; 
    gen_sols(PROVER, NUM, REST)  
  ).

main([PROVER, NUM_ATOM]) :- 
  prover_abrv(PROVER, PRVR),
  get_problem_names(ALL),
  length(ALL, ALL_NUM),
  format("+ Total number of problems = ~w\n", ALL_NUM), 
  names_archived(PRVR, NAS),
  length(NAS, NAS_NUM),
  format("- Number of archived problems = ~w\n", NAS_NUM), 
  names_failed(PRVR, NFS),
  length(NFS, NFS_NUM),
  format("- Number of failed problems = ~w\n", NFS_NUM), 
  subtract(ALL, NAS, TEMP),
  subtract(TEMP, NFS, NEW),
  write("---------------------------------------\n"),
  length(NEW, NEW_NUM),
  format("Number of unattempted problems = ~w\n", NEW_NUM),
  atom_number(NUM_ATOM, NUM),
  msg("Enter solution genaration loop"),
  gen_sols(PRVR, NUM, NEW), 
  msg("Exit solution generation loop"),
  true.