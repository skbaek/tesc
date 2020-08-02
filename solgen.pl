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

gen_sol(PROVER, TPTP) :-
  tptp_name(TPTP, NAME),
  msg('Problem chosen = ~w', [NAME]),
  atomics_to_string(["./", PROVER, "s/", NAME, ".tstp"], TSTP),
  msg("Begin proof search with ~w", PROVER),
  (
    call_prover(PROVER, TPTP, TSTP) -> 
    msg("Proof search successful.")
  ;
    (
      msg("Proof search failed, deleting solution file"),
      delete_file(TSTP),
      false
    )
  ).

gen_sols(_, 0, _).
gen_sols(PROVER, NUM, PATHS) :- 
  msg('Starting bench : ~w more problems to go', NUM),
  num_pred(NUM, PRED), 
  msg("Choosing random problem"), 
  random_pluck(PATHS, PATH, REST), 
  (
    gen_sol(PROVER, PATH) ->
    gen_sols(PROVER, PRED, REST) ; 
    gen_sols(PROVER, NUM, REST)  
  ).

main([PROVER, NUM_ATOM]) :- 
  prover_abrv(PROVER, PRVR),
  probsel(PATHS),
  atom_number(NUM_ATOM, NUM),
  msg("Enter gen loop"),
  gen_sols(PRVR, NUM, PATHS), 
  msg("Exit gen loop").