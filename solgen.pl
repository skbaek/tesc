#!/usr/bin/env swipl

:- initialization(main, main).
:- use_module(library(shell)).
:- [solve, prove, check].

path_cat_id(Path, Cat, ID) :- 
  atom_codes(Path, Codes0), 
  append(_, [47 | Codes1], Codes0),
  \+ member(47, Codes1), 
  append([C0, C1, C2 | Rest], [46, 112], Codes1),
  string_codes(Cat, [C0, C1, C2]),
  string_codes(ID, Rest).

msg(PTRN, ARGS) :-
  % write(" ────────────────────────────────────────────────────────────────── "), 
  write("                                                                      > "), 
  format(PTRN, ARGS),
  write("\n\n").

msg(STR) :-
  % write(" ────────────────────────────────────────────────────────────────── "), 
  write("                                                                      > "), 
  write(STR),
  write("\n\n").

is_fol_prob(PATH) :- 
  \+ sub_string(PATH, _, _, _, "="),
  \+ sub_string(PATH, _, _, _, "^"), 
  \+ sub_string(PATH, _, _, _, "_"), 
  string_concat(_, ".p", PATH).
  
call_tptp2x(CAT, ID) :- 
  atomics_to_string([CAT, ID, ".tptp"], TPTP),
  atomics_to_string(["tptp2X -ftptp -dtemp ~/programs/TPTP/Problems/", CAT, "/", CAT, ID, ".p"], CMD), 
  shell(CMD, _),
  atomics_to_string(["temp/", CAT, "/", TPTP], TEMP_PATH),
  mv(TEMP_PATH, TPTP),
  shell("rm -r temp", _).

call_compiler(v, TPTP, TSTP, TXTX) :- 
  set_prolog_flag(stack_limit, 2_147_483_648),
  style_check(-singleton),
  pose(TPTP, PIDS, PROB),
  solve(PRVR, PIDS, TSTP, SOL),
  open(TXTX, write, STRM, [encoding(octet)]),
  prove(STRM, none, PRVR, SOL, PROB),
  close(STRM).

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

mv_concat(FILE, LIST) :- 
  atomic_list_concat(LIST, PATH),
  mv(FILE, PATH).

gen_sol(PROVER, TPTP) :- 
  string_concat(TEMP, ".tptp", TPTP),
  string_concat("./p/", NAME, TEMP),
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
  rec_dir_files("./p/", PATHS), 
  atom_number(NUM_ATOM, NUM),
  msg("Enter gen loop"),
  gen_sols(PROVER, NUM, PATHS), 
  msg("Exit gen loop").