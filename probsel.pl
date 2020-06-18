#!/usr/bin/env swipl

:- initialization(main, main).
% :- use_module(library(shell)).

:- [basic].

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

is_fol_thm(PATH) :- 
  string_concat(_, ".p", PATH),
  \+ sub_string(PATH, _, _, _, "="),
  \+ sub_string(PATH, _, _, _, "^"), 
  \+ sub_string(PATH, _, _, _, "_"), 
  is_thm(PATH).
  % file_strings(PATH, STRS),
  % member(STR, STRS),
  % split_string(STR, ":", " %", ["Status", STAT_STR]), 
  % member(STAT_STR, ["Theorem", "Unsatisfiable"]).
  
call_tptp2x(PATH) :- 
  path_cat_id(PATH, CAT, ID), 
  atomics_to_string([CAT, ID, ".tptp"], TPTP),
  atomics_to_string(["tptp2X -ftptp -dtemp ~/programs/TPTP/Problems/", CAT, "/", CAT, ID, ".p"], CMD), 
  shell(CMD, _),
  atomics_to_string(["temp/", CAT, "/", TPTP], OLD_PATH),
  atomics_to_string(["p/", TPTP], NEW_PATH),
  mv(OLD_PATH, NEW_PATH),
  shell("rm -r temp", _).

mv_concat(FILE, LIST) :- 
  atomic_list_concat(LIST, PATH),
  mv(FILE, PATH).

is_thm_core(STRM) :-
  read_line_to_string(STRM, STR), 
  (
    STR = end_of_file -> 
    close(STRM), 
    false
  ;
    (
      split_string(STR, ":", " %", ["Status", STAT]), 
      member(STAT, ["Theorem", "Unsatisfiable"])
    ) -> 
    close(STRM)
  ;
    is_thm_core(STRM)
  ).

is_thm(PATH) :-
  open(PATH, read, STRM), 
  is_thm_core(STRM).

prob_ext(PATH) :- 
  call_tptp2x(PATH) -> true ;
  atomics_to_string(["echo ", PATH, " >> ", "failed.txt"], CMD),
  shell(CMD, _).

drop(0, X, X).
drop(NUM, [_ | Y], Z) :-
  0 < NUM,
  PRED is NUM - 1,  
  drop(PRED, Y, Z).
  
partition_cut(_, [], [], []). 
partition_cut(PRED, [ELEM | LIST], INC, EXC) :- 
  call(PRED, ELEM) -> 
  INC = [ELEM | INC_TAIL], 
  partition_cut(PRED, LIST, INC_TAIL, EXC) 
; 
  EXC = [ELEM | EXC_TAIL], 
  partition_cut(PRED, LIST, INC, EXC_TAIL). 

probsel(PATHS) :- 
  set_prolog_flag(stack_limit, 4_294_967_296),
  msg("Generating paths"),
  rec_dir_files("/home/sk/programs/TPTP/Problems", ALL), 
  partition_cut(is_fol_thm, ALL, PATHS, _), !, 
  % append(_, ['/home/sk/programs/TPTP/Problems/CSR/CSR054+6.p' | REST], TEMP),
  % PATHS = (['/home/sk/programs/TPTP/Problems/CSR/CSR054+6.p' | REST]),
  % maplist_cut(prob_ext, PATHS),
  true.
  