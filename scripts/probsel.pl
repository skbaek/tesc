#!/usr/bin/env swipl

:- [misc].

:- initialization(main, main).
% :- use_module(library(shell)).

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
  
partition_cut(_, [], [], []). 
partition_cut(PRED, [ELEM | LIST], INC, EXC) :- 
  call(PRED, ELEM) -> 
  INC = [ELEM | INC_TAIL], 
  partition_cut(PRED, LIST, INC_TAIL, EXC) 
; 
  EXC = [ELEM | EXC_TAIL], 
  partition_cut(PRED, LIST, INC, EXC_TAIL). 


loadable(NAME) :- 
  format("Testing : ~w, ", NAME),
  (
    ids_from_name(NAME, _) ->
    true
  ;
    format("~w is non-unique, not loadable\n\n", NAME),
    false
  ).

include_count(_, _, [], []) :- write("Finish inclusion.\n\n").

include_count(GOAL, CNT, [ELEM | IN], OUT) :-
  format("count = ~w\n\n", CNT), !,
  num_succ(CNT, SUCC), !,
  (
    call(GOAL, ELEM) -> 
    OUT = [ELEM | TAIL], 
    include_count(GOAL, SUCC, IN, TAIL) 
  ; 
    include_count(GOAL, SUCC, IN, OUT) 
  ).

get_problem_names(NAMES) :- path_atoms(problems, NAMES).

create_symlink(PATH, NAME) :- 
  atomic_list_concat([PATH, "/", NAME], DIR), 
  cd(DIR),
  tptp_path(TPTP),
  atomic_list_concat(["ln -s ", TPTP, "Axioms/ Axioms"], CMD), 
  shell(CMD, _).

symlink :- 
  tptp_path(TPTP),
  atomic_concat(TPTP, "Problems", PATH),
  path_filenames(PATH, X), 
  write_list(X),
  maplist_cut(create_symlink(PATH), X).


main([DA, TA]) :- 
  % set_prolog_flag(stack_limit, 4_294_967_296),
  atom_number(DA, DROP),
  atom_number(TA, TAKE),
  get_problem_names(ALL), 
  slice(DROP, TAKE, ALL, NAMES),
  % maplist(path_name, PATHS, TEMP), 
  % open(problems, write, STRM), 
  write_list(STRM, NAMES),
  close(STRM),
  true.
  

ends_with_p(PATH) :- atom_concat(_, '.p', PATH).

prob_names(PROB_NAMES) :-
  % set_prolog_flag(stack_limit, 4_294_967_296),
  msg("Generating paths"),
  tptp_path(TPTP),
  atomic_list_concat([TPTP, "Problems"], PATH),
  rec_path_filenames(PATH, PATHS), 
  convlist(probpath_probname, PATHS, UNSORTED),
  sort(UNSORTED, PROB_NAMES),
  % partition_cut(is_fol_thm, ALL, PATHS, _), !, 
  true.

%   include_count(loadable, 0, NAMES, GOOD),
%   wf_list(PATH, GOOD).
% 
% 
% record_assoc(AXIOM) :- 
%   include_terms(include(AXIOM), TERMS),
%   maplist(precla_pcla, TERMS, PCLAS), 
%   maplist_cut(fst, PCLAS, IDS), !,
%   empty_assoc(EMP),
%   foldl_cut(try_add, IDS, EMP, ASSOC),
%   write_file(csr_large, ASSOC).
% 
