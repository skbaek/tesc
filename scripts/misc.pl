:- consult("../tesc/basic.pl").
:- consult("../tesc/paths.pl").

maplist_count(_, CNT, TTL, [], CNT, TTL).
maplist_count(GOAL, CNT_I, TTL_I, [ELEM | LIST], CNT_O, TTL_O) :- 
  atomics_to_string(["PASSED/TOTAL = ", CNT_I, "/", TTL_I, "\n"], STRING),
  write(STRING),
  (call(GOAL, ELEM) -> num_succ(CNT_I, CNT_T) ; CNT_I = CNT_T),
  num_succ(TTL_I, TTL_T), 
  maplist_count(GOAL, CNT_T, TTL_T, LIST, CNT_O, TTL_O).

names_proven(PRVR, NAMES) :- 
  atom_concat(PRVR, prf, PATH),
  rec_path_filenames(PATH, PATHS),
  maplist_cut(path_name, PATHS, NAMES).

drop(0, LIST, LIST). 
drop(NUM, [_ | LIST], REM) :- 
  num_pred(NUM, PRED),
  drop(PRED, LIST, REM).

take(0, _, []). 
take(NUM, [ELEM | LIST], [ELEM | REM]) :- 
  num_pred(NUM, PRED),
  take(PRED, LIST, REM).

slice(DROP, TAKE, LIST, SLICE) :- 
  drop(DROP, LIST, TEMP), 
  take(TAKE, TEMP, SLICE). 

get_solution_names(PRVR, NAMES) :- 
  atom_concat(PRVR, sol, PATH),
  rec_path_filenames(PATH, PATHS),
  maplist_cut(path_name, PATHS, NAMES).

random_pluck(LIST, ELEM, REST) :- 
  random_member(ELEM, LIST), 
  delete(LIST, ELEM, REST).

random_n(0, _, []) :- !.
random_n(NUM, LIST, [ELEM | SEL]) :- 
  num_pred(NUM, PRED),
  random_pluck(LIST, ELEM, REST), 
  random_n(PRED, REST, SEL).
  
ids_from_ax(AX, IDS_I, IDS_O) :-
  tptp_path(TPTP),
  atomics_to_string([TPTP, AX], PATH), !,
  ids_from_path(PATH, IDS_I, IDS_O).

ids_from_codes([105, 110, 99, 108, 117, 100, 101, 40, 39 | CODES], IDS_I, IDS_O) :- !, 
  append(AX_CODES, [39 | _], CODES), !, 
  atom_codes(AX, AX_CODES), !,
  ids_from_ax(AX, IDS_I, IDS_O).


ids_from_codes(CODES, IDS_I, IDS_O) :- 
  (
    CODES = [99, 110, 102, 40 | TAIL] ;
    CODES = [102, 111, 102, 40 | TAIL] 
  ) -> 
  append(ID_CODES, [44 | _], TAIL), !, 
  atom_codes(ID, ID_CODES), 
  (
    get_assoc(ID, IDS_I, c) -> 
    format("Duplicate ids found : ~w is already present\n\n", ID),
    false 
  ;
    put_assoc(ID, IDS_I, c, IDS_O)
  )
;
  IDS_O = IDS_I.

ids_from_strm(STRM, IDS_I, IDS_O) :- 
  read_line_to_codes(STRM, CODES), 
  ( 
    CODES = end_of_file -> 
    IDS_O = IDS_I
  ;
    ids_from_codes(CODES, IDS_I, IDS_T), !,
    ids_from_strm(STRM, IDS_T, IDS_O) 
  ).

ids_from_path(PATH, IDS_I, IDS_O) :- 
  open(PATH, read, STRM), !,
  ids_from_strm(STRM, IDS_I, IDS_O), !,
  close(STRM).

ids_from_name(NAME, IDS) :- 
  name_probpath(NAME, TPTP), 
  empty_assoc(EMP), !,
  ids_from_path(TPTP, EMP, IDS).

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

codes_after_last_slash(ATOM, CODES) :- 
  atom_codes(ATOM, ALL), 
  append(_, [47 | CODES], ALL),
  \+ member(47, CODES). 
  
path_cat_id(Path, Cat, ID) :- 
  codes_after_last_slash(Path, Codes1), 
  append([C0, C1, C2 | Rest], [46, 112], Codes1),
  string_codes(Cat, [C0, C1, C2]),
  string_codes(ID, Rest).

path_name(PATH, NAME) :- 
  codes_after_last_slash(PATH, TEMP1), !, 
  append(TEMP2, [46 | TEMP3], TEMP1),
  \+ member(46, TEMP3), !, 
  atom_codes(NAME, TEMP2).

probpath_probname(PATH, NAME) :- 
  codes_after_last_slash(PATH, CODES_A), !, 
  append(CODES_B, [46, 112], CODES_A),
  atom_codes(NAME, CODES_B).

path_atoms(PATH, ATOMS) :- 
  open(PATH, read, STRM), 
  stream_strings(STRM, STRS),
  maplist_cut(string_to_atom, STRS, ATOMS).

path_cat(PATH, CAT) :- 
  atom_codes(PATH, [C0, C1, C2 | _]), 
  string_codes(CAT, [C0, C1, C2]).

name_cat(NAME, CAT) :- 
  atom_chars(NAME, [A, B, C | _]), 
  atomic_list_concat([A, B, C], CAT).

name_solpath(SVR, NAME, SOL_PATH) :- 
  tesc_path(TESC_PATH),
  atomic_list_concat([TESC_PATH, SVR, 'sol/', NAME, ".s"], SOL_PATH).

name_probpath(PROB_NAME, PROB_PATH) :- 
  tptp_path(TPTP_PATH),
  atom_codes(PROB_NAME, [C0, C1, C2 | _]),
  atom_codes(CAT, [C0, C1, C2]),  
  atomic_list_concat([TPTP_PATH, 'Problems/', CAT, "/", PROB_NAME, ".p"], PROB_PATH).
  
write_punct(STRM, TERM) :- 
  write_term(STRM, TERM, [fullstop(true), nl(true), quoted(true)]).

update_problems(TERMS) :- 
  open('problems.pl', append, STRM), 
  maplist(write_punct(STRM), TERMS), !,
  close(STRM).

atom_includes_char(ATOM, CHAR) :- 
  atom_codes(ATOM, CODES),
  char_code(CHAR, CODE),
  member(CODE, CODES).

