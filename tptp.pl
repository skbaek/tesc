:- [op].

tptp_directory("/home/sk/programs/TPTP/").

current_directory(X) :-
  working_directory(X, X).

name_cat(NAME, CAT) :- 
  atom_chars(NAME, [A, B, C | _]), 
  atomic_list_concat([A, B, C], CAT).

is_include(include(_)).

include_terms(include(AXIOM), TERMS) :- 
  tptp_directory(TPTP), 
  atomics_to_string([TPTP, AXIOM], PATH),
  read_file_to_terms(PATH, TERMS, []).
  
precla_id_pcla(PRECLA, ID, (ID, TYPE, FORM)) :- 
  PRECLA =.. [LNG, ID, TYPE, TF], 
  tf_form(LNG, TF, FORM).

tptp_ids_pclas(TPTP, IDS, PCLAS) :- 
  style_check(-singleton),
  declare_TPTP_operators,
  % read_file_to_terms(TPTP, TERMS, []),
  tptp_terms(TPTP, TERMS),
  partition(is_include, TERMS, INCLS, ORIG),
  maplist(include_terms, INCLS, AXIOMSS),
  append([ORIG | AXIOMSS], PRECLAS),
  maplist(precla_id_pcla, PRECLAS, IDS, PCLAS), 
  true.

add_pcla((ID, conjecture, FORM), PROB_IN, PROB_OUT) :- !,
  put_assoc(ID, PROB_IN, $pos($not(FORM)), PROB_OUT).

add_pcla((ID, _, FORM), PROB_IN, PROB_OUT) :- 
  put_assoc(ID, PROB_IN, $pos(FORM), PROB_OUT).

pose(TPTP, IDS, PROB) :- 
  % trim_consult(TPTP),
  empty_assoc(EMP), 
  % findall(HYP, hypothesis(HYP), HYPS), 
  % maplist_cut(fst, HYPS, IDS),
  tptp_ids_pclas(TPTP, IDS, PCLAS),
  foldl(add_pcla, PCLAS, EMP, PROB).
