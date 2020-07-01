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
  
precla_pcla(PRECLA, (ID, FORM)) :- 
  PRECLA =.. [LNG, ID, TYPE, TF], 
  tf_form(LNG, TF, TEMP),
  (
    TYPE = conjecture -> 
    FORM = $not(TEMP) 
  ;
    FORM = TEMP
  ).

tptp_pclas(TPTP, PCLAS) :- 
  style_check(-singleton),
  declare_TPTP_operators,
  % read_file_to_terms(TPTP, TERMS, []),
  tptp_terms(TPTP, TERMS),
  partition(is_include, TERMS, INCLS, ORIG),
  maplist(include_terms, INCLS, AXIOMSS),
  append([ORIG | AXIOMSS], PRECLAS),
  maplist(precla_pcla, PRECLAS, PCLAS), 
  true.

add_pcla((ID, FORM), PROB_IN, PROB_OUT) :- !, 
  put_assoc(ID, PROB_IN, $pos(FORM), PROB_OUT).

% lit_cmp_gnd((>), LIT_A, LIT_B) :-
%   no_fv_form(0, LIT_A), 
%   \+ no_fv_form(0, LIT_B).
  
%  lit_cmp_gnd((<), LIT_A, LIT_B) :-
%    no_fv_form(0, LIT_B), 
%    \+ no_fv_form(0, LIT_A).

form_gnd(FORM, NUM) :- 
  ground(FORM) ->
  NUM = 1 
;
  NUM = 0.

exp_size(VAR, 1) :- var(VAR), !.
exp_size(EXP, SIZE) :- 
  EXP =.. [_ | ARGS], 
  maplist_cut(exp_size, ARGS, SIZES),
  sum_list([1 | SIZES], SIZE).

exp_depth(VAR, 0) :- var(VAR), !.
exp_depth(EXP, DEPTH) :- 
  EXP =.. [_ | ARGS], 
  (
    ARGS == [] -> 
    DEPTH = 0 
  ;
    maplist_cut(exp_depth, ARGS, DEPTHS),
    max_list(DEPTHS, PRED),
    num_succ(PRED, DEPTH)
  ).

exp_cnum(VAR, 0) :- var(VAR), !.
exp_cnum(EXP, CNUM) :- 
  EXP =.. [_ | ARGS], 
  (
    ARGS == [] -> 
    CNUM = 1 
  ;
    maplist_cut(exp_cnum, ARGS, CNUMS),
    sum_list(CNUMS, CNUM)
  ).

measure_cmp(MSR, EXP_A, EXP_B, ORD) :- 
  call(MSR, EXP_A, NUM_A),
  call(MSR, EXP_B, NUM_B),
  (
    NUM_A > NUM_B, ORD = (>) ;
    NUM_B > NUM_A, ORD = (<)
  ).

lit_cmp(ORD, LIT_A, LIT_B) :- 
  lit_atom(LIT_A, ATOM_A),
  lit_atom(LIT_B, ATOM_B),
  atom_cmp(ORD, ATOM_A, ATOM_B).

atom_cmp(ORD, ATOM_A, ATOM_B) :- 
  (
    measure_cmp(form_gnd, ATOM_A, ATOM_B, ORD) ;
    measure_cmp(exp_depth, ATOM_A, ATOM_B, ORD) ;
    measure_cmp(exp_size, ATOM_A, ATOM_B, ORD) ;
    measure_cmp(exp_cnum, ATOM_A, ATOM_B, ORD) ;
    compare(ORD, ATOM_A, ATOM_B) 
  ), !.

pcla_cla((ID, FORM), (ID, NORM)) :- 
  inst_with_lvs(FORM, BODY), !,
  body_lits(BODY, LITS), !, 
  predsort(lit_cmp, LITS, TEMP), !,
  reverse(TEMP, NORM), !.

pose(MODE, TPTP, PIDS, CLAS, PROB) :- 
  empty_assoc(EMP), 
  tptp_pclas(TPTP, PCLAS),
  ( 
    MODE = verbose ->
    maplist_cut(fst, PCLAS, PIDS),
    convlist(pcla_cla, PCLAS, CLAS) 
  ;
    true
  ),
  foldl(add_pcla, PCLAS, EMP, PROB).
