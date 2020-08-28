% :- module(tptp, [pose/5]).

:- [basic].
:- [op].

is_include(include(_)).

include_terms(include(AXIOM), TERMS) :- 
  tptp_directory(TPTP),
  atomics_to_string([TPTP, AXIOM], PATH),
  tptp_terms(PATH, TERMS).
  
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
  tptp_terms(TPTP, TERMS),
  partition(is_include, TERMS, INCLS, ORIG),
  maplist(include_terms, INCLS, AXIOMSS),
  append([ORIG | AXIOMSS], PRECLAS),
  maplist(precla_pcla, PRECLAS, PCLAS), 
  true.

add_hyp((ID, FORM), PROB, PROB_N) :- !, 
  get_assoc(ID, PROB, _) -> 
  write("Found duplicate ids\n\n"),
  false 
;
  put_assoc(ID, PROB, FORM, PROB_N).

nonfun($var(_)).
nonfun($dst(_)).

form_gnd(FORM, NUM) :- 
  ground(FORM) ->
  NUM = 1 
;
  NUM = 0.

term_node_count(TERM, 1) :- (var(TERM) ; nonfun(TERM)), !.
term_node_count($fun(_, TERMS), NUM) :- 
  maplist_cut(term_node_count, TERMS, NUMS),
  sum_list([1 | NUMS], NUM).

form_node_count(FORM, CNT) :- 
  decom_uct(FORM, _, SUB),
  form_node_count(SUB, PRED),
  num_succ(PRED, CNT).
form_node_count(FORM, CNT) :- 
  decom_bct(FORM, _, FORM_A, FORM_B),
  form_node_count(FORM_A, CNT_A),
  form_node_count(FORM_B, CNT_B),
  CNT is CNT_A + CNT_B + 1.
form_node_count($rel(_, TERMS), NUM) :- 
  maplist_cut(term_node_count, TERMS, NUMS),
  sum_list([1 | NUMS], NUM).

term_depth(TERM, 0) :- (var(TERM) ; nonfun(TERM)), !.
term_depth($fun(_, TERMS), DEP) :- 
  maplist_cut(term_depth, TERMS, DEPS),
  max_list(DEPS, PRED),
  num_succ(PRED, DEP).

form_depth(FORM, DEP) :- 
  decom_uct(FORM, _, SUB),
  form_depth(SUB, PRED),
  num_succ(PRED, DEP).
form_depth(FORM, DEP) :- 
  decom_bct(FORM, _, FORM_A, FORM_B),
  form_depth(FORM_A, NUM_A),
  form_depth(FORM_B, NUM_B),
  max(NUM_A, NUM_B, MAX),
  num_succ(MAX, DEP).
form_depth($rel(_, TERMS), DEP) :- 
  maplist_cut(term_depth, TERMS, DEPS),
  max_list(DEPS, PRED),
  num_succ(PRED, DEP).

term_cnum(TERM, 0) :- (var(TERM) ; nonfun(TERM)), !.
term_cnum($fun(_, TERMS), NUM) :- 
  maplist_cut(term_cnum, TERMS, NUMS),
  sum_list([1 | NUMS], NUM). 

form_cnum(FORM, NUM) :- !, 
  decom_bct(FORM, _, FORM_A, FORM_B),
  form_cnum(FORM_A, NUM_A),
  form_cnum(FORM_B, NUM_B),
  NUM is NUM_A + NUM_B.
form_cnum(FORM, NUM) :- 
  decom_uct(FORM, _, SUB), !,
  form_cnum(SUB, NUM).
form_cnum($rel(_, TERMS), NUM) :- 
  maplist_cut(term_cnum, TERMS, NUMS),
  sum_list(NUMS, PRED), 
  num_succ(PRED, NUM).

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
    measure_cmp(form_depth, ATOM_A, ATOM_B, ORD) ;
    measure_cmp(form_node_count, ATOM_A, ATOM_B, ORD) ;
    measure_cmp(form_cnum, ATOM_A, ATOM_B, ORD) ;
    compare(ORD, ATOM_A, ATOM_B) 
  ), !.

pcla_cla((ID, FORM), (ID, NORM)) :- 
  inst_with_lvs(FORM, BODY), !,
  body_lits(BODY, LITS, []), !, 
  predsort(lit_cmp, LITS, TEMP), !,
  reverse(TEMP, NORM), !.

pose(TPTP, PROB) :- 
  tptp_pclas(TPTP, PCLAS),
  empty_assoc(EMP), 
  foldl_cut(add_hyp, PCLAS, EMP, PROB).

pose_path(TPTP, TTP) :- 
  open(TTP, write, WS, [encoding(octet)]), !, 
  empty_assoc(EMP), 
  pose_path(WS, TPTP, EMP, _),
  put_char(WS, '.'),
  close(WS).
  
pose_path(WS, PATH, NAMES_I, NAMES_O) :- 
  style_check(-singleton),
  declare_TPTP_operators,
  tptp_terms(PATH, TERMS), !, 
  foldl_cut(pose_term(WS), TERMS, NAMES_I, NAMES_O),
  %  partition(is_include, TERMS, INCLS, ORIG),
  %  maplist(include_terms, INCLS, AXIOMSS),
  %  append([ORIG | AXIOMSS], PRECLAS),
  %  maplist(precla_pcla, PRECLAS, PCLAS), 
  true.

pose_term(WS, include(AX), NAMES_I, NAMES_O) :- !, 
  tptp_directory(TPTP),
  atomics_to_string([TPTP, AX], PATH), !, 
  pose_path(WS, PATH, NAMES_I, NAMES_O), !.

pose_term(WS, TERM, NAMES_I, NAMES_O) :- 
  TERM =.. [LNG, NAME, TYPE, TF], 
  (
    get_assoc(NAME, NAMES_I, _) ->
    format("Duplicate ID found = ~w\n", NAME), false 
  ; 
    true
  ),
  put_assoc(NAME, NAMES_I, c, NAMES_O), 
  tf_form(LNG, TF, TEMP),
  (
    TYPE = conjecture -> 
    FORM = $not(TEMP) 
  ;
    FORM = TEMP
  ),
  put_char(WS, ';'),
  put_name(WS, NAME),
  put_form(WS, FORM).

