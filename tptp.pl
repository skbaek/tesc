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

% tptp_pclas_without_large(TPTP, PCLAS) :- 
%   style_check(-singleton),
%   declare_TPTP_operators,
%   tptp_terms(TPTP, TERMS),
%   partition(is_include, TERMS, INCLS, ORIG),
%   delete(INCLS, include('Axioms/CSR002+5.ax'), INCLS_NEW),
%   maplist(include_terms, INCLS_NEW, AXIOMSS),
%   append([ORIG | AXIOMSS], PRECLAS),
%   maplist(precla_pcla, PRECLAS, PCLAS), 
%   true.


tptp_pclas(TPTP, PCLAS) :- 
  style_check(-singleton),
  declare_TPTP_operators,
  tptp_terms(TPTP, TERMS),
  partition(is_include, TERMS, INCLS, ORIG),
  maplist(include_terms, INCLS, AXIOMSS),
  append([ORIG | AXIOMSS], PRECLAS),
  maplist(precla_pcla, PRECLAS, PCLAS), 
  true.

add_hyp((ID, SF), PROB, PROB_N) :- !, 
  get_assoc(ID, PROB, _) -> 
  write("Found duplicate ids\n\n"),
  false 
;
  put_assoc(ID, PROB, SF, PROB_N).

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

pcla_hyp((ID, FORM), (ID, $pos(FORM))).

pcla_cla((ID, FORM), (ID, NORM)) :- 
  inst_with_lvs(FORM, BODY), !,
  body_lits(BODY, LITS, []), !, 
  predsort(lit_cmp, LITS, TEMP), !,
  reverse(TEMP, NORM), !.

pose(MODE, TPTP, HYPS, CLAS, PROB) :- 
  tptp_pclas(TPTP, PCLAS),
  maplist_cut(pcla_hyp, PCLAS, HYPS),
  ( 
    MODE = verbose ->
    convlist(pcla_cla, PCLAS, CLAS) 
  ;
    true
  ),
  empty_assoc(EMP), 
  foldl_cut(add_hyp, HYPS, EMP, PROB).