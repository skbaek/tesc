% :- module(tptp, [pose/5]).

:- [basic].
:- [op].

current_directory(X) :- working_directory(X, X).

name_cat(NAME, CAT) :- 
  atom_chars(NAME, [A, B, C | _]), 
  atomic_list_concat([A, B, C], CAT).

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

ids_from_ax(AX, IDS_I, IDS_O) :-
  tptp_directory(TPTP),
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
  name_tptp(NAME, TPTP), 
  empty_assoc(EMP), !,
  ids_from_path(TPTP, EMP, IDS).

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

try_add(ID, PROB, PROB_N) :- !, 
  get_assoc(ID, PROB, c) -> 
  write("Found duplicate ids\n\n"),
  false 
;
  put_assoc(ID, PROB, c, PROB_N).


fst((X, _), X).


is_large(PATH) :-
  path_name(PATH, NAME),
  member(
    NAME,
    [
'CSR061+6',
'CSR055+6',
'CSR033+6',
'CSR029+6',
'CSR053+6',
'CSR057+6',
'CSR028+6',
'CSR072+6',
'CSR056+6',
'CSR049+6',
'CSR036+6',
'CSR041+6',
'CSR035+6',
'CSR037+6',
'CSR068+6',
'CSR031+6',
'CSR071+6',
'CSR058+6',
'CSR038+6',
'CSR051+6',
'CSR059+6',
'CSR027+6',
'CSR043+6',
'CSR032+6',
'CSR052+6',
'CSR069+6',
'CSR040+6',
'CSR065+6',
'CSR064+6',
'CSR073+6',
'CSR050+6',
'CSR044+6',
'CSR042+6',
'CSR034+6',
'CSR026+6',
'CSR025+6',
'CSR060+6',
'CSR070+6',
'CSR045+6',
'CSR063+6',
'CSR074+6',
'CSR030+6',
'CSR066+6',
'CSR067+6',
'CSR047+6',
'CSR039+6',
'CSR062+6',
'CSR046+6',
'CSR111+6',
'CSR048+6',
'CSR054+6'
    ]
  ).


poseable(TPTP) :- 
%   is_large(TPTP) -> 
%   write("Handling large CSR problem\n\n"), 
%   read_file_to_terms(csr_large, [ASSOC], []),
%   tptp_pclas_without_large(TPTP, PCLAS), !,
%   maplist_cut(fst, PCLAS, IDS), !,
%   foldl_cut(try_add, IDS, ASSOC, _)
% ;
  tptp_pclas(TPTP, PCLAS), !,
  maplist_cut(fst, PCLAS, IDS), !,
  empty_assoc(EMP), !, 
  foldl_cut(try_add, IDS, EMP, _).

  
% prob_has_dup(TPTP) :- 
%   tptp_pclas(TPTP, PCLAS),
%   maplist_cut(pcla_id, PCLAS, IDS),
%   list_has_dup(IDS).
% 
% list_has_dup([ELEM | LIST]) :-
%   member(ELEM, LIST) ; 
%   list_has_dup(LIST).
%   
% 