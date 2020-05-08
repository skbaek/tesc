:- [basic].

% id_sid(ID, s(ID)).
  % atom_concat('s', ID, SID).

%rul_hint(cnf_transformation, v_cnf).
% rul_hint(flattening, flt).  
% rul_hint(skolemisation, skm).  
% rul_hint(ennf_transformation, ennf).  
% rul_hint(nnf_transformation, nnf).  
% rul_hint(avatar_component_clause, acmp).
% rul_hint(rectify, rtf).
% rul_hint(factoring, wkn).
% rul_hint(duplicate_literal_removal, wkn).
% rul_hint(true_and_false_elimination, tfe).
% rul_hint(pure_predicate_removal, ppr).
% rul_hint(distinct_equality_removal, der).

rul_hint(superposition, (sup, l)).  
rul_hint(forward_demodulation, (sup, l)).
rul_hint(backward_demodulation, (sup, r)).
rul_hint(resolution, res).
rul_hint(subsumption_resolution, res).
rul_hint(trivial_inequality_removal, eqr).
rul_hint(equality_resolution, eqr).
rul_hint(equality_factoring, eqf).

rul_hint(cnf_transformation, dtrx).
rul_hint(factoring, dtrx).
rul_hint(avatar_component_clause, dtrx).
rul_hint(avatar_contradiction_clause, pblx).
rul_hint(duplicate_literal_removal, dtrx).

% axiom
% conjecture
rul_hint(negated_conjecture, parac).  
rul_hint(flattening, parac).  
rul_hint(ennf_transformation, paras).  
rul_hint(rectify, paral).
rul_hint(true_and_false_elimination, paratf).
rul_hint(pure_predicate_removal, parad).
rul_hint(nnf_transformation, vnnf).  

rul_hint(avatar_sat_refutation, sat).
rul_hint(unused_predicate_definition_removal, updr).
rul_hint(avatar_split_clause, spl).
rul_hint(definition_folding, dff).
rul_hint(definition_unfolding, dfu).
rul_hint(choice_axiom, gaoc).
rul_hint(skolemisation, skm).  
% avatar_definition
% predicate_definition_introduction

rul_hint(RUL, _) :- 
  format('Rule not found : ~w', RUL), 
  throw(no_tactic_for_rule). 

rul_hints(RUL, [HINT]) :-
  rul_hint(RUL, HINT).

pred_def_norm(! Xs : TPTP, ! Xs : NewTPTP) :- 
  pred_def_norm(TPTP, NewTPTP).

pred_def_norm((TPTP | ~ Atom), (Atom <=> TPTP)).
pred_def_norm((Atom <=> TPTP), (Atom <=> TPTP)).

v_tup_inst(
  PIDS,
  (ID, conjecture, TF, _),
  inf([parac, dtrx], PIDS, ID, (~ FORM))
) :- 
  fof_form([], TF, FORM).
  
v_tup_inst(
 PIDS,
 (ID, axiom, TF, _),
 inf([parac, dtrx], PIDS, ID, FORM) 
) :-
  fof_form([], TF, FORM).

v_tup_inst(
  _,
  (ID, plain, (PRD <=> TF), introduced(avatar_definition,[new_symbols(naming,[PRD])])), 
  add([def, PRD], ID, FORM)
) :- 
  PRD \= (~ _),
  fof_form([], (PRD <=> TF), FORM).
  
v_tup_inst(
  _,
  (ID, plain, TF, introduced(predicate_definition_introduction,[new_symbols(naming, [PRD])])),
  add([def, PRD], ID, FORM)
) :- 
  pred_def_norm(TF, TEMP),
  fof_form([], TEMP, FORM).

v_tup_inst(
  _, 
  (ID, _, TF, introduced(RUL, _)),
  add(HINTS, ID, FORM)
) :- 
  RUL \= predicate_definition_introduction,
  RUL \= avatar_definition,
  rul_hints(RUL, HINTS),
  fof_form([], TF, FORM).
  
v_tup_inst(
  _, 
  (ID, _, TF, inference(RUL, _, IDS)),
  inf(HINTS, IDS, ID, FORM)
) :-
  rul_hints(RUL, HINTS),
  fof_form([], TF, FORM).

vampire_cmp_hints(ORD, (ID_A, _, _, _), (ID_B, _, _, _)) :- 
  atom_concat('f', TEMP_A, ID_A),
  atom_number(TEMP_A, NUM_A),
  atom_concat('f', TEMP_B, ID_B),
  atom_number(TEMP_B, NUM_B),
  compare(ORD, NUM_A, NUM_B).

update_seen(SEEN, [], SEEN, []).

update_seen(SEEN_I, [ID | IDS], SEEN_O, DELS) :- 
  get_assoc(ID, SEEN_I, c) -> 
  update_seen(SEEN_I, IDS, SEEN_O, DELS) 
;
  put_assoc(ID, SEEN_I, c, SEEN_T),
  DELS = [del(ID) | DELS_T], 
  update_seen(SEEN_T, IDS, SEEN_O, DELS_T). 

insert_dels([], EMP, []) :- 
  empty_assoc(EMP).
  
insert_dels([INST | INSTS_I], SEEN, INSTS_O) :- 
  insert_dels(INSTS_I, SEEN_T, INSTS_T), 
  (
    INST = del(_) -> 
    throw(invalid_deletion)
  ; 
    INST = add(_, _, _) -> 
    SEEN = SEEN_T,
    INSTS_O = [INST | INSTS_T]
  ;
    INST = inf(_, IDS, _, _), 
    sort(IDS, IDS_S), 
    update_seen(SEEN_T, IDS_S, SEEN, DELS), 
    append([INST | DELS], INSTS_T, INSTS_O)
  ).

thread([], X, X).
thread([GOAL | GOALS], X, Z) :-
  call(GOAL, X, Y), 
  thread(GOALS, Y, Z).

bind_par(IDX, CNT, IDX, #(CNT)).
bind_par(IDX_A, _, IDX_B, @(IDX_B)) :- IDX_A \= IDX_B.

bind_var(IDX, CNT, NUM, TERM) :- 
  NUM is IDX + CNT -> 
  TERM = #(CNT)
;
  TERM = #(NUM).

bind_par_term(IDX, CNT, TERM_I, TERM_O) :-
  map_par(bind_par(IDX, CNT), TERM_I, TERM_O).

bind_var_term(IDX, CNT, TERM_I, TERM_O) :-
  map_var(bind_var(IDX, CNT), TERM_I, TERM_O).

par_in(NUM, EXP) :- 
  sub_term(TERM, EXP), 
  \+ var(TERM),
  TERM = @(NUM).

maxpar(EXP, MAX) :- 
  findall(NUM, par_in(NUM, EXP), NUMS), 
  max_list(NUMS, MAX).

bind_vars(FORM_I, FORM_O) :-
  minvar(FORM_I, IDX) ->
  map_form(bind_var_term(IDX), 0, FORM_I, TEMP), 
  bind_vars(! TEMP, FORM_O)
;
  FORM_O = FORM_I.

bind_pars(FORM_I, FORM_O) :-
  maxpar(FORM_I, IDX) -> 
  map_form(bind_par_term(IDX), 0, FORM_I, TEMP), 
  bind_pars(! TEMP, FORM_O)
;
  FORM_O = FORM_I.

revert_pars_par(NUM, IDX, #(DIFF)) :- 
  DIFF is NUM - IDX.

revert_pars_term(NUM, TERM_I, TERM_O) :- 
  map_par(revert_pars_par(NUM), TERM_I, TERM_O).

revert_pars(CNT, FORM, AOC) :- 
  NUM is CNT - 1,
  map_form(revert_pars_term, NUM, FORM, TEMP), 
  add_fas(CNT, TEMP, AOC).

get_fun(TERM, FUN) :-
  TERM =.. [FUN | _].

get_aocs(FORM, SKMS, AOCS) :- 
  inst_with_pars(0, FORM, CNT, ANTE => CONS), 
  mk_pars(desc, CNT, PARS),
  get_aocs_aux(PARS, CNT, ANTE, CONS, SKM_TERMS, FORMS),
  maplist_cut(get_fun, SKM_TERMS, SKMS),
  maplist_cut(revert_pars(CNT), FORMS, AOCS).

get_aocs_aux(ARGS, FP, ? ANTE, CONS, [TERM | TERMS], [(? ANTE) => ANTE_O | AOCS]) :- !,
  subst_form(TERM, ANTE, ANTE_O), 
  get_aocs_aux(ARGS, FP, ANTE_O, CONS, TERMS, AOCS).

get_aocs_aux(_, FP, ANTE, CONS, [], []) :- 
  paral(((0, (+ ANTE)), (1, (- CONS)), (_, FP, 2))).

id_skm_aoc_inst(ID, SKM, AOC, add([aoc, SKM], ID, AOC)).

mk_dels(NUM, DELS) :-
  range(asc, NUM, NUMS),
  maplist_cut(mk(t), NUMS, IDS),
  maplist_cut(mk(del), IDS, DELS).

reduce_gaocs([], []).

reduce_gaocs([INST | INSTS], SOL) :- 
  (
    INST = add([gaoc], ID, FORM) -> 
    get_aocs(FORM, SKMS, AOCS),
    length(SKMS, LTH),
    range(asc, LTH, NUMS),
    maplist_cut(atom_concat(t), NUMS, IDS),
    maplist_cut(id_skm_aoc_inst, IDS, SKMS, AOCS, ADDS), 
    append(ADDS, [inf([gaoc], IDS, ID, FORM)], PFX) ;
    PFX = [INST]
  ),
  reduce_gaocs(INSTS, SFX),
  append(PFX, SFX, SOL). 

axiomatic(TYPE) :- 
  member(TYPE, [lemma, axiom, hypothesis, conjecture, negated_conjecture]).

mk_rw(ATOM, ~ FORM, ~ RW) :- !,
  mk_rw(ATOM, FORM, RW).

mk_rw(ATOM, (FORM_L | FORM_R), (RW_L | RW_R)) :- !,
  mk_rw(ATOM, FORM_L, RW_L), 
  mk_rw(ATOM, FORM_R, RW_R).

mk_rw(ATOM, FORM, RW) :- 
  syeq_atom(ATOM, FORM) -> RW = $true ; 
  RW = FORM.

mk_rw_form(LHS, RHS, ~ FORM, ~ RW) :- !,
  mk_rw_form(LHS, RHS, FORM, RW).

mk_rw_form(LHS, RHS, (FORM_L | FORM_R), (RW_L | RW_R)) :- !,
  (
    mk_rw_form(LHS, RHS, FORM_L, RW_L),
    FORM_R = RW_R
  ;
    mk_rw_form(LHS, RHS, FORM_R, RW_R),
    FORM_L = RW_L
  ).

mk_rw_form(LHS, RHS, FORM_I, FORM_O) :- 
  FORM_I =.. [REL | TERMS_I], 
  mk_rw_terms(LHS, RHS, TERMS_I, TERMS_O), 
  FORM_O =.. [REL | TERMS_O]. 

mk_rw_terms(LHS, RHS, [TERM_I | TERMS_I], [TERM_O | TERMS_O]) :-  
  mk_rw_term(LHS, RHS, TERM_I, TERM_O),
  TERMS_I = TERMS_O 
;
  TERM_I = TERM_O, 
  mk_rw_terms(LHS, RHS, TERMS_I, TERMS_O).

mk_rw_term(LHS, RHS, TERM_I, TERM_O) :- 
  unify_with_occurs_check(LHS, TERM_I),
  unify_with_occurs_check(RHS, TERM_O)
; 
  \+ var(TERM_I),
  TERM_I =.. [FUN | TERMS_I], 
  mk_rw_terms(LHS, RHS, TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O]. 

mk_cf([], $false).
mk_cf([LIT], LIT) :- !.
mk_cf([LIT | LITS], LIT | CLA) :-
  mk_cf(LITS, CLA).

nst_orient(pm, HYP_L, HYP_R, HYP_L, HYP_R).
nst_orient(rw, HYP_L, HYP_R, HYP_L, HYP_R).
nst_orient(sr, HYP_L, HYP_R, HYP_R, HYP_L).

pull_ovs(_, [], FORM, FORM).
pull_ovs(CNT, [NUM | NUMS], FORM, NORM) :- 
  safe_subst_form(NUM, #(CNT), FORM, TEMP), 
  SUCC is CNT + 1,
  pull_ovs(SUCC, NUMS, TEMP, NORM).

pull_ovs(FORM, NORM) :- 
  ovs(FORM, OVS), 
  reverse(OVS, REV),
  pull_ovs(0, REV, FORM, NORM).

skolemize(SYMBS, DTH, FORM, SKM, AOC, NORM) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT), !, 
  (
    skolemize(SYMBS, DTH, FORM_A, SKM, AOC, NORM_A) -> 
    NORM_B = FORM_B
  ;
    skolemize(SYMBS, DTH, FORM_B, SKM, AOC, NORM_B), 
    NORM_A = FORM_A
  ), 
  NORM =.. [BCT, NORM_A, NORM_B].

skolemize(SYMBS, DTH, ~ FORM, SKM, AOC, ~ NORM) :- !,
  skolemize(SYMBS, DTH, FORM, SKM, AOC, NORM).

skolemize(SYMBS, DTH, ! FORM, SKM, AOC, ! NORM) :- !,
  SUCC is DTH + 1,
  skolemize(SYMBS, SUCC, FORM, SKM, AOC, NORM).

skolemize((SKM, LTH), DTH, ? FORM, SKM, AOC, NORM) :-  
  % ovs(FORM, NUMS), 
  % sort(NUMS, [0 | SORTED]), 
  % length(SORTED, LTH),
  % maplist(num_pred, SORTED, PREDS),
  % reverse(PREDS, REV), 
  % maplist_cut(mk('#'), REV, VARS), 
  % SKM_TERM =.. [SKM | VARS], 
  LTH =< DTH,
  e_skm_term(SKM, LTH, SKM_TERM),
  safe_subst_form(SKM_TERM, FORM, NORM),
  bind_vars((? FORM) => NORM, AOC), !.

e_skm_term(SKM, NUM, TERM) :- 
  range(desc, NUM, NUMS), 
  maplist_cut(mk('#'), NUMS, VARS), 
  TERM =.. [SKM | VARS].

last_id([inf(_,  _, ID, _) | _], ID).

pairs_insts(FI, [], FI, [], []).
pairs_insts(FI_I, [(SKM, AOC) | PAIRS], FI_O, [t(FI_I) | IDS], [add([aoc, SKM], t(FI_I), AOC) | INSTS]) :- 
  FI_T is FI_I + 1, 
  pairs_insts(FI_T, PAIRS, FI_O, IDS, INSTS).
  
unroll_hint(
  skm(PAIRS), FI_I, PID, SF, FI_O, t(FI_T), 
  [inf([skm], [PID | IDS], t(FI_T), SF) | INSTS]
) :- !, 
  pairs_insts(FI_I, PAIRS, FI_T, IDS, REV_INSTS),
  FI_O is FI_T + 1,
  reverse(REV_INSTS, INSTS).

unroll_hint(
  HINT, FI_I, PID, SF, FI_O, t(FI_I), 
  [inf([HINT], [PID], t(FI_I), SF)]
) :- 
  FI_O is FI_I + 1.

unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX) :- 
  format("Cannot unroll hint : ~w\n\n", unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX)).

unroll_hint(HINT, FI_I, SID, MID, SF, FI_O, t(FI_I), 
  [inf([HINT], [SID, MID], t(FI_I), SF)]
) :- 
  FI_O is FI_I + 1.

unroll_tree(FI, ntr(ID, _), FI, ID, []).

unroll_tree(
  FI_I, 
  utr(TREE, HINT, SF), 
  FI_O, 
  CID,
  INSTS   
) :- 
  unroll_tree(FI_I, TREE, FI_T, PID, SFX), 
  unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX),
  append(PFX, SFX, INSTS).

unroll_tree(
  FI_I, 
  btr(TREE_A, TREE_B, HINT, SF), 
  FI_O, 
  CID,
  INSTS   
) :- 
  unroll_tree(FI_I, TREE_A, FI_1, SID, SFX), 
  unroll_tree(FI_1, TREE_B, FI_2, MID, MFX), 
  unroll_hint(HINT, FI_2, SID, MID, SF, FI_O, CID, PFX),
  append([PFX, MFX, SFX], INSTS).

perm_cla(CLA_I, CLA_O) :- 
  cf_lits(CLA_I, LITS),
  permutation(LITS, PERM), 
  mk_cf(PERM, CLA_O).

eq_resolve(FORM_I, FORM_O) :- 
  inst_fas(FORM_I, BODY_I), 
  cf_lits(BODY_I, LITS),
  pluck(LITS, ~ (LHS = RHS), REST), 
  unify_with_occurs_check(LHS, RHS), 
  mk_cf(REST, BODY_O),
  close_lvs(BODY_O, FORM_O).
  
split_equiv(EQV, IMP) :- 
  inst_fas(EQV, LHS <=> RHS), 
  (
    BODY = (LHS => RHS) ;
    BODY = (RHS => LHS) 
  ),
  close_lvs(BODY, IMP).

conjunct(FORM, CONJ) :- 
  inst_fas(FORM, BODY), 
  conjunct_core(BODY, TEMP), 
  perm_cla(TEMP, PERM), 
  close_lvs(PERM, CONJ).

conjunct_core(FORM_A & FORM_B, NORM) :- !, 
  (
    conjunct_core(FORM_A, NORM) ;
    conjunct_core(FORM_B, NORM)
  ).
conjunct_core(FORM, FORM).

tree_conc(ntr(_, SF), SF).
tree_conc(utr(_, _, SF), SF).
tree_conc(btr(_, _, _, SF), SF).

combine_opts(none, OPT, OPT).
combine_opts(OPT, none, OPT).
combine_opts(some(VAL_A), some(VAL_B), some(VAL_A)) :- VAL_A == VAL_B.

compute_eqn_term(TERM_A, TERM_B, none) :- TERM_A == TERM_B, !.
compute_eqn_term(TERM_A, TERM_B, EQN) :-
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A =.. [FUN | TERMS_A],
  TERM_B =.. [FUN | TERMS_B],
  maplist(compute_eqn_term, TERMS_A, TERMS_B, EQNS), 
  foldl(combine_opts, EQNS, none, EQN), !.
compute_eqn_term(TERM_A, TERM_B, some((TERM_A, TERM_B))) :- \+ TERM_A == TERM_B.

compute_eqn_form(FORM_A, FORM_B, none) :- FORM_A == FORM_B, !.
compute_eqn_form(FORM_A, FORM_B, EQN) :- 
  uct_break(FORM_A, UCT, SUB_A), !,
  uct_break(FORM_B, UCT, SUB_B), 
  compute_eqn_form(SUB_A, SUB_B, EQN).
compute_eqn_form(FORM_A, FORM_B, EQN) :- 
  bct_break(FORM_A, BCT, SUB_LA, SUB_RA), !, 
  bct_break(FORM_B, BCT, SUB_LB, SUB_RB),
  compute_eqn_form(SUB_LA, SUB_LB, EQN_L),
  compute_eqn_form(SUB_RA, SUB_RB, EQN_R),
  combine_opts(EQN_L, EQN_R, EQN).
compute_eqn_form(FORM_A, FORM_B, EQN) :- 
  FORM_A =.. [REL | TERMS_A],
  FORM_B =.. [REL | TERMS_B],
  maplist(compute_eqn_term, TERMS_A, TERMS_B, EQNS), 
  foldl(combine_opts, EQNS, none, EQN).

mk_root(_, assume_negation, ~ FORM, rnm, ~ FORM).
% mk_root(_, shift_quantors, FORM, upnf, NORM) :- upnf(FORM, NORM).
mk_root(_, shift_quantors, FORM, bf_push, NORM) :- push_qtf(FORM, NORM).
mk_root(_, fof_nnf, FORM, fnnf, NORM) :- fnnf(FORM, NORM), !.
mk_root(_, variable_rename, FORM, rnm, FORM).
mk_root(_, fof_simplification, FORM, simp, NORM) :- esimp(FORM, NORM), !.
mk_root(_, split_conjunct, FORM, scj, NORM) :- conjunct(FORM, NORM).
mk_root(_, split_equiv, FORM, scj, NORM) :- split_equiv(FORM, NORM).
mk_root(_, cn, FORM, paratf, NORM) :- bool_norm(FORM, NORM), !.
% mk_root(_, distribute, FORM, dist, NORM) :- distribute(FORM, NORM), !.
mk_root(_, er, FORM, eqr, NORM) :- eq_resolve(FORM, NORM).

mk_root(_, ef, FORM_I, eqf, FORM_O) :- 
  inst_fas(FORM_I, BODY_I),
  cf_lits(BODY_I, LITS), 
  pluck(2, LITS, [LIT_L, LIT_R], REST),
  permutation([LIT_L, LIT_R], [LIT_A, LIT_B]),
  compute_eqn_form(LIT_A, LIT_B, some((LHS, RHS))), 
  mk_cf([~(LHS = RHS), LIT_B | REST], BODY_O), 
  close_lvs(BODY_O, FORM_O).
  
% mk_root(_, ef, FORM_I, pmt, FORM_O) :- 
%   inst_fas(FORM_I, BODY_I),
%   cf_lits(BODY_I, LITS), 
%   pluck(2, LITS, [LIT_A, LIT_B], REST),
%   unify_with_occurs_check(LIT_A, LIT_B), 
%   mk_cf([LIT_A | REST], BODY_O), 
%   close_lvs(BODY_O, FORM_O).
mk_root(FAS, skolemize, FORM, skm(PAIRS), NORM) :- 
  skolemize_many(FAS, FORM, PAIRS, NORM).

skolemize_many(_, FORM, [], FORM) :- \+ has_exists(FORM).
skolemize_many(FAS, FORM, [(SKM, AOC) | HINTS], NORM) :- 
  pluck(FAS, FA, REST),
  skolemize(FA, 0, FORM, SKM, AOC, TEMP), 
  skolemize_many(REST, TEMP, HINTS, NORM).

form_lits(FORM, LITS) :- 
  inst_fas(FORM, BODY),
  cf_lits(BODY, LITS).

% % mk_prem(RUL, CONC_B, TGT, HINT, TGT_A) *-> 
mk_prem(RUL, PREM_B, CONC, (sup, l), PREM_A) :- 
  member(RUL, [pm, rw]),
  cf_lits(CONC, LITS_C), 
  form_lits(PREM_B, LITS_B), 
  pluck(LITS_B, LIT_B, REST_B), 
  pluck(LITS_C, LIT_C, REST_C),
  erient_form(LIT_B, LHS = RHS), 
  mk_rw_form(LHS, RHS, LIT_C, LIT_A), 
  maplist(includes(REST_C), REST_B), 
  syinsert_lit(LIT_A, REST_C, TEMP),
  mk_cf(TEMP, PREM_A).

includes(LIST, ELEM) :- 
  member(ELEM, LIST). 

mk_root(_, RUL, FORM_A, FORM_B, (sup, l), FORM) :- 
  member(RUL, [pm, rw, sr]),
  inst_fas(FORM_A, BODY_A),
  cf_lits(BODY_A, LITS_A), 
  pluck(LITS_A, LIT_A, REST_A),
  inst_fas(FORM_B, BODY_B),
  cf_lits(BODY_B, LITS_B), 
  pluck(LITS_B, LIT_B, REST_B),
  erient_form(LIT_B, LHS = RHS), 
  mk_rw_form(LHS, RHS, LIT_A, LIT_N), 
  syunion_lits([LIT_N | REST_A], REST_B, LITS),
  mk_cf(LITS, BODY_N),
  close_lvs(BODY_N, FORM).

mk_root(_, RUL, FORM_A, FORM_B, res, FORM) :- 
  member(RUL, [rw, sr, pm]), 
  inst_fas(FORM_A, BODY_A),
  inst_fas(FORM_B, BODY_B),
  nst_orient(RUL, BODY_A, BODY_B, BODY_L, BODY_R),
  cf_lits(BODY_L, LITS_L), 
  cf_lits(BODY_R, LITS_R), 
  pluck(LITS_L, ~ ATOM_L, REST_L),
  pluck(LITS_R, ATOM_R, REST_R),
  unify_atom(ATOM_L, ATOM_R),
  exclude(syeq_lit(~ ATOM_L), REST_L, FILT_L),
  exclude(syeq_atom(ATOM_R), REST_R, FILT_R), 
  syunion_lits(FILT_L, FILT_R, LITS),
  mk_cf(LITS, CF),
  close_lvs(CF, FORM).
  
mk_root(_, rw, FORM, _, rnm, FORM).

target_tree(TGT, TREE, utr(TREE, HINT, CONC)) :-
  tree_conc(TREE, SUB),
  entails(SUB, TGT, HINT), 
  ground_all(c, TGT),
  bind_pars(TGT, CONC), !.

mk_tree_fwd(CTX, _, ID, ntr(ID, FORM)) :- 
  atom(ID), !,
  get_assoc(ID, CTX, + FORM).

mk_tree_fwd(CTX, FAS, inference(distribute, _, [ANT]), utr(utr(TREE, bf_pull, NORM), bf_dist, CONC)) :- !, 
  mk_tree_fwd(CTX, FAS, ANT, TREE), 
  tree_conc(TREE, SUB), 
  pull_qtf(SUB, NORM), 
  distribute(NORM, CONC).

mk_tree_fwd(CTX, FAS, inference(RUL, _, [ANT]), utr(TREE, HINT, CONC)) :- 
  % format("Build : ~w\n\n", inference(RUL, _, [ANT])),
  mk_tree_fwd(CTX, FAS, ANT, TREE), 
  tree_conc(TREE, SUB), 
  mk_root(FAS, RUL, SUB, HINT, CONC).

mk_tree_fwd(CTX, FAS, inference(RUL, _, [ANT_A, ANT_B]), btr(TREE_A, TREE_B, HINT, CONC)) :- 
  % format("ANT : ~w\n\n", inference(RUL, _, [ANT_A, ANT_B])),
  mk_tree_fwd(CTX, FAS, ANT_A, TREE_A),
  tree_conc(TREE_A, CONC_A), 
  mk_tree_fwd(CTX, FAS, ANT_B, TREE_B), 
  tree_conc(TREE_B, CONC_B), 
  mk_root(FAS, RUL, CONC_A, CONC_B, HINT, CONC).

mk_tree_fwd(CTX, TGT, FAS, ANT, TREE) :- 
  mk_tree_fwd(CTX, FAS, ANT, SUB), 
  target_tree(TGT, SUB, TREE).
  
mk_tree_bwd(CTX, TGT, FAS, ANT, TREE) :- 
  (
    ANT = inference(RUL, _, [ANT_A, ANT_B]),
    % format("ANT : ~w\n\n", ANT),
    mk_tree_fwd(CTX, FAS, ANT_B, TREE_B), 
    tree_conc(TREE_B, CONC_B), 
    mk_prem(RUL, CONC_B, TGT, HINT, TGT_A) 
  ) *->
  mk_tree_bwd(CTX, TGT_A, FAS, ANT_A, TREE_A),
  ground_all(c, TGT),
  bind_pars(TGT, CONC),
  TREE = btr(TREE_A, TREE_B, HINT, CONC)
;
  mk_tree_fwd(CTX, FAS, ANT, SUB), 
  target_tree(TGT, SUB, TREE).

m_tuplize(TERM, (ID, TYPE, FORM, none)) :- 
  TERM =.. [LNG, ID, TYPE, TF], 
  tf_form(LNG, TF, TEMP), 
  (
    TYPE = conjecture -> 
    FORM = (~ TEMP) ;
    FORM = TEMP
  ).

e_tuplize(TERM, (ID, TYPE, FORM, ANT)) :- 
  (
    TERM =.. [LNG, ID, TYPE, TF], ANT = none ;
    TERM =.. [LNG, ID, TYPE, TF, ANT] ;
    TERM =.. [LNG, ID, TYPE, TF, ANT, [_]]
  ), 
  tf_form(LNG, TF, TEMP), 
  (
    TYPE = conjecture -> 
    FORM = (~ TEMP) ;
    FORM = TEMP
  ).

% e_tuplize(TERM, (ID, TYPE, FORM, ANT)) :- 
%   (
%     TERM =.. [LNG, ID, TYPE, TF, ANT] ;
%     TERM =.. [LNG, ID, TYPE, TF, ANT, [_]]
%   ), 
%   tf_form(LNG, TF, FORM).

cperm_aux([], _).
cperm_aux([LIT | LITS_A], LITS_B) :- 
  (
    LIT = $false ;
    LIT = (~ $true) ; 
    LIT = (~ TERM_A = TERM_B), 
    unify_with_occurs_check(TERM_A, TERM_B)
  ; 
    erient_lit(LIT, EQV),
    member(EQV, LITS_B)
  ), 
  cperm_aux(LITS_A, LITS_B).

cperm(FORM_A, FORM_B) :- 
  inst_fas_exs(FORM_B, BODY_B), 
  inst_fas(FORM_A, BODY_A),
  cf_lits(BODY_A, LITS_A),
  cf_lits(BODY_B, LITS_B),
  cperm_aux(LITS_A, LITS_B).

entails(SF, SF, rnm).
entails(PREM, CONC, para) :- syeq_form(PREM, CONC).
entails(PREM, CONC, bf) :- bfe(((0, (+ PREM)), (1, (- CONC)), (_, 0, 2))).
entails(PREM, CONC, bf2) :- bfe2(((0, (+ PREM)), (1, (- CONC)), (_, 0, 2))).
% entails(PREM, CONC, bf_push) :- bf_push((unr((0, (+ PREM))), unr((1, (- CONC))), (_, 0, 2))).
entails(FORM_A, FORM_B, cperm) :- cperm(FORM_A, FORM_B).

def_pred(FORM, PRED) :- 
  strip_fas(FORM, _, ATOM <=> _), 
  ATOM =.. [PRED | _].

e_tup_insts(
  _,
  (_, TYPE, _, file(_, _)),
  []
) :- !,
  axiomatic(TYPE).

e_tup_insts(
  _,
  (CID, plain, FORM, introduced(definition)),
  [add([def, PRED], CID, FORM)]
) :- !,
  def_pred(FORM, PRED).

e_tup_insts(
  _,
  (CID, _, FORM, inference(apply_def, _, [ANT_A, ANT_B])),
  [inf([dff], [ID_A, ID_B], CID, FORM)]
) :- !, 
  (
    atom(ANT_A), ID_A = ANT_A ;
    ANT_A = inference(assume_negation, _, [ID_A])
  ), 
  (
    atom(ANT_B), ID_B = ANT_B ;
    ANT_B = inference(assume_negation, _, [ID_B])
  ).

e_tup_insts(
  _,
  (CID, TYPE, FORM, PID),
  [inf([parac, dtrx], [PID], CID, FORM)]
) :- 
  axiomatic(TYPE),
  atom(PID), !.
  
e_tup_insts(
  CTX,
  (CID, TYPE, FORM, ANT),
  INSTS 
) :- 
  e_skm_pairs(FORM, FAS),
  inst_fas(0, FORM, TGT), 
  timed_call( 
    10,
    mk_tree_bwd(CTX, TGT, FAS, ANT, TREE),
    (
      write("Backward search failed, switch to forward search\n"),
      timed_call(
        60, 
        mk_tree_fwd(CTX, TGT, FAS, ANT, TREE),
        (
          write("Forward search failed, print failure trace\n"),
          report_sol_failure(CTX, (CID, TYPE, FORM, ANT)),
          % throw(solution_failed),
          true
        )
      )
    )
  ),
  unroll_tree(0, TREE, SIZE, PID, REV), 
  reverse(REV, PFX),
  mk_dels(SIZE, DELS), 
  append(PFX, [inf([rnm], [PID], CID, FORM) | DELS], INSTS).

e_tup_insts(CTX, ANT, _) :- 
  report_sol_failure(CTX, ANT),
  throw(solution_failed).

e_skm_pairs(FORM, PAIRS) :- 
  form_funaris(FORM, FAS), 
  include(is_skm_pair, FAS, PAIRS).
  
is_skm_pair((SKM, _)) :- 
  atom_concat(esk, _, SKM) ;
  atom_concat(skolemFOFtoCNF, _, SKM).

report_sol_failure(CTX, ANT) :- 
  write("\nSolution failed, annotaition : "), 
  write(ANT), nl, nl,
  % write("\nInference failed, premises :\n\n"),
  % write_list(PREMS), 
  % format("\nInference failed, conclusion : ~w\n\n", CONC), 
  open("debug_trace.pl", write, Stream), 
  write(Stream, ":- [main].\n\n"), 
  format(Stream, '~w.\n\n', debug_ctx(CTX)), 
  format(Stream, '~w.\n\n', debug_ant(ANT)), 
  close(Stream).


%%%%%%%%%%%%%%%% METIS %%%%%%%%%%%%%%%%

m_tup_insts(
 PIDS,
 CTX,
 (CID, TYPE, FORM, none),
 INSTS
) :- 
  axiomatic(TYPE), !, 
  (
    get_assoc(CID, CTX, TEMP) -> 
    TEMP = (+ FORM), 
    INSTS = [] 
  ;
    INSTS = [inf([parac], PIDS, CID, FORM)]
  ).

m_tup_insts(
  _,
  CTX,
  (CID, plain, FORM, inference(clausify, [], [PID])),
  INSTS
) :- 
  ANT = 
    inference(
      distribute, _,
      [
        inference(
          shift_quantors, _,
          [
            inference(
              skolemize, _, 
              [
                inference(fof_nnf, _, [PID])
              ]
            )
          ]
        )
      ]
    ),
  e_skm_pairs(FORM, FAS),
  inst_fas(0, FORM, TGT), 
      timed_call(
        60, 
        mk_tree_fwd(CTX, TGT, FAS, ANT, TREE),
        (
          write("Forward search failed, print failure trace\n"),
          report_sol_failure(CTX, (CID, plain, FORM, ANT)),
          % throw(solution_failed),
          true
        )
      ),
  unroll_tree(0, TREE, SIZE, NID, REV), 
  reverse(REV, PFX),
  mk_dels(SIZE, DELS), 
  append(PFX, [inf([rnm], [NID], CID, FORM) | DELS], INSTS).
  

m_tup_insts(
  _,
  _,
  (ID, plain, FORM, ANT),
  [inf(HINTS, IDS, ID, FORM)]
) :- 
  ant_ids_hints(ANT, IDS, HINTS).

ant_ids_hints(inference(subst, [], [PID : _]), [PID], [subst]).

ant_ids_hints(inference(RUL, _, IDS), IDS, [HINT]) :- 
  RUL \= subst, 
  metis_rul_hint(RUL, HINT).

ant_ids_hints(introduced(tautology, [refl, _]), [], [refl]).

ant_ids_hints(introduced(tautology, [equality, _]), [], [eq]).

ant_ids_hints(introduced(RUL), [], [HINT]) :- 
  RUL \= tautology,
  metis_rul_hint(RUL, HINT).

metis_rul_hint(strip, strip).
metis_rul_hint(canonicalize, cnn).
metis_rul_hint(specialize, rnm).
metis_rul_hint(negate, neg).
metis_rul_hint(simplify, res).
metis_rul_hint(resolve, res).
metis_rul_hint(conjunct, mscj).

string_id(STR, ID) :- 
  split_string(STR, ",(", " ", [LNG, ID_STR | _]), 
  member(LNG, ["cnf", "fof"]),
  atom_string(ID, ID_STR).

sorted_ids(TSTP, IDS) :-
  file_strings(TSTP, STRS),
  maplist_try(string_id, STRS, IDS).

tup_ctx((ID, _, FORM, _), CTX_I, CTX_O) :- 
%   TYPE = conjecture -> 
%   put_assoc(ID, CTX_I, + ~ FORM, CTX_O)
% ;
  put_assoc(ID, CTX_I, + FORM, CTX_O).

tups_ctx(TUPS, CTX) :- 
  empty_assoc(EMP), 
  foldl(tup_ctx, TUPS, EMP, CTX).

solve(v, PIDS, TSTP, SOL) :- 
  trim_consult(TSTP),
  findall((ID, IDS, TF, RUL), fof(ID, IDS, TF, RUL), UNSORTED),
  predsort(vampire_cmp_hints, UNSORTED, SORTED), 
  maplist_cut(v_tup_inst(PIDS), SORTED, INSTS), 
  % write("Computing deletions...\n"),
  insert_dels(INSTS, _, DELETED),
  % write("Deletions found.\n"),
  reduce_gaocs(DELETED, SOL),
  % write("Solution found.\n"),
  true.

solve(e, _, TSTP, SOL) :- 
  trim_read(TSTP, TEMP), 
  maplist_cut(e_tuplize, TEMP, TUPS),
  tups_ctx(TUPS, CTX),
  maplist_cut(e_tup_insts(CTX), TUPS, INSTSS),
  append(INSTSS, SOL),
  true.

solve(m, PIDS, TSTP, SOL) :- 
  trim_read(TSTP, TEMP), 
  maplist_cut(e_tuplize, TEMP, TUPS),
  tups_ctx(TUPS, CTX),
  maplist_cut(m_tup_insts(PIDS, CTX), TUPS, INSTSS),
  append(INSTSS, SOL),
  true.

% solve(m, PIDS, TSTP, SOL) :- 
%   trim_read(TSTP, TEMP),
%   maplist_cut(m_tuplize, TEMP, TUPS),
%   maplist_cut(metis_tuple_insts(PIDS), TUPS, INSTSS),
%   append(INSTSS, SOL),
%   true.
