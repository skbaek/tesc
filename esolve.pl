% :- module(esolve, [esolve/2, tup_insts/3, mk_tree_fwd/4]).
:- [basic].
:- [tstp].

par_pdx_args(PAR, PDX, ARGS) :- 
  \+ var(PAR),
  PAR =.. [FUN | ARGS],
  atom(FUN),
  atom_concat('@', TEMP, FUN),
  atom_number(TEMP, PDX).

pdx_in(EXP, PDX) :- 
  sub_term(TERM, EXP), 
  % TERM = @(NUM).
  par_pdx_args(TERM, PDX, _).

maxpdx(EXP, MAX) :- 
  findall(NUM, pdx_in(EXP, NUM), NUMS), 
  max_list(NUMS, MAX).

map_par(_, #(NUM), #(NUM)) :- !.
map_par(GOAL, ^(FUN, TERMS_I), ^(FUN, TERMS_O)) :- !, 
  maplist_cut(map_par(GOAL), TERMS_I, TERMS_O).
map_par(GOAL, TERM_I, TERM_O) :- 
  par_pdx_args(TERM_I, PDX, []) -> 
  call(GOAL, PDX, TERM_O) 
;
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(map_par(GOAL), TERMS_I, TERMS_O),
  TERM_O =.. [FUN | TERMS_O]. 

bind_par(DEP, IDX, IDX, #(DEP)).
bind_par(_, IDX_A, IDX_B, PAR) :- 
  IDX_A \= IDX_B,
  mk_par(IDX_B, [], PAR).

bind_pars_term(IDX, DEP, TERM_I, TERM_O) :-
  map_par(bind_par(DEP, IDX), TERM_I, TERM_O).

bind_all_pars(FORM_I, FORM_O) :-
  maxpdx(FORM_I, PDX) -> 
  map_form(bind_pars_term(PDX), 0, FORM_I, TEMP), 
  bind_all_pars($fa(TEMP), FORM_O)
;
  FORM_O = FORM_I.

entails(SF, SF, rnm).
entails(PREM, CONC, para) :- para(((prem, PREM), (conc, CONC), (_, 0))).
entails(PREM, CONC, para_e1) :- para_e1(((prem, $pos(PREM)), (conc, $neg(CONC)), (_, 0))).
% entails(PREM, CONC, para_e2) :- para_e2(((prem, $pos(PREM)), (conc, $neg(CONC)), (_, 0))).
entails(PREM, CONC, eqr) :- eqr((prem, $pos(PREM)), (conc, $neg(CONC)), (_, 0)).

tree_conc(ntr(_, SF), SF).
tree_conc(utr(_, _, SF), SF).
tree_conc(btr(_, _, _, SF), SF).

incr_vdx(DEP, IDX, #(NEW)) :- 
  IDX < DEP -> 
  NEW = IDX ;
  num_succ(IDX, NEW). 

incr_vdx_term(DEP, TERM, NORM) :-
  map_var(incr_vdx(DEP), TERM, NORM).

incr_vdx_form(FORM, NORM) :-
  map_form(incr_vdx_term, 0, FORM, NORM). 
 
pull_qtf_bct(BCT, $fa(FORM_A), FORM_B, $fa(NORM)) :- !,
  incr_vdx_form(FORM_B, FORM_N), 
  pull_qtf_bct(BCT, FORM_A, FORM_N, NORM).
pull_qtf_bct(BCT, FORM_A, $fa(FORM_B), $fa(NORM)) :- !,
  incr_vdx_form(FORM_A, FORM_N), 
  pull_qtf_bct(BCT, FORM_N, FORM_B, NORM).
pull_qtf_bct(BCT, FORM_A, FORM_B, NORM) :- 
  FORM_A \= $fa(_),
  FORM_B \= $fa(_),
  apply_bop(BCT, FORM_A, FORM_B, NORM).
  
pull_qtf(FORM, NORM)  :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !, 
  pull_qtf(FORM_A, NORM_A), 
  pull_qtf(FORM_B, NORM_B), 
  pull_qtf_bct(BCT, NORM_A, NORM_B, NORM).
pull_qtf($fa(FORM), $fa(NORM)) :- !, 
  pull_qtf(FORM, NORM).
pull_qtf(FORM, FORM). 

target_tree(TGT, TREE, utr(TREE, HINT, CONC)) :-
  tree_conc(TREE, SUB),
  entails(SUB, TGT, HINT), 
  ground_all(^(c,[]), TGT),
  bind_all_pars(TGT, CONC), !.

mk_tree_fwd(CTX, inference(distribute, _, [ANT]), utr(utr(TREE, para_pull, NORM), para_dist, CONC)) :- !, 
  mk_tree_fwd(CTX, ANT, TREE), 
  tree_conc(TREE, SUB), 
  pull_qtf(SUB, NORM),
  distribute(NORM, CONC).

mk_tree_fwd(CTX, inference(RUL, _, [ANT]), utr(TREE, HINT, CONC)) :- 
  % format("Build : ~w\n\n", inference(RUL, _, [ANT])),
  mk_tree_fwd(CTX, ANT, TREE), 
  tree_conc(TREE, SUB), 
  mk_root(RUL, SUB, HINT, CONC).

mk_tree_fwd(CTX, inference(RUL, _, [ANT_A, ANT_B]), btr(TREE_A, TREE_B, HINT, CONC)) :- 
  % format("ANT : ~w\n\n", inference(RUL, _, [ANT_A, ANT_B])),
  mk_tree_fwd(CTX, ANT_A, TREE_A),
  tree_conc(TREE_A, CONC_A), 
  mk_tree_fwd(CTX, ANT_B, TREE_B), 
  tree_conc(TREE_B, CONC_B), 
  mk_root(RUL, CONC_A, CONC_B, HINT, CONC).

mk_tree_fwd(CTX, ID, ntr(ID, FORM)) :- 
  atom(ID), !,
  get_assoc(ID, CTX, $pos(FORM)).

mk_tree_fwd(CTX, TGT, ANT, TREE) :- 
  mk_tree_fwd(CTX, ANT, SUB), 
  target_tree(TGT, SUB, TREE).

mk_cf([], $false).
mk_cf([LIT], LIT) :- !.
mk_cf([LIT | LITS], $or(LIT, CLA)) :-
  mk_cf(LITS, CLA).

bind_lvs(_, []).
bind_lvs(NUM, [#(NUM) | VARS]) :- 
  num_succ(NUM, SUCC),
  bind_lvs(SUCC, VARS).

close_lvs(BODY, FORM) :-
  term_variables(BODY, VARS), 
  % replace_lvs_form(VARS, 0, BODY, TEMP), 
  bind_lvs(0, VARS),
  length(VARS, NUM), 
  add_fas(NUM, BODY, FORM).

conjunct(FORM, CONJ) :- 
  inst_with_lvs(FORM, BODY), 
  conjunct_core(BODY, TEMP), 
  %perm_cla(TEMP, PERM),
  close_lvs(TEMP, CONJ).

conjunct_core($and(FORM_A, FORM_B), NORM) :- !, 
  (
    conjunct_core(FORM_A, NORM) ;
    conjunct_core(FORM_B, NORM)
  ).
conjunct_core(FORM, FORM).

split_equiv(EQV, IMP) :- 
  strip_fas(EQV, NUM, $iff(LHS, RHS)), 
  (
    BODY = $imp(LHS, RHS) ;
    BODY = $imp(RHS, LHS) 
  ),
  add_fas(NUM, BODY, IMP).
  % inst_with_lvs(EQV, $iff(LHS, RHS)), 
  % (
  %   BODY = $imp(LHS, RHS) ;
  %   BODY = $imp(RHS, LHS) 
  % ),
  % close_lvs(BODY, IMP).

eq_resolve(FORM_I, FORM_O) :- 
  inst_with_lvs(FORM_I, BODY_I), 
  cf_lits(BODY_I, LITS),
  pluck(LITS, $not(LHS = RHS), REST), 
  unify_with_occurs_check(LHS, RHS), 
  mk_cf(REST, BODY_O),
  close_lvs(BODY_O, FORM_O).
combine_opts(none, OPT, OPT).
combine_opts(OPT, none, OPT).
combine_opts(some(VAL_A), some(VAL_B), some(VAL_A)) :- VAL_A == VAL_B.

compute_eqn_term(TERM_A, TERM_B, none) :- TERM_A == TERM_B, !.
compute_eqn_term(TERM_A, TERM_B, EQN) :-
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A = ^(FUN, TERMS_A),
  TERM_B = ^(FUN, TERMS_B),
  maplist(compute_eqn_term, TERMS_A, TERMS_B, EQNS), 
  foldl(combine_opts, EQNS, none, EQN), !.
compute_eqn_term(TERM_A, TERM_B, some((TERM_A, TERM_B))) :- \+ TERM_A == TERM_B.

compute_eqn_form(FORM_A, FORM_B, none) :- FORM_A == FORM_B, !.
compute_eqn_form(FORM_A, FORM_B, EQN) :- 
  decom_uct(FORM_A, UCT, SUB_A), !,
  decom_uct(FORM_B, UCT, SUB_B),
  compute_eqn_form(SUB_A, SUB_B, EQN).
compute_eqn_form(FORM_A, FORM_B, EQN) :- 
  decom_bct(FORM_A, BCT, SUB_LA, SUB_RA), !, 
  decom_bct(FORM_B, BCT, SUB_LB, SUB_RB),
  compute_eqn_form(SUB_LA, SUB_LB, EQN_L),
  compute_eqn_form(SUB_RA, SUB_RB, EQN_R),
  combine_opts(EQN_L, EQN_R, EQN).
compute_eqn_form(FORM_A, FORM_B, EQN) :- 
  FORM_A =.. [REL | TERMS_A],
  FORM_B =.. [REL | TERMS_B],
  maplist(compute_eqn_term, TERMS_A, TERMS_B, EQNS), 
  foldl(combine_opts, EQNS, none, EQN).

skolemize(DTH, FORM, SKM, ARI, AOC, NORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !,
  (
    skolemize(DTH, FORM_A, SKM, ARI, AOC, NORM_A) -> 
    NORM_B = FORM_B
  ;
    skolemize(DTH, FORM_B, SKM, ARI, AOC, NORM_B), 
    NORM_A = FORM_A
  ), 
  apply_bop(BCT, NORM_A, NORM_B, NORM).

skolemize(DTH, $not(FORM), SKM, ARI, AOC, $not(NORM)) :- !,
  skolemize(DTH, FORM, SKM, ARI, AOC, NORM).

skolemize(DTH, $fa(FORM), SKM, ARI, AOC, $fa(NORM)) :- !,
  num_succ(DTH, SUCC),
  skolemize(SUCC, FORM, SKM, ARI, AOC, NORM).

skolemize(DTH, $ex(FORM), SKM, DTH, AOC, NORM) :-  
  % ovs(FORM, NUMS), 
  % sort(NUMS, [0 | SORTED]), 
  % length(SORTED, LTH),
  % maplist(num_pred, SORTED, PREDS),
  % reverse(PREDS, REV), 
  % maplist_cut(mk('#'), REV, VARS), 
  % SKM_TERM =.. [SKM | VARS], 
  % LTH =< DTH,
  e_skm_term(SKM, DTH, SKM_TERM),
  substitute_form(safe, SKM_TERM, FORM, NORM),
  bind_vars($imp($ex(FORM), NORM), AOC), !.

positive(NUM) :- 0 < NUM.

ovs($not(FORM), OVS) :- !, ovs(FORM, OVS).
ovs(FORM, OVS) :- 
  decom_qtf(FORM, _, SUB), !, 
  ovs(SUB, TEMP),
  include(positive, TEMP, FILT), 
  maplist(num_pred, FILT, OVS).
ovs(FORM, OVS) :- 
  decom_bct(FORM, _, FORM_A, FORM_B), !, 
  ovs(FORM_A, BND_A),
  ovs(FORM_B, BND_B),
  union(BND_A, BND_B, OVS).
ovs(FORM, OVS) :- 
  findall(NUM, is_vdx_in(NUM, FORM), TEMP), 
  sort(TEMP, OVS), !.

is_vdx_in(NUM, EXP) :- 
  sub_term(X, EXP),
  \+ var(X),
  X = #(NUM).

minvar(FORM, MIN) :- 
  ovs(FORM, NUMS),
  min_list(NUMS, MIN).
bind_vars(FORM_I, FORM_O) :-
  minvar(FORM_I, IDX) ->
  map_form(bind_var_term(IDX), 0, FORM_I, TEMP), 
  bind_vars($fa(TEMP), FORM_O)
;
  FORM_O = FORM_I.

bind_var(IDX, CNT, NUM, TERM) :- 
  NUM is IDX + CNT -> 
  TERM = #(CNT)
;
  TERM = #(NUM).

bind_var_term(IDX, CNT, TERM_I, TERM_O) :-
  map_var(bind_var(IDX, CNT), TERM_I, TERM_O).

e_skm_term(SKM, NUM, ^(SKM, VARS)) :-
  range(desc, NUM, NUMS), 
  maplist_cut(mk('#'), NUMS, VARS), 
  % TERM =.. [SKM | VARS],
  true.

has_exists($ex(_)).
has_exists($fa(FORM)) :- has_exists(FORM).
has_exists($and(FORM_A, FORM_B)) :- has_exists(FORM_A) ; has_exists(FORM_B).
has_exists($or(FORM_A, FORM_B)) :- has_exists(FORM_A) ; has_exists(FORM_B).

skolemize_many(FORM, [], FORM) :- \+ has_exists(FORM).
skolemize_many(FORM, [(SKM, ARI, AOC) | HINTS], NORM) :- 
  skolemize(0, FORM, SKM, ARI, AOC, TEMP), 
  skolemize_many(TEMP, HINTS, NORM).

syeq_lit($not(ATOM_A), $not(ATOM_B)) :- !, 
  syeq_atom(ATOM_A, ATOM_B).
syeq_lit(LIT_A, LIT_B) :- 
  syeq_atom(LIT_A, LIT_B).

syeq_atom(FORM_A, FORM_B) :- FORM_A == FORM_B.
syeq_atom(LHS_A = RHS_A, LHS_B = RHS_B) :- 
  LHS_A == RHS_B, 
  RHS_A == LHS_B.

symember_lit(LIT, LITS) :- 
  member(EQV, LITS), 
  syeq_lit(LIT, EQV).

syinsert_lit(LIT, LITS_I, LITS_O) :- 
  symember_lit(LIT, LITS_I) -> 
  LITS_I = LITS_O
;
  [LIT | LITS_I] = LITS_O.

syunion_lits([], LITS, LITS).
syunion_lits([LIT | LITS_A], LITS_B, LITS) :- 
  syunion_lits(LITS_A, LITS_B, TEMP), 
  syinsert_lit(LIT, TEMP, LITS).

mk_rw_form(LHS, RHS, $not(FORM), $not(RW)) :- !,
  mk_rw_form(LHS, RHS, FORM, RW).

mk_rw_form(LHS, RHS, $or(FORM_L, FORM_R), $or(RW_L, RW_R)) :- !,
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

mk_rw_term(FROM, TO, TERM_I, TERM_O) :- 
  \+ var(TERM_I),
  (
    unify_with_occurs_check(FROM, TERM_I),
    TO = TERM_O
  ; 
    TERM_I = ^(FUN, TERMS_I), 
    mk_rw_terms(FROM, TO, TERMS_I, TERMS_O), 
    TERM_O = ^(FUN, TERMS_O) 
  ).

nst_orient(pm, HYP_L, HYP_R, HYP_L, HYP_R).
nst_orient(rw, HYP_L, HYP_R, HYP_L, HYP_R).
nst_orient(sr, HYP_L, HYP_R, HYP_R, HYP_L).

unify_atom(ATOM_A, ATOM_B) :- 
  erient_form(ATOM_A, TEMP), 
  unify_with_occurs_check(TEMP, ATOM_B).

fold_definition(NUM, ATOM, BODY, $not(FORM), $not(NORM)) :- 
  fold_definition(NUM, ATOM, BODY, FORM, NORM).

fold_definition(NUM, ATOM, BODY, FORM, NORM) :- 
  decom_qtf(FORM, QTF, SUB_FORM), 
  mk_par(NUM, [], PAR),
  substitute_form(fast, PAR, SUB_FORM, TEMP_FORM), 
  num_succ(NUM, SUCC), 
  fold_definition(SUCC, ATOM, BODY, TEMP_FORM, TEMP_NORM), 
  map_form(bind_pars_term(NUM), 0, TEMP_NORM, SUB_NORM), 
  apply_uop(QTF, SUB_NORM, NORM).

fold_definition(NUM, ATOM, BODY, FORM, NORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), 
  (
    fold_definition(NUM, ATOM, BODY, FORM_A, NORM_A), 
    NORM_B = FORM_B 
  ;
    fold_definition(NUM, ATOM, BODY, FORM_B, NORM_B), 
    NORM_A = FORM_A 
  ),
  apply_bop(BCT, NORM_A, NORM_B, NORM).

fold_definition(_, ATOM, BODY, BODY, ATOM).

mk_root(assume_negation, $not(FORM), rnm, $not(FORM)).
mk_root(shift_quantors, FORM, para_push, NORM) :- push_qtf(FORM, NORM).
mk_root(fof_nnf, FORM, fnnf, NORM) :- fnnf(FORM, NORM), !.
mk_root(evalgc, FORM, rnm, FORM).
mk_root(variable_rename, FORM, rnm, FORM).
mk_root(fof_simplification, FORM, simp, NORM) :- esimp(FORM, NORM), !.
mk_root(split_conjunct, FORM, scj, NORM) :- conjunct(FORM, NORM).
mk_root(split_equiv, FORM, speq, NORM) :- split_equiv(FORM, NORM).
mk_root(cn, FORM, paratf, NORM) :- bool_norm(FORM, NORM), !.
mk_root(er, FORM, eqr, NORM) :- eq_resolve(FORM, NORM).

mk_root(ef, FORM_I, eqf, FORM_O) :- 
  inst_with_lvs(FORM_I, BODY_I),
  cf_lits(BODY_I, LITS), 
  pluck(2, LITS, [LIT_L, LIT_R], REST),
  permutation([LIT_L, LIT_R], [LIT_A, LIT_B]),
  compute_eqn_form(LIT_A, LIT_B, some((LHS, RHS))), 
  mk_cf([$not(LHS = RHS), LIT_B | REST], BODY_O), 
  close_lvs(BODY_O, FORM_O).
  
mk_root(ef, FORM_I, sbsm, FORM_O) :- 
  inst_with_lvs(FORM_I, BODY_I),
  cf_lits(BODY_I, LITS), 
  pluck(2, LITS, [LIT_A, LIT_B], REST),
  unify_with_occurs_check(LIT_A, LIT_B), 
  mk_cf([LIT_A | REST], BODY_O), 
  close_lvs(BODY_O, FORM_O).

mk_root(skolemize, FORM, skm(PAIRS), NORM) :- 
  skolemize_many(FORM, PAIRS, NORM).

mk_root(apply_def, FORM_A, FORM_B, dff, FORM_C) :- !, 
  % inst_with_pars(0, FORM_A, _, BODY_A),
  inst_with_lvs(FORM_B, $iff(ATOM, BODY_B)), 
  fold_definition(0, ATOM, BODY_B, FORM_A, FORM_C),
  ground(FORM_C),
  % bind_all_pars(TEMP, FORM_C).
  true.

mk_root(RUL, FORM_A, FORM_B, (sup, l), FORM) :- 
  member(RUL, [pm, rw, sr]),
  inst_with_lvs(FORM_A, BODY_A),
  cf_lits(BODY_A, LITS_A), 
  inst_with_lvs(FORM_B, BODY_B),
  cf_lits(BODY_B, LITS_B),  
  pluck(LITS_B, LIT_B, REST_B),
  orient_equation(LIT_B, LHS = RHS),
  pluck(LITS_A, LIT_A, REST_A),
  mk_rw_form(LHS, RHS, LIT_A, LIT_N), 
  syunion_lits([LIT_N | REST_A], REST_B, LITS),
  mk_cf(LITS, BODY_N),
  close_lvs(BODY_N, FORM).

mk_root(RUL, FORM_A, FORM_B, res, FORM) :- 
  member(RUL, [rw, sr, pm]), 
  inst_with_lvs(FORM_A, BODY_A),
  inst_with_lvs(FORM_B, BODY_B),
  nst_orient(RUL, BODY_A, BODY_B, BODY_L, BODY_R),
  cf_lits(BODY_L, LITS_L), 
  cf_lits(BODY_R, LITS_R), 
  pluck(LITS_L, $not(ATOM_L), REST_L),
  pluck(LITS_R, ATOM_R, REST_R),
  unify_atom(ATOM_L, ATOM_R),
  exclude(syeq_lit($not(ATOM_L)), REST_L, FILT_L),
  exclude(syeq_atom(ATOM_R), REST_R, FILT_R), 
  syunion_lits(FILT_L, FILT_R, LITS),
  mk_cf(LITS, CF),
  close_lvs(CF, FORM).
  
mk_root(rw, FORM, _, rnm, FORM).

def_pred_ari(FORM, PRED, ARI) :- 
  strip_fas(FORM, _, $iff(ATOM, _)), 
  ATOM =.. [PRED | TERMS],
  length(TERMS, ARI).

inst_fas(NUM, $fa(FORM), BODY) :- !,
  num_succ(NUM, SUCC),
  mk_par(NUM, [], PAR),
  substitute_form(fast, PAR, FORM, TEMP),
  inst_fas(SUCC, TEMP, BODY).
inst_fas(_, FORM, FORM) :- FORM \= $fa(_).

pairs_insts(FI, [], FI, [], []).
pairs_insts(FI_I, [(SKM, ARI, AOC) | PAIRS], FI_O, [t(FI_I) | IDS], [skm(SKM, ARI, t(FI_I), AOC) | INSTS]) :- 
  num_succ(FI_I, FI_T), 
  pairs_insts(FI_T, PAIRS, FI_O, IDS, INSTS).
  
unroll_hint(
  skm(PAIRS), FI_I, PID, SF, FI_O, t(FI_T), 
  [inf(skm, [PID | IDS], t(FI_T), SF) | INSTS]
) :- !, 
  pairs_insts(FI_I, PAIRS, FI_T, IDS, REV_INSTS),
  num_succ(FI_T, FI_O),
  reverse(REV_INSTS, INSTS).

unroll_hint(
  HINT, FI_I, PID, SF, FI_O, t(FI_I), 
  [inf(HINT, [PID], t(FI_I), SF)]
) :- 
  num_succ(FI_I, FI_O).

unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX) :- 
  format("Cannot unroll hint : ~w\n\n", unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX)).

unroll_hint(HINT, FI_I, SID, MID, SF, FI_O, t(FI_I), 
  [inf(HINT, [SID, MID], t(FI_I), SF)]
) :- 
  num_succ(FI_I, FI_O).

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

tup_insts(
  _,
  (CID, TYPE, FORM, file(_, _)),
  [inf(orig, $orig, CID, FORM)]
) :- !,
  axiomatic(TYPE).

tup_insts(
  _, 
  (CID, plain, FORM, introduced(definition)),
  [add([def, PRD, ARI], CID, FORM)]
) :- !,
  def_pred_ari(FORM, PRD, ARI).

tup_insts(
  _,
  (CID, TYPE, FORM, PID),
  [inf(orig, [PID], CID, FORM)]
) :- 
  axiomatic(TYPE),
  atom(PID), !.
  
tup_insts(
  CTX,
  (CID, TYPE, FORM, ANT),
  INSTS 
) :- 
  % format("Solving for ID : ~w\n\n", CID),
  inst_fas(0, FORM, TGT), 
  timed_call(
    20, 
    mk_tree_fwd(CTX, TGT, ANT, TREE),
    (
      write("Forward search failed, print failure trace\n"),
      report_sol_failure(CTX, (CID, TYPE, FORM, ANT)),
      false
    )
  ),
  unroll_tree(0, TREE, SIZE, PID, REV), 
  reverse(REV, PFX),
  mk_dels(SIZE, DELS), 
  append(PFX, [inf(rnm, [PID], CID, FORM) | DELS], INSTS).

mk_dels(NUM, DELS) :-
  range(asc, NUM, NUMS),
  maplist_cut(mk(t), NUMS, IDS),
  maplist_cut(mk(del), IDS, DELS).

report_sol_failure(CTX, ANT) :- 
  write("\nSolution failed, annotation : "), 
  write(ANT), nl, nl,
  % write("\nInference failed, premises :\n\n"),
  % write_list(PREMS), 
  % format("\nInference failed, conclusion : ~w\n\n", CONC), 
  open("sol_trace.pl", write, Stream), 
  format(Stream, '~w.\n\n', debug_ctx(CTX)), 
  format(Stream, '~w.\n\n', debug_ant(ANT)), 
  close(Stream).

tup_ctx((ID, _, FORM, _), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, $pos(FORM), CTX_O).

tups_ctx(TUPS, CTX) :- 
  empty_assoc(EMP), 
  foldl(tup_ctx, TUPS, EMP, CTX).

invert_conjecture([], []).
invert_conjecture([TUP_I | TUPS_I], [TUP_O | TUPS_O]) :- 
  TUP_I = (ID, conjecture, FORM, file(X, Y)) -> 
  TUP_O = (ID, negated_conjecture, $not(FORM), file(X, Y)),
  TUPS_O = TUPS_I
;
  TUP_O = TUP_I,
  invert_conjecture(TUPS_I, TUPS_O).

explicate_scla((ID, TYPE, FORM, INFO), (ID, TYPE, NORM, INFO)) :- 
  explicate_form(FORM, NORM).

implicate_inst(add(HINT, ID, FORM), add(HINT, ID, NORM)) :- 
  implicate_form(FORM, NORM).
implicate_inst(skm(FUN, ARI, ID, FORM), skm(FUN, ARI, ID, NORM)) :- 
  implicate_form(FORM, NORM).
implicate_inst(inf(HINT, IDS, ID, FORM), inf(HINT, IDS, ID, NORM)) :- 
  implicate_form(FORM, NORM).
implicate_inst(del(ID), del(ID)).

implicate_inst(X, _) :-
  write("Error : cannot implicate "),
  write(X),
  false.
  
esolve(TSTP, SOL) :- 
  tstp_sclas(TSTP, TEMP), !, 
  maplist_cut(explicate_scla, TEMP, EXPL),
  invert_conjecture(EXPL, TUPS),
  tups_ctx(TUPS, CTX),
  maplist_cut(tup_insts(CTX), TUPS, INSTSS),
  append(INSTSS, APPENDED),
  maplist_cut(implicate_inst, APPENDED, IMPL),
  relabel(IMPL, SOL),
  true.