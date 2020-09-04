:- [basic].

maxpdx(EXP, MAX) :- 
  findall(NUM, sub_term($par(NUM), EXP), NUMS), 
  max_list(NUMS, MAX).

map_par(_, $var(NUM), $var(NUM)) :- !.
map_par(_, $dst(STR), $dst(STR)) :- !.
map_par(GOAL, $fun($par(NUM), []), TERM) :- !, 
  call(GOAL, NUM, TERM). 
map_par(GOAL, $fun(FUN, TERMS_I), $fun(FUN, TERMS_O)) :- 
  maplist_cut(map_par(GOAL), TERMS_I, TERMS_O).

bind_par(DEP, IDX, IDX, $var(DEP)).
bind_par(_, IDX_A, IDX_B, $fun($par(IDX_B), [])) :- IDX_A \= IDX_B.

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
entails(PREM, CONC, eqr) :- eqr((prem, $pos(PREM)), (conc, $neg(CONC)), (_, 0)).

tree_conc(ntr(_, SF), SF).
tree_conc(utr(_, _, SF), SF).
tree_conc(btr(_, _, _, SF), SF).

incr_vdx(DEP, IDX, $var(NEW)) :- 
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
  ground_all($fun(c,[]), TGT),
  bind_all_pars(TGT, CONC), !.

ant_names(inference(_, _, [ANT]), NAMES) :- ant_names(ANT, NAMES).
ant_names(inference(_, _, [ANT_A, ANT_B]), NAMES) :- 
  ant_names(ANT_A, NAMES_A),
  ant_names(ANT_B, NAMES_B),
  union(NAMES_A, NAMES_B, NAMES).
ant_names(NAME, [NAME]) :- atom(NAME).

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
bind_lvs(NUM, [$var(NUM) | VARS]) :- 
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

eq_resolve(FORM_I, FORM_O) :- 
  inst_with_lvs(FORM_I, BODY_I), 
  cf_lits(BODY_I, LITS),
  pluck(LITS, $not($rel('=', [LHS, RHS])), REST), 
  unify_with_occurs_check(LHS, RHS), 
  mk_cf(REST, BODY_O),
  close_lvs(BODY_O, FORM_O).
combine_opts(none, OPT, OPT).
combine_opts(OPT, none, OPT).
combine_opts(some((X, Y)), some((Z, W)), some((X, Y))) :- 
  (
    X == Z, Y == W ;
    X == W, Y == W
  ), !.
combine_opts(some((X, Y)), some((Z, W)), some((X, Y))) :- unify_with_occurs_check(Z, W).
combine_opts(some((X, Y)), some((Z, W)), some((Z, W))) :- unify_with_occurs_check(X, Y).

compute_eqn_term(TERM_A, TERM_B, none) :- TERM_A == TERM_B, !.
compute_eqn_term(TERM_A, TERM_B, EQN) :-
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A = $fun(FUN, TERMS_A),
  TERM_B = $fun(FUN, TERMS_B),
  maplist(compute_eqn_term, TERMS_A, TERMS_B, EQNS), 
  foldl(combine_opts, EQNS, none, EQN).
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
compute_eqn_form($rel(REL, TERMS_A), $rel(REL, TERMS_B), EQN) :- 
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
  X = $var(NUM).

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
  TERM = $var(CNT)
;
  TERM = $var(NUM).

bind_var_term(IDX, CNT, TERM_I, TERM_O) :-
  map_var(bind_var(IDX, CNT), TERM_I, TERM_O).

e_skm_term(SKM, NUM, $fun(SKM, VARS)) :-
  range(desc, NUM, NUMS), 
  maplist_cut([X, $var(X)]>>true, NUMS, VARS), 
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
syeq_atom($rel('=', [LHS_A, RHS_A]), $rel('=', [LHS_B, RHS_B])) :- 
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

mk_rw_form(LHS, RHS, $rel(REL, TERMS_I), $rel(REL, TERMS_O)) :- 
  mk_rw_terms(LHS, RHS, TERMS_I, TERMS_O).
  
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
    TERM_I = $fun(FUN, TERMS_I), 
    mk_rw_terms(FROM, TO, TERMS_I, TERMS_O), 
    TERM_O = $fun(FUN, TERMS_O) 
  ).

nst_orient(pm, HYP_L, HYP_R, HYP_L, HYP_R).
nst_orient(rw, HYP_L, HYP_R, HYP_L, HYP_R).
nst_orient(sr, HYP_L, HYP_R, HYP_R, HYP_L).
nst_orient(sr, HYP_L, HYP_R, HYP_L, HYP_R).

unify_atom(ATOM_A, ATOM_B) :- 
  erient_form(ATOM_A, TEMP), 
  unify_with_occurs_check(TEMP, ATOM_B).

fold_definition(NUM, ATOM, BODY, $not(FORM), $not(NORM)) :- 
  fold_definition(NUM, ATOM, BODY, FORM, NORM).

fold_definition(NUM, ATOM, BODY, FORM, NORM) :- 
  decom_qtf(FORM, QTF, SUB_FORM), 
  substitute_form(fast, $fun($par(NUM), []), SUB_FORM, TEMP_FORM), 
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

mk_root(_, $false, rnm, $false) :- !.
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
  erient_form(LIT_A, LIT_AT),
  compute_eqn_form(LIT_AT, LIT_B, some((LHS, RHS))), 
  mk_cf([$not($rel('=', [LHS, RHS])), LIT_B | REST], BODY_O), 
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

mk_root(_, $false, _, rnm, $false) :- !.
mk_root(_, _, $false, rnm, $false) :- !.

mk_root(apply_def, FORM_A, FORM_B, dff, FORM_C) :- !, 
  inst_with_lvs(FORM_B, $iff(ATOM, BODY_B)), 
  fold_definition(0, ATOM, BODY_B, FORM_A, FORM_C),
  ground(FORM_C),
  true.

mk_root(RUL, FORM_A, FORM_B, (sup, l), FORM) :- 
  member(RUL, [pm, rw, sr]),
  inst_with_lvs(FORM_A, BODY_A),
  cf_lits(BODY_A, LITS_A), 
  inst_with_lvs(FORM_B, BODY_B),
  cf_lits(BODY_B, LITS_B),  
  pluck(LITS_B, LIT_B, REST_B),
  orient_equation(LIT_B, $rel('=', [LHS, RHS])),
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
  strip_fas(FORM, _, $iff($rel(PRED, TERMS), _)), 
  length(TERMS, ARI).

inst_fas(NUM, $fa(FORM), BODY) :- !,
  num_succ(NUM, SUCC),
  substitute_form(fast, $fun($par(NUM), []), FORM, TEMP),
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
  (CID, axiom, FORM, some(ANNOT)),
  [orig(PID, CID, FORM)]
) :- 
  (ANNOT = file(_, PID) ; ANNOT = PID), 
  atom(PID), !.

tup_insts(
  _, 
  (CID, plain, FORM, some(introduced(definition))),
  [add([def, PRD, ARI], CID, FORM)]
) :- !,
  def_pred_ari(FORM, PRD, ARI).
  
% tup_insts(
%   CTX,
%   (CID, TYPE, FORM, some(ANT)),
%   INSTS 
% ) :- 
%   inst_fas(0, FORM, TGT), 
%   timed_call(
%     30, 
%     mk_tree_fwd(CTX, TGT, ANT, TREE),
%     (
%       write("Solution failed prematurely. "), 
%       report_sol_failure(CTX, (CID, TYPE, FORM, some(ANT))),
%       false
%     ),
%     (
%       write("Solution timed out. "), 
%       report_sol_failure(CTX, (CID, TYPE, FORM, some(ANT))),
%       false
%     )
%   ),
%   unroll_tree(0, TREE, _, PID, REV), 
%   reverse([inf(rnm, [PID], CID, FORM) | REV], INSTS).
tup_insts(
  CTX,
  (CNM, _, FORM, some(ANT)),
  INSTS 
) :- 
  inst_fas(0, FORM, TGT), 
  timed_call(
    1, 
    (
      mk_tree_fwd(CTX, TGT, ANT, TREE),
      unroll_tree(0, TREE, _, PNM, REV), 
      reverse([inf(rnm, [PNM], CNM, FORM) | REV], INSTS)
    ),
    (
      format("Failed to expand instruction = ~w, relegating proof...\n", CNM),
      ant_names(ANT, NAMES),
      INSTS = [inf(gps, NAMES, CNM, FORM)]
    )
  ).

report_sol_failure(CTX, ANT) :- 
  format("Annotation = ~w\n", ANT), 
  open("sol_trace.pl", write, Stream), 
  format(Stream, '~w.\n\n', debug_ctx(CTX)), 
  format(Stream, '~w.\n\n', debug_ant(ANT)), 
  close(Stream),
  true.

tup_ctx((ID, _, FORM, _), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, $pos(FORM), CTX_O).

tups_ctx(TUPS, CTX) :- 
  empty_assoc(EMP), 
  foldl(tup_ctx, TUPS, EMP, CTX).
  
esolve(TSTP, SOL) :- 
  tptp_sol(TSTP, TUPS), !, 
  tups_ctx(TUPS, CTX),
  maplist_cut(tup_insts(CTX), TUPS, INSTSS),
  append(INSTSS, APPENDED),
  relabel(APPENDED, SOL).