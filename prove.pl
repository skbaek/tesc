:- [basic].


term_poseq_term(Var, _) :- var(Var).

term_poseq_term(_, Var) :- var(Var).

term_poseq_term(TERM_A, TERM_B) :- 
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A =.. [FUN | TERMS_A],
  TERM_B =.. [FUN | TERMS_B],
  length(TERMS_A, LTH),
  length(TERMS_B, LTH).

term_poseq_term(_, TERM_A, TERM_B) :- 
  term_poseq_term(TERM_A, TERM_B).

term_poseq_term(OPQEs, TERM_A, TERM_B) :- 
  member((_, $pos(QE)), OPQEs), 
  inst_with_lvs(QE, TERM_L = TERM_R),
  ( 
    term_poseq_term(TERM_A, TERM_L) ; 
    term_poseq_term(TERM_A, TERM_R) ; 
    term_poseq_term(TERM_B, TERM_R) ; 
    term_poseq_term(TERM_B, TERM_L) 
  ).

%%%%%%% Decomposition to Equational GOALs %%%%%%%

intro_eqs(MONO, [], [], GOAL, MONO, [], GOAL).

intro_eqs(MONO, [TERM_A | TERMS_A], [TERM_B | TERMS_B], GOAL, Iff, [(ONE, SubGOAL) | HGS], GOAL_N) :-
  cp(MONO, TERM_A, GOAL, MONOA, GOAL_A), 
  cp(MONOA, TERM_B, GOAL_A, MONOAB, GOAL_AB), 
  bp(MONOAB, GOAL_AB, ONE, TempMONO, SubGOAL, GOAL_T), 
  intro_eqs(TempMONO, TERMS_A, TERMS_B, GOAL_T, Iff, HGS, GOAL_N). 

break_eq_fun(OPEs, ONE, GOAL, HGS) :- 
  ONE = (_, $neg(TERM_A = TERM_B)),
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A =.. [FUN | TERMS_A],
  TERM_B =.. [FUN | TERMS_B],
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  maplist_cut(term_poseq_term(OPEs), TERMS_A, TERMS_B),
  mk_mono_fun(LTH, FUN, MONOForm),
  % atom_number(LTH_ATOM, LTH),
  tp($pos(MONOForm), GOAL, MONO, GOAL0),
  intro_eqs(MONO, TERMS_A, TERMS_B, GOAL0, OPE, HGS, GOAL1),
  xp(OPE, ONE, GOAL1).

break_eq_rel(OPEs, OPA, ONA, GOAL, HGS) :- 
  OPA = (_, $pos(ATOM_A)),
  ONA = (_, $neg(ATOM_B)),
  ATOM_A =.. [REL | TERMS_A], 
  ATOM_B =.. [REL | TERMS_B], 
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  maplist_cut(term_poseq_term(OPEs), TERMS_A, TERMS_B),
  mk_mono_rel(LTH, REL, MONOForm),
  % atom_number(LTH_ATOM, LTH),
  tp($pos(MONOForm), GOAL, MONO, GOAL0),
  intro_eqs(MONO, TERMS_A, TERMS_B, GOAL0, IMP, HGS, GOAL1),
  bp(IMP, GOAL1, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  xp(OPA, HYP_L, GOAL_L), 
  xp(HYP_R, ONA, GOAL_R). 

subst_fun_mul(OPEs, ONE, GOAL, NewOPEs) :-
  ONE = (_, $neg(TERM_A = TERM_B)), 
  (
    TERM_A == TERM_B -> 
    (eq_refl(ONE, GOAL), NewOPEs = OPEs) ;
    subst_fun_mul_0(OPEs, ONE, GOAL, NewOPEs)
  ).

subst_fun_mul_0(OPEs, ONF, GOAL, OPEs) :- 
  ONF = (_, $neg(TERM_A = TERM_B)), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONF, GOAL).

subst_fun_mul_0(OPEs, ONE, GOAL, NewOPEs) :-
  break_eq_fun(OPEs, ONE, GOAL, HGS),
  subst_fun_mul_aux(OPEs, HGS, NewOPEs). 

subst_fun_mul_0(OPQEs, ONE, GOAL, NewOPQEs) :- 
  ONE = (_, $neg(TERM_A0 = TERM_C)), 
  pluck_uniq(OPQEs, OPQE, REST),
  many_nb([c], [OPQE], GOAL, [PRE_OPE], GOAL_T), 
  PRE_OPE = (_, $pos(_ = _)),
  erient_hyp(PRE_OPE, GOAL_T, OPE, GOAL0),
  OPE = (_, $pos(TERM_A1 = TERM_B)),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  fp(TERM_B = TERM_C, GOAL0, NewONE, NewOPE, GOAL1, GOAL2), 
  subst_fun_mul(REST, NewONE, GOAL1, NewOPQEs), 
  eq_trans(OPE, NewOPE, ONE, GOAL2).

subst_fun_mul_aux(OPEs, [], OPEs).

subst_fun_mul_aux(OPEs, [(ONE, GOAL) | HGS], NewOPEs) :-
  subst_fun_mul(OPEs, ONE, GOAL, TempOPEs),
  subst_fun_mul_aux(TempOPEs, HGS, NewOPEs).

subst_rel_mul(HYP_L, OPEs, HYP_R, GOAL, NewOPEs) :-  
  orient_sign(HYP_L, HYP_R, PreOPA, ONA),
  erient_hyp(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel(OPEs, OPA, ONA, GOAL_T, HGS),
  subst_fun_mul_aux(OPEs, HGS, NewOPEs). 

subst_fun_add(EQNS, (HYP, GOAL)) :-
  subst_fun_add(EQNS, HYP, GOAL).

subst_fun_add(EQNS, ONE, GOAL) :-
  ONE = (_, $neg(TERM_A = TERM_B)), 
  (
    TERM_A == TERM_B -> 
    eq_refl(ONE, GOAL) ;
    subst_fun_add_0(EQNS, ONE, GOAL)
  ).

subst_fun_add_0(_, ONF, GOAL) :- 
  ONF = (_, $neg(TERM_A = TERM_B)), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONF, GOAL).

subst_fun_add_0(EQNS, ONE, GOAL) :-
  break_eq_fun(EQNS, ONE, GOAL, HGS),
  maplist(subst_fun_add(EQNS), HGS). 

subst_fun_add_0(OPQEs, ONE, GOAL) :- 
  ONE = (_, $neg(TERM_A0 = TERM_C)), 
  pluck_uniq(OPQEs, OPQE, REST),
  many_nb([c], [OPQE], GOAL, [PRE_OPE], GOAL_T), 
  PRE_OPE = (_, $pos(_ = _)),
  erient_hyp(PRE_OPE, GOAL_T, OPE, GOAL0),
  OPE = (_, $pos(TERM_A1 = TERM_B)),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  fp(TERM_B = TERM_C, GOAL0, NewONE, NewOPE, GOAL1, GOAL2), 
  subst_fun_add(REST, NewONE, GOAL1), 
  eq_trans(OPE, NewOPE, ONE, GOAL2).

subst_rel_add(EQNS, HYP_L, HYP_R, GOAL) :-  
  orient_sign(HYP_L, HYP_R, PreOPA, ONA),
  erient_hyp(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel(EQNS, OPA, ONA, GOAL_T, HGS),
  maplist(subst_fun_add(EQNS), HGS).

pick_pivot(HYPS, HYP, GOAL, HYP_N, GOAL_N) :-
  many([b, c, s], ([HYP], GOAL), HGS),
  pluck(HGS, ([HYP_N], GOAL_N), REST), 
  maplist(pick_mate(HYPS), REST). 

pick_pivot_prop(HYPS, HYP, GOAL, HYP_N, GOAL_N) :-
  many([b, s], ([HYP], GOAL), HGS),
  pluck(HGS, ([HYP_N], GOAL_N), REST), 
  maplist(pick_mate(HYPS), REST). 

apply_aocs(ANTE, [AOC | AOCS], GOAL_I, CONS, GOAL_O) :-  
  many_nb([c], [AOC], GOAL_I, [IMP], GOAL_T),
  bp(IMP, GOAL_T, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  mate(ANTE, HYP_L, GOAL_L), 
  apply_aocs(HYP_R, AOCS, GOAL_R, CONS, GOAL_O).

apply_aocs(HYP, [], GOAL, HYP, GOAL). 

vcnf(PREM, HYPS, GOAL) :- 
  sp(PREM, GOAL, PREM_N, GOAL_N), !,
  vcnf(PREM_N, HYPS, GOAL_N).
 
vcnf(PREM, HYPS, GOAL) :- 
  bp(PREM, GOAL, PREM_A, PREM_B, GOAL_A, GOAL_B), !,
  vcnf(PREM_A, HYPS, GOAL_A),
  vcnf(PREM_B, HYPS, GOAL_B).

vcnf(PREM, HYPS, GOAL) :- 
  cp(PREM, _, GOAL, PREM_N, GOAL_N), !, 
  vcnf(PREM_N, HYPS, GOAL_N).

vcnf(PREM, HYPS, GOAL) :- 
  member(DIR, [l, r]),
  ap(PREM, DIR, GOAL, PREM_N, GOAL_N),
  vcnf(PREM_N, HYPS, GOAL_N).

vcnf(PREM, HYPS, GOAL) :- 
  member(HYP, HYPS), 
  mate(PREM, HYP, GOAL).

vacc_aux(TRP) :- 
  para__s(TRP, TRP_N) ->
  mate(TRP_N) ;
  mate(TRP).

vacc_aux((PREM, CONC, GOAL)) :- 
  pmt_cla(PREM, CONC, GOAL).

vacc(PREM, CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [CONC_N], GOAL1), 
  many_nb([c], [PREM], GOAL1, [PREM_T], GOAL2), 
  member(DIR, [l,r]),
  ap(PREM_T, DIR, GOAL2, PREM_N, GOAL3), 
  paraab_choose((PREM_N, CONC_N, GOAL3), TRP_A, TRP_B), 
  vacc_aux(TRP_A),
  vacc_aux(TRP_B).

pmt_cla(PREM, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  many([b, c, s], ([PREM], GOAL_T), HGS), 
  maplist(pick_mate(HYPS), HGS).

res(PYP0, PYP1, NYP, GOAL) :- 
  many_nb([a, d, s], [NYP], GOAL, HYPS, GOAL_T), 
  (
    res_core(PYP0, PYP1, HYPS, GOAL_T) ;
    res_core(PYP1, PYP0, HYPS, GOAL_T)
  ), !.

res_core(PYP0, PYP1, HYPS, GOAL) :- 
  fp(_, GOAL, NPVT, PPVT, GOAL_N, GOAL_P), 
  many([b, c, s], ([PYP0], GOAL_N), HGS0), 
  many([b, c, s], ([PYP1], GOAL_P), HGS1), !, 
  pluck(HGS0, ([HYP0], GOAL0), REST0), 
  mate_pn(HYP0, NPVT, GOAL0), 
  pluck(HGS1, ([HYP1], GOAL1), REST1), 
  mate_pn(PPVT, HYP1, GOAL1), 
  maplist(pick_mate([NPVT | HYPS]), REST0), 
  maplist(pick_mate([PPVT | HYPS]), REST1). 

dfu(DEFS, PREM, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T),
  many([b, c, s], ([PREM], GOAL_T), HGS),
  dfu_many(DEFS, HYPS, HGS).

dfu_many(_, [], []).

dfu_many(EQNS, HYPS, [([HYP], GOAL) | HGS]) :- 
  pluck(HYPS, CMP, REST), 
  subst_rel_add(EQNS, HYP, CMP, GOAL), 
  dfu_many(EQNS, REST, HGS).

dff(_, HYP0, HYP1, DFP) :-
  mate(HYP0, HYP1, DFP). 

dff(Defs, HYP0, HYP1, DFP) :- 
  (
    paras((HYP0, HYP1, DFP), (NewHYP0, NewHYP1, NewDFP)) ;
    paracd((HYP0, HYP1, DFP), (NewHYP0, NewHYP1, NewDFP))
  ), !,
  dff(Defs, NewHYP0, NewHYP1, NewDFP).

dff(Defs, HYP0, HYP1, GOAL) :- 
  paraab((HYP0, HYP1, GOAL), (HYP0L, HYP1L, GOAL_L), (HYP0R, HYP1R, GOAL_R)),
  dff(Defs, HYP0L, HYP1L, GOAL_L),
  dff(Defs, HYP0R, HYP1R, GOAL_R).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, $pos(Atom)), 
  unsigned_atom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0),
  IFF = (_, $pos($iff(Atom, _))), !,
  ap(IFF, l, DFP0, IMP, DFP1), 
  bp(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Ante, DFP2), 
  dff(Defs, HYP0, Cons, DFP3).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, $neg(Atom)), 
  unsigned_atom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, $pos($iff(Atom, _))), !,
  ap(IFF, r, DFP0, IMP, DFP1), 
  bp(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Cons, DFP3), 
  dff(Defs, HYP0, Ante, DFP2).



%%%%%%%%%%%%%%%% SAT SOLVER %%%%%%%%%%%%%%%% 

lit_num(ANA, $not(ATOM), NEG) :- !,
  get_assoc(ATOM, ANA, NUM), 
  NEG is - NUM.

lit_num(ANA, ATOM, NUM) :- !,
  get_assoc(ATOM, ANA, NUM).

cla_nums(ANA, CH, NUMS) :- 
  cla_lits(CH, LITS), 
  maplist_cut(lit_num(ANA), LITS, NUMS). 

cla_lits((_, $pos(CF)), LITS) :- 
  cf_lits(CF, LITS).

cla_atoms(CH, ATOMS) :-
  cla_lits(CH, LITS),
  maplist_cut(lit_atom, LITS, ATOMS). 

cla_table(CH, TBL_I, TBL_O) :- 
  cla_atoms(CH, ATOMS), 
  foldl(atom_table, ATOMS, TBL_I, TBL_O).
  
atom_table(ATOM, (NUM_I, ANA_I, NAA_I), TBL_O) :- 
  get_assoc(ATOM, ANA_I, _) -> 
  TBL_O = (NUM_I, ANA_I, NAA_I)
;
  num_succ(NUM_I, NUM_O),
  put_assoc(ATOM, ANA_I, NUM_I, ANA_O),
  put_assoc(NUM_I, NAA_I, ATOM, NAA_O),
  TBL_O = (NUM_O, ANA_O, NAA_O).
  
mk_sat_tables(CHS, ANA, NAA) :- 
  empty_assoc(EMP), 
  foldl(cla_table, CHS, (1, EMP, EMP), (_, ANA, NAA)).
  
cla_ctx(CLA, (NUM_I, CTX_I), (NUM_O, CTX_O)) :- 
  num_succ(NUM_I, NUM_O), 
  put_assoc(NUM_I, CTX_I, CLA, CTX_O).

mk_sat_ctx(CLAS, CTX) :- 
  empty_assoc(EMP), 
  foldl(cla_ctx, CLAS, (1, EMP), (_, CTX)).
  
string_numbers(STR, NUMS) :- 
  split_string(STR, " ", "", STRS), 
  maplist_cut(string_number, STRS, NUMS).

nums_dimacs(NUMS, Str) :- 
  maplist(number_string, NUMS, Strs),
  strings_concat_with(" ", Strs, TempStr),
  string_concat(TempStr, " 0", Str).

num_lit(NAA, NUM, LIT) :- 
  NUM < 0 -> 
  NEG is - NUM, 
  get_assoc(NEG, NAA, ATOM),
  LIT = $not(ATOM)
;
  get_assoc(NUM, NAA, LIT).

lits_cla([], $false).

lits_cla(Lits, Cla) :- 
  lits_cla_core(Lits, Cla).

lits_cla_core([Lit], Lit).

lits_cla_core([Lit | Lits], $or(Lit, Cla)) :- 
  lits_cla_core(Lits, Cla).

nums_cla(NAA, NUMS, CLA) :- 
  maplist_cut(num_lit(NAA), NUMS, LITS),
  lits_cla(LITS, CLA). 

add_del_inst(ID, [del(ID) | SIS], SIS).

line_sat_insts(_, LINE, SIS_I, SIS_O) :- 
  split_string(LINE, " ", "", [_, "d" | NUMS]), 
  append(ID_STRS, ["0"], NUMS), 
  maplist_cut(number_string, IDS, ID_STRS), 
  foldl(add_del_inst, IDS, SIS_I, SIS_O).

line_sat_insts(NAA, LINE, [rup(SIDS, SID, CLA) | SIS], SIS) :- 
  string_numbers(LINE, [SID | NUMS]),
  append(CLA_NUMS, [0 | REST], NUMS), 
  nums_cla(NAA, CLA_NUMS, CLA),
  append(SIDS, [0], REST). 
  
file_sat_insts(NAA, FILE, SIS) :-
  read_file_strings(FILE, LINES), 
  foldl(line_sat_insts(NAA), LINES, SIS, []).

nums_maxvar(NUMS, MaxVar) :-
  maplist_cut(abs, NUMS, Nats),
  max_list(Nats, MaxVar).

numss_maxvar(NUMSs, MaxVar) :-
  maplist(nums_maxvar, NUMSs, MaxVars),
  max_list(MaxVars, MaxVar).

numss_dimacs(NUMSs, DIMACS) :-
  numss_maxvar(NUMSs, MaxVar), 
  number_string(MaxVar, MaxVarStr),
  length(NUMSs, NumCla),
  number_string(NumCla, NumClaStr),
  strings_concat(["p cnf ", MaxVarStr, " ", NumClaStr], Str),
  maplist(nums_dimacs, NUMSs, Strs),
  strings_concat_with("\n", [Str | Strs], DIMACS).

lit_sl($not(ATOM), $neg(ATOM)) :- !.
lit_sl(ATOM, $pos(ATOM)).

form_sls(FORM, SLS) :- 
  body_lits(FORM, LITS, []), 
  maplist_cut(lit_sl, LITS, SLS).

% form_sls($or(LIT, FORM), [SL | SLS]) :- !,
%   lit_sl(LIT, SL),
%   form_sls(FORM, SLS). 
%   
% form_sls(LIT, [SL]) :- lit_sl(LIT, SL).

find_new_unit_core([SL], _, SL) :- !.
find_new_unit_core([SL_I | SLS_A], SLS_B, SL) :- 
  (
    member(SL_B, SLS_B), 
    complements(SL_I, SL_B)
  ) -> 
  find_new_unit_core(SLS_A, SLS_B, SL) 
;
  SL = SL_I.

find_new_unit((_, $pos(FORM)), HYPS, SL) :- 
  form_sls(FORM, SLS_A),
  maplist_cut(snd, HYPS, SLS_B), 
  find_new_unit_core(SLS_A, SLS_B, SL).

unit_propagate(PREM, (HYPS_I, GOAL_I), ([HYP | HYPS_I], GOAL_O)) :- 
  find_new_unit(PREM, HYPS_I, SL), 
  fps(SL, GOAL_I, HYP_T, HYP, GOAL_T, GOAL_O),
  many([b, s], ([PREM], GOAL_T), HGS), 
  % pluck(HGS, ([HYP], GOAL_O), REST),
  maplist_cut(pick_mate([HYP_T | HYPS_I]), HGS).

get_sat_cla(CTX, SID, CLA) :- 
  get_assoc(SID, CTX, CLA).
  
put_sat_cla(CTX_I, SID, CLA, CTX_O) :- 
  put_assoc(SID, CTX_I, CLA, CTX_O).

del_sat_cla(CTX_I, SID, CLA, CTX_O) :- 
  del_assoc(SID, CTX_I, CLA, CTX_O).

use_sat_inst(CTX, del(SID), GOAL, CTX_N, GOAL_N) :-
  del_sat_cla(CTX, SID, CLA, CTX_N), 
  wp(CLA, GOAL, GOAL_N). 

use_sat_inst(CTX, rup(SIDS, SID, CLA), GOAL, CTX_N, GOAL_N) :- 
  fp(CLA, GOAL, NYP, PYP, GOAL_T, GOAL_N), 
  put_sat_cla(CTX, SID, PYP, CTX_N),
  many_nb([a, s], [NYP], GOAL_T, HYPS_I, GOAL_I), 
  maplist_cut(get_sat_cla(CTX), SIDS, PREMS), !,
  foldl_cut(unit_propagate, PREMS, (HYPS_I, GOAL_I), ([HYP | HYPS_O], GOAL_O)), !,
  member(CMP, HYPS_O),
  mate(HYP, CMP, GOAL_O), !.

use_sat_insts(CTX, [SI | SIS], GOAL) :- 
  % write("Using SAT step : "), 
  % write(SI), nl, nl,
  use_sat_inst(CTX, SI, GOAL, CTX_N, GOAL_N), 
  (
    SIS = [] -> 
    SI = rup(_, SID, _), 
    get_sat_cla(CTX_N, SID, CLA), 
    use_pf(CLA, GOAL_N)
  ;
    use_sat_insts(CTX_N, SIS, GOAL_N)
  ).

sat(CLAS, GOAL) :-
  mk_sat_tables(CLAS, ANA, NAA),
  maplist_cut(cla_nums(ANA), CLAS, NUMSS),
  numss_dimacs(NUMSS, DIMACS),
  write_file("temp.cnf", DIMACS), !,
  shell("./cadical -q temp.cnf temp.drat", _), !,
  shell("./drat-trim temp.cnf temp.drat -L temp.lrat", _), !,

  write("Reading LRAT file...\n\n"),
  file_sat_insts(NAA, "temp.lrat", SIS), 

  write("Constructing SAT context...\n\n"),
  mk_sat_ctx(CLAS, CTX), 

  use_sat_insts(CTX, SIS, GOAL),
  delete_file("temp.cnf"),
  delete_file("temp.drat"),
  delete_file("temp.lrat"),
  true.


eskm(AOCS, H2G) :- 
  para_m(H2G) -> true 
;
  paraab(H2G, H2G_L, H2G_R) -> 
  skm(AOCS, H2G_L), 
  skm(AOCS, H2G_R)
;
  para__d(H2G, H2G_N) ->
  eskm(AOCS, H2G_N)
;
  para_c_(H2G, H2G_N) ->
  eskm(AOCS, H2G_N)
;
  H2G = (PREM, CONC, GOAL),
  pluck(AOCS, AOC, REST),
  many_nb([c], [AOC], GOAL, [HYP], GOAL_T), 
  bp(HYP, GOAL_T, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  xp(PREM, HYP_L, GOAL_L),
  eskm(REST, (HYP_R, CONC, GOAL_R)).

skm(AOCS, H2G) :- 
  para_m(H2G) -> true 
;
  para_c_(H2G, H2G_N), 
  %paracd(H2G, H2G_N), 
  skm(AOCS, H2G_N)
;
  paral_cd(H2G, H2G_N), 
  skm(AOCS, H2G_N)
;
  paraab(H2G, H2G_L, H2G_R),
  skm(AOCS, H2G_L), 
  skm(AOCS, H2G_R)
;
  H2G = (PREM, CONC, GOAL),
  pluck(AOCS, AOC, REST),
  many_nb([c], [AOC], GOAL, [HYP], GOAL_T), 
  bp(HYP, GOAL_T, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  xp(PREM, HYP_L, GOAL_L),
  skm(REST, (HYP_R, CONC, GOAL_R)).



spl_exp([], [], GOAL, [], GOAL).

spl_exp([PREM | PREMS], HYPS_I, GOAL_I, [HYP | HYPS_O], GOAL_O) :- 
  pluck(HYPS_I, HYP_I, REST), 
  (
    ap(PREM, l, GOAL_I, HYP_T, GOAL_T) ;
    ap(PREM, r, GOAL_I, HYP_T, GOAL_T) 
  ), 
  (
    bp(HYP_T, GOAL_T, HYP_A, HYP_B, GOAL_A, GOAL_B) ;
    bp(HYP_T, GOAL_T, HYP_B, HYP_A, GOAL_B, GOAL_A) 
  ), 
  mate(HYP_A, HYP_I, GOAL_A), 
  many_nb([d, s], [HYP_B], GOAL_B, [HYP], GOAL),
  spl_exp(PREMS, REST, GOAL, HYPS_O, GOAL_O).

eqf(HYPS, EQN, ([HYP], GOAL)) :- 
  member(CMP, HYPS), 
  subst_rel_add([EQN], CMP, HYP, GOAL).

rwa(AYP, TRP) :- 
  TRP = (PREM, _, GOAL), 
  (
    para_m(TRP) -> true ; 
    paras(TRP, TRP_N) -> rwa(AYP, TRP_N) ; 
    paraab(TRP, TRP_L, TRP_R), 
    rwa(AYP, TRP_L), 
    rwa(AYP, TRP_R)
  ;
    mate(AYP, PREM, GOAL) 
  ).

pmt((PREM, CONC, GOAL)) :- 
  many_nb([a, s], [CONC], GOAL, HYPS, GOAL_T), 
  many([b, s], ([PREM], GOAL_T), HGS), 
  maplist(pick_mate(HYPS), HGS).

speq(TRP) :- 
  para_cd(TRP, TEMP) -> speq(TEMP) ;
  a_para(TRP, TEMP),
  para_m(TEMP). 

scj(H2G) :- 
  pmt(H2G) -> true ;
  paras(H2G, H2G_N) -> scj(H2G_N) ;
  a_para(H2G, H2G_N),
  scj(H2G_N).

sf_sign_form($pos(FORM), pos, FORM).
sf_sign_form($neg(FORM), neg, FORM).
hyp_sign_form((_, SF), SIGN, FORM) :- sf_sign_form(SF, SIGN, FORM).

esimp_fork_not((HYP_A, HYP_B, GOAL), (HYP_A, HYP_L, GOAL_L), (HYP_R, HYP_B, GOAL_R)) :- 
  hyp_sign_form(HYP_A, SIGN, $not(FORM)), 
  esimp(FORM, NORM), 
  apply_uop(SIGN, $not(NORM), SF),
  fps(SF, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

esimp_not(X) :- 
  para_lc(X) -> true ;
  para_m(X) -> true ;
  paras(X, Y), 
  esimp_not(Y).
  
esimp_bct(X) :- para_lc(X).
esimp_bct(X) :- 
  para_b_(X, Y, Z), 
  para_mlc(Y),
  para_mlc(Z).
esimp_bct(X) :- 
  paraab(X, Y, Z), 
  para_m(Y),
  para_m(Z).
esimp_bct((PREM, CONC, GOAL)) :- 
  aap(PREM, GOAL, HYP_L, HYP_R, GOAL_T), 
  (
    use_lc(HYP_L, GOAL_T) ; 
    use_lc(HYP_R, GOAL_T) ; 
    mate(HYP_L, CONC, GOAL_T) ;
    mate(HYP_R, CONC, GOAL_T) ;
    mate(HYP_L, HYP_R, GOAL_T) ;
    (
      (HYP = HYP_L ; HYP = HYP_R),
      TRP = (HYP, CONC, GOAL_T),
      (para_b_(TRP, TRP_A, TRP_B) ; para_b_(TRP, TRP_B, TRP_A)), 
      para_lc(TRP_A),
      (para__s(TRP_B, TRP_C) ; true),
      para_m(TRP_C)
    )
  ).

esimp_bct((PREM, _, GOAL)) :- 
  bp(PREM, GOAL, PREM_L, PREM_R, GOAL_L, GOAL_R), 
  aap(PREM_L, GOAL_L, PREM_LL, PREM_LR, GOAL_LT), 
  mate(PREM_LL, PREM_LR, GOAL_LT),
  aap(PREM_R, GOAL_R, PREM_RL, PREM_RR, GOAL_RT), 
  mate(PREM_RL, PREM_RR, GOAL_RT).

esimp_fork_bct((HYP_A, HYP_B, GOAL), (HYP_A, HYP_L, GOAL_L), (HYP_R, HYP_B, GOAL_R)) :- 
  hyp_sign_form(HYP_A, SIGN, FORM), 
  decom_bct(FORM, BCT, FORM_A, FORM_B), 
  esimp(FORM_A, NORM_A),
  esimp(FORM_B, NORM_B),
  apply_bop(BCT, NORM_A, NORM_B, NORM), 
  apply_uop(SIGN, NORM, SF), 
  fps(SF, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

esimp_fork_qtf((HYP_A, HYP_B, GOAL), (HYP_A, HYP_L, GOAL_L), (HYP_R, HYP_B, GOAL_R)) :- 
  hyp_sign_form(HYP_A, SIGN, FORM), 
  decom_qtf(FORM, QTF, SUB_FORM), 
  esimp(SUB_FORM, SUB_NORM),
  apply_uop(QTF, SUB_NORM, NORM), 
  apply_uop(SIGN, NORM, SF), 
  fps(SF, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

esimp_qtf(X) :- 
  para_lc(X) -> true ;
  para_m(X) -> true ;
  para_c_(X, Y) ->
  esimp_qtf(Y) ;
  para_d_(X, Y) ->
  esimp_qtf(Y).

esimp(X) :- 
  para_lc(X) -> true ;
  para_m(X) -> true ;
  esimp_fork_not(X, Y, Z) -> 
  para_s_(Y, Y1),
  para__s(Y1, Y2), 
  esimp(Y2), 
  esimp_not(Z)
;
  esimp_fork_bct(X, Y, Z) -> 
  paraab(Y, Y1, Y2), 
  esimp(Y1), 
  esimp(Y2), 
  esimp_bct(Z)
;
  esimp_fork_qtf(X, Y, Z) -> 
  paracd(Y, Y1), 
  esimp(Y1), 
  esimp_qtf(Z).

mscj(H2G) :- 
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> mscj(H2G_N) ;
  para__d(H2G, H2G_N) -> mscj(H2G_N) ;
  para_c_(H2G, H2G_N) -> mscj(H2G_N) ;
  a_para(H2G, H2G_N),
  mscj(H2G_N).

lit_map_lit(LIT, LIT).
lit_map_lit(TERM_A = TERM_B, TERM_B = TERM_A).
lit_map_lit($not(TERM_A = TERM_B), $not(TERM_B = TERM_A)).

lit_mappable_lit(LIT_A, LIT_B) :- unifiable(LIT_A, LIT_B, _).
lit_mappable_lit(TERM_A = TERM_B, LIT) :- unifiable(TERM_B = TERM_A, LIT, _).
lit_mappable_lit($not(TERM_A = TERM_B), LIT) :- unifiable($not(TERM_B = TERM_A), LIT, _).

lits_map_lits([], _).

lits_map_lits([LIT | LITS_A], LITS_B) :- 
  lit_map_lits(LIT, LITS_B), 
  lits_map_lits(LITS_A, LITS_B).

lit_map_lits(LIT_A, [LIT_B | _]) :- 
  lit_map_lit(LIT_A, LIT_B).

lit_map_lits(LIT_A, [LIT_B | LITS]) :- 
  lit_mappable_lit(LIT_A, LIT_B) -> 
  nonground(LIT_A, _), 
  lit_map_lits(LIT_A, LITS) 
;
  lit_map_lits(LIT_A, LITS).

% report_success(X) :- 
%   format("FOUND : ~w\n\n", X).

subsume_cla(LITS_A, (ID, LITS_B), ID) :- 
  copy_term(LITS_B, LITS_C),
  lits_map_lits(LITS_C, LITS_A), 
  % report_success(LITS_C), 
  !.

find_subsumer(CNT, CLAS, (_, $neg(FORM)), ID) :- 
  inst_with_pars(CNT, FORM, _, BODY), !, 
  body_lits(BODY, LITS, []), !, 
  try(subsume_cla(LITS), CLAS, ID).

orig_aux(PREM, GOAL, CONC) :- 
  infer(_, id, [PREM], _, CONC, GOAL) ;
  pmt_cla(PREM, CONC, GOAL) ;
  para_clausal(v, (PREM, CONC, GOAL)).



%%%%%%%%%%%%%%%% MAIN PROOF COMPILATION %%%%%%%%%%%%%%%%

infer(e, para_dist, [PREM], _, CONC, GOAL) :- 
  para_dist(PREM, CONC, GOAL).

infer(_, para_pull, [PREM], _, CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP], GOAL_T), 
  para_pull((PREM, HYP, GOAL_T)).

infer(e, para_e1, [PREM], _, CONC, GOAL) :- 
  para_e1((PREM, CONC, GOAL)).

infer(e, para_e2, [PREM], _, CONC, GOAL) :- 
  para_e2((PREM, CONC, GOAL)).

infer(e, para_push, [PREM], _, CONC, GOAL) :-
  para_push((PREM, CONC, GOAL)). 

infer(_, rnm, [PREM | _], _, CONC, GOAL) :- 
  mate(PREM, CONC, GOAL).

infer(e, simp, [PREM | _], _, CONC, GOAL) :- 
  esimp((PREM, CONC, GOAL)).

infer(PRVR, skm, [PREM | AOCS], _, CONC, GOAL) :- 
  PRVR = e -> 
  eskm(AOCS, (PREM, CONC, GOAL)) 
;
  many_nb([d], [CONC], GOAL, [CONC_N], GOAL1), 
  % many_nb([c], [PREM], GOAL1, [PREM_N], GOAL2), 
  skm(AOCS, (PREM, CONC_N, GOAL1)).

infer(_, ngt, [PREM], _, CONC, GOAL) :- 
  sp(CONC, GOAL, TEMP, GOAL_T), 
  mate(PREM, TEMP, GOAL_T).
  
infer(_, dff, [PREM | PREMS], _, CONC, GOAL) :- 
  sort(PREMS, DEFS),
  dff(DEFS, PREM, CONC, GOAL).

infer(_, dfu, [PREM | PREMS], _, CONC, GOAL) :- 
  dfu(PREMS, PREM, CONC, GOAL).

infer(v, sat, PREMS, _, _, GOAL) :-
  sat(PREMS, GOAL).
  
infer(m, subst, [PREM], _, CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP_C], GOAL0), 
  many_nb([c], [PREM], GOAL0, [HYP_P], GOAL1), 
  ( 
    mate(HYP_P, HYP_C, GOAL1) ;
    pblx(p, [HYP_P, HYP_C], GOAL1)
  ).

infer(m, eq, [], _, CONC, GOAL) :-
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  pluck(HYPS, EQ, [HYP_A, HYP_B]),
  EQ = (_, $pos(_ = _)), 
  subst_rel_mul(HYP_A, [EQ], HYP_B, GOAL_T, []). 

infer(m, refl, [], _, CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP], GOAL_T), 
  eq_refl(HYP, GOAL_T).

infer(_, rwa, [PREM_A, PREM_B], _, CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP_C], GOAL_C), 
  many_nb([c], [PREM_B], GOAL_C, [HYP_B], GOAL_B), 
  many_nb([c], [PREM_A], GOAL_B, [HYP_A], GOAL_A), 
  rwa(HYP_B, (HYP_A, HYP_C, GOAL_A)).

infer(v, gaoc, AOCS, _, GAOC, GOAL) :- 
  many_nb([d], [GAOC], GOAL, [IMP], GOAL0), 
  IMP = (_, $neg($imp(_, _))),
  aap(IMP, GOAL0, ANTE, CONS, GOAL1), 
  apply_aocs(ANTE, AOCS, GOAL1, TEMP, GOAL2), 
  paral((TEMP, CONS, GOAL2)).
  
infer(PRVR, res, [PYP0, PYP1], _, NYP, GOAL) :- 
  member(PRVR, [v, e]),
  res(PYP0, PYP1, NYP, GOAL).

infer(_, id, PREMS, _, CONC, GOAL) :-
  member(PREM, PREMS),
  mate(PREM, CONC, GOAL), !.

infer(_, opmt, PREMS, CLAS, CONC, GOAL) :-
  snd(GOAL, CNT),
  find_subsumer(CNT, CLAS, CONC, ID),
  member((ID, HYP), PREMS), 
  pmt_cla((ID, HYP), CONC, GOAL), !.

infer(m, simplify, [PREM_A, PREM_B], _, CONC, GOAL) :- 
  res(PREM_A, PREM_B, CONC, GOAL).
  
infer(e, orig, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  orig_aux(PREM, GOAL, CONC).

infer(v, orig, PREMS, CLAS, CONC, GOAL) :- 
  infer(_, id, PREMS, CLAS, CONC, GOAL) ;
  infer(_, opmt, PREMS, CLAS, CONC, GOAL) ;
  infer(v, para_clausal, PREMS, CLAS, CONC, GOAL). 

infer(_, eqf, [PREM], _, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  pluck(HYPS, HYP, REST), 
  HYP = (_, $pos(_ = _)), 
  many([b, c, s], ([PREM], GOAL_T), HGS), 
  maplist(eqf(REST, HYP), HGS).

infer(_, eqr, [PREM], _, CONC, GOAL) :- 
  eqr(PREM, CONC, GOAL).

infer(v, updr, [PREM], _, CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [CONC_N], GOAL0),
  many_nb([c], [PREM], GOAL0, [PREM_N], GOAL1),
  (
    ap(PREM_N, l, GOAL1, PREM_D, GOAL2) ;
    ap(PREM_N, r, GOAL1, PREM_D, GOAL2)
  ),
  mate(PREM_D, CONC_N, GOAL2).

infer(e, fnnf, [PREM], _, CONC, GOAL) :- 
  fnnf((PREM, CONC, GOAL)).

infer(_, rwe, [PREM_L, PREM_R], _, CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [TEMP_C], GOAL0), 
  many_nb([c], [PREM_L], GOAL0, [TEMP_L], GOAL1), 
  many_nb([d], [TEMP_L], GOAL1, [BODY_L], GOAL2), 
  many_nb([c], [TEMP_C], GOAL2, [BODY_C], GOAL3), 
  many_nb([c], [PREM_R], GOAL3, [BODY_R], GOAL4), 
  many_nb([a, s], [BODY_C], GOAL4, HYPS, GOAL5), 
  pick_pivot_prop(HYPS, BODY_L, GOAL5, SRC, GOAL6), 
  pick_pivot_prop(HYPS, BODY_R, GOAL6, PRE_EQN, GOAL7), 
  PRE_EQN = (_, $pos(_ = _)),
  erient_hyp(PRE_EQN, GOAL7, EQN, GOAL8),
  member_rev(TGT, HYPS),
  subst_rel_add([EQN], SRC, TGT, GOAL8). 
  
infer(_, (sup, DIR), [PREM_A, PREM_B], _, CONC, GOAL) :- 
  orient_dir(PREM_A, PREM_B, DIR, PREM_L, PREM_R),
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL0), 
  pick_pivot(HYPS, PREM_L, GOAL0, SRC, GOAL1), 
  pick_pivot(HYPS, PREM_R, GOAL1, PRE_EQN, GOAL2), 
  PRE_EQN = (_, $pos(_ = _)),
  erient_hyp(PRE_EQN, GOAL2, EQN, GOAL3),
  member_rev(TGT, HYPS),
  subst_rel_add([EQN], SRC, TGT, GOAL3). 

infer(v, spl, [PREM | PREMS], _, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS0, GOAL0), 
  spl_exp(PREMS, HYPS0, GOAL0, HYPS1, GOAL1),
  append(HYPS0, HYPS1, HYPS),
  pblx(q, [PREM | HYPS], GOAL1).

infer(_, para, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  para((PREM, CONC, GOAL)).

infer(_, sbsm, [PREM], _, CONC, GOAL) :- 
  sbsm(PREM, CONC, GOAL).



  %  maplist(pick_mate(HYPS), HGS). 

infer(v, cnf, [PREM], _, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, TEMP), 
  vcnf(PREM, HYPS, TEMP).

infer(v, acc, [PREM], _, CONC, GOAL) :- 
  vacc(PREM, CONC, GOAL).

infer(v, ppr, [PREM], _, CONC, GOAL) :-
  % member(PREM, PREMS),
  ppr(PREM, CONC, GOAL) ;
  ppr((PREM, CONC, GOAL)).

infer(v, paras, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  para_switch((PREM, CONC, GOAL)).

infer(v, paral, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  paral((PREM, CONC, GOAL)).

infer(v, parav, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  parav((PREM, CONC, GOAL)).

infer(_, mscj, [PREM], _, CONC, GOAL) :- 
  mscj((PREM, CONC, GOAL)).

infer(e, speq, [PREM], _, CONC, GOAL) :- 
  speq((PREM, CONC, GOAL)).

infer(_, scj, [PREM], _, CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [HYP0], GOAL0), 
  many_nb([c], [PREM], GOAL0, [HYP1], GOAL1), 
  scj((HYP1, HYP0, GOAL1)).

infer(v, vnnf, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  vnnf((PREM, CONC, GOAL)).


infer(PRVR, para_clausal, PREMS, _, CONC, GOAL) :- 
  many_nb([d, s], [CONC], GOAL, [HYP_C], GOAL_C), 
  member(PREM, PREMS),
  many_nb([c, s], [PREM], GOAL_C, [HYP_P], GOAL_P), 
  para_clausal(PRVR, (HYP_P, HYP_C, GOAL_P)).

infer(_, paratf, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  paratf((PREM, CONC, GOAL)).

report_failure(MODE, PRVR, HINTS, PREMS, CLAS, CONC, PROB, PRF, GOAL) :- 
  write("\nInference failed, hints : "), 
  write(HINTS), 
  write("\n\n"), 
  (
    MODE = verbose ->
    write("\nInference failed, premises :\n\n"),
    write_list(PREMS)
  ;
    true
  ),
  write("Inference failed, conclusion = "), 
  write(CONC), 
  write("\n\n"),
  (
    MODE = verbose ->
    open("temp_trace", write, Stream), 
    write(Stream, ":- [basic].\n\n"), 
    format(Stream, '~w.\n\n', debug_prvr(PRVR)), 
    format(Stream, '~w.\n\n', debug_hints(HINTS)), 
    format(Stream, '~w.\n\n', debug_ctx(PREMS)), 
    format(Stream, '~w.\n\n', debug_clas(CLAS)), 
    format(Stream, '~w.\n\n', debug_hyp(CONC)), 
    format(Stream, '~w.\n\n', debug_goal(GOAL)), 
    format(Stream, '~w.\n\n', debug_prob(PROB)), 
    format(Stream, '~w.\n\n', debug_prf(PRF)), 
    close(Stream), 
    open("temp_trace", read, STRM_R), 
    open("proof_trace.pl", write, STRM_W), 
    quote_par(STRM_R, STRM_W), 
    close(STRM_R),
    close(STRM_W),
    delete_file("temp_trace"),
    throw(compilation_timeout)
  ;
    true
  ).

subprove(STRM, PRVR, OCLAS, CNT, HINT, PREMS, FORM) :-   
  % format("Adding lemma ~w\n\n", CID),
  mk_par(CNT, [], CID),
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  num_succ(CNT, SCNT),
  GOAL = (PRF, SCNT), 
  timed_call(
    30,
    infer(PRVR, HINT, PREMS, OCLAS, (CID, $neg(FORM)), GOAL), 
    (
      report_failure(fast, PRVR, HINT, PREMS, OCLAS, (CID, $neg(FORM)), none, none, GOAL), 
      false
    )
  ), !,
  ground_all(c, PRF),
  % put_assoc(CID, PROB, $neg(FORM), SUB_PROB),
  % (
  %   check_term(SUB_PROB, SCNT, PRF) ->  true ; 
  %   format("ID at error = ~w\n\n", CID),
  %   format("Prob at error = ~w\n\n", SUB_PROB),
  %   throw(invalid_subproof)
  %   % report_failure(fast, PRVR, HINTS, CTX, (CID, $neg(FORM)), SUB_PROB, PRF, GOAL)
  % ),
  put_prf(STRM, PRF). 

set_tup_nth(0, (_, Y), X, (X, Y)) :- !.
set_tup_nth(NUM, (X, T0), Y, (X, T1)) :- 
  num_pred(NUM, PRED), 
  set_tup_nth(PRED, T0, Y, T1).

get_tup_nth(0, (X, _), X) :- !.
get_tup_nth(NUM, (_, TUP), ELEM) :- 
  num_pred(NUM, PRED), 
  get_tup_nth(PRED, TUP, ELEM).

% PS = (PROB, SOL, LAST, STRM, PRVR, OHYPS, OCLAS, nil)
get_ps_prob(PS, PROB)  :- get_tup_nth(0, PS, PROB).
get_ps_sol(PS, SOL)    :- get_tup_nth(1, PS, SOL).
get_ps_last(PS, LAST)  :- get_tup_nth(2, PS, LAST).
get_ps_strm(PS, STRM)  :- get_tup_nth(3, PS, STRM).
get_ps_prvr(PS, PRVR)  :- get_tup_nth(4, PS, PRVR).
get_ps_ohyps(PS, HYPS) :- get_tup_nth(5, PS, HYPS).
get_ps_oclas(PS, CLAS) :- get_tup_nth(6, PS, CLAS).

set_ps_prob(PS_O, PROB, PS_N)  :- set_tup_nth(0, PS_O, PROB, PS_N).
set_ps_sol(PS_O, SOL, PS_N)    :- set_tup_nth(1, PS_O, SOL, PS_N).
set_ps_last(PS_O, LAST, PS_N)  :- set_tup_nth(2, PS_O, LAST, PS_N).

use_inst(PS, CNT, add(FORM), PS_N) :- 
  get_ps_prob(PS, PROB),
  get_ps_strm(PS, STRM),
  mk_par(CNT, [], CID),
  justified(CNT, $pos(FORM)),
  put_char(STRM, 'T'), 
  put_sf(STRM, $pos(FORM)), 
  put_assoc(CID, PROB, $pos(FORM), PROB_N), 
  set_ps_prob(PS, PROB_N, PS1), 
  set_ps_last(PS1, CID, PS_N), 
  true.
  
use_inst(PS, CNT, inf(HINT, IDS, FORM), PS_N) :- 
  get_ps_prvr(PS, PRVR),
  get_ps_strm(PS, STRM),
  get_ps_prob(PS, PROB),
  % format("Constructing subproof with ID = ~w, hint = ~w\n\n", [CNT, HINT]),
  get_ps_oclas(PS, OCLAS),
  (
    IDS == $orig -> 
    get_ps_ohyps(PS, PREMS) ;
    get_context(PROB, IDS, PREMS)
  ),
  subprove(STRM, PRVR, OCLAS, CNT, HINT, PREMS, FORM),
  mk_par(CNT, [], CID),
  put_assoc(CID, PROB, $pos(FORM), PROB_N),
  set_ps_prob(PS, PROB_N, PS1), 
  set_ps_last(PS1, CID, PS_N), 
  true.

use_inst(PS, _, del(ID), PS_N) :- 
  % format("Deleting lemma ~w\n\n", PID),
  get_ps_strm(PS, STRM),
  get_ps_prob(PS, PROB_O),
  put_char(STRM, 'W'), 
  put_id(STRM, ID), 
  del_assoc(ID, PROB_O, _, PROB_N), !, 
  set_ps_prob(PS, PROB_N, PS_N).
  
prove(PS0, NUM) :- 
  get_ps_sol(PS0, [INST | SOL]), 
  set_ps_sol(PS0, SOL, PS1), !, 
  use_inst(PS1, NUM, INST, PS2), !, 
  num_succ(NUM, SUCC),
  prove(PS2, SUCC).

prove(PS, NUM) :- 
  get_ps_sol(PS, []), 
  get_ps_strm(PS, STRM), 
  get_ps_last(PS, LAST),
  mk_par(NUM, [], CID),
  put_prf(STRM, t($neg($false), x(LAST, CID))).

para_push(TRP) :- 
  para_m(TRP) -> true 
;
  paraab(TRP, TRP_L, TRP_R) -> 
  para_push(TRP_L), !,
  para_push(TRP_R)
;
  TRP = (PREM, CONC, GOAL), 
  PREM = (_, $pos($fa(FORM))), 
  push_qtf(FORM, NORM),
  fp($fa(NORM), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP_L0 = (PREM, HYP_A, GOAL_A), 
  paracd(TRP_L0, TRP_L1),
  para_push(TRP_L1), 
  para_dist_fa((HYP_B, CONC, GOAL_B))
;
  TRP = (PREM, CONC, GOAL), 
  PREM = (_, $pos($ex(FORM))), 
  push_qtf(FORM, NORM), 
  fp($ex(NORM), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP_L0 = (PREM, HYP_A, GOAL_A), 
  para_dc(TRP_L0, TRP_L1),
  para_push(TRP_L1), 
  para_dist_ex((HYP_B, CONC, GOAL_B)).

para_dist_ex(TRP) :- para_m(TRP).

para_dist_ex(TRP) :- 
  para_d_(TRP, TRP_T), 
  para_m(TRP_T).

para_dist_ex((PREM, CONC, GOAL)) :- 
  PREM = (_, $pos($ex($or(FORM_A, FORM_B)))), !, 
  fp($or($ex(FORM_A), $ex(FORM_B)), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para_d_(TRP, TRP_0), 
  para_ba(TRP_0, TRP_L0, TRP_R0),
  para__c(TRP_L0, TRP_L1), 
  para_m(TRP_L1), 
  para__c(TRP_R0, TRP_R1),
  para_m(TRP_R1), 
  para_ba((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_ex(TRP_A),
  para_dist_ex(TRP_B).

para_dist_ex((PREM, CONC, GOAL)) :- 
  PREM = (_, $pos($ex($and(FORM_A, FORM_B)))),
  decr_vdx_form(FORM_A, _), !, 
  fp($and(FORM_A, $ex(FORM_B)), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para_d_(TRP, TRP0),
  para_ab(TRP0, TRP_L, TRP_R), 
  para__c(TRP_R, TRP_R0), 
  para_m(TRP_L), 
  para_m(TRP_R0), 
  para_ab((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_ex(TRP_A), 
  para_dist_ex(TRP_B).
  
para_dist_ex((PREM, CONC, GOAL)) :- 
  PREM = (_, $pos($ex($and(FORM_A, FORM_B)))), 
  decr_vdx_form(FORM_B, _), !, 
  fp($and($ex(FORM_A), FORM_B), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para_d_(TRP, TRP0),
  para_ab(TRP0, TRP_L, TRP_R), 
  para__c(TRP_L, TRP_L0), 
  para_m(TRP_L0), 
  para_m(TRP_R), 
  para_ab((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_ex(TRP_A), 
  para_dist_ex(TRP_B). 

para_dist_fa(TRP) :- para_m(TRP).

para_dist_fa(TRP) :- 
  para_c_(TRP, TRP_T),
  para_m(TRP_T).

para_dist_fa((PREM, CONC, GOAL)) :- 
  PREM = (_, $pos($fa($and(FORM_A, FORM_B)))), !, 
  fp($and($fa(FORM_A), $fa(FORM_B)), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para__b(TRP, TRP_L0, TRP_R0),
  para__d(TRP_L0, TRP_L1), 
  para_c_(TRP_L1, TRP_L2), 
  para_a_(l, TRP_L2, TRP_L3),
  para_m(TRP_L3), 
  para__d(TRP_R0, TRP_R1), 
  para_c_(TRP_R1, TRP_R2), 
  para_a_(r, TRP_R2, TRP_R3), 
  para_m(TRP_R3), 
  para_ab((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_fa(TRP_A),
  para_dist_fa(TRP_B).

para_dist_fa((PREM, CONC, GOAL)) :- 
  PREM = (_, $pos($fa($or(FORM_A, FORM_B)))), 
  decr_vdx_form(FORM_A, _), !, 
  fp($or(FORM_A, $fa(FORM_B)), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  aap(HYP_A, GOAL_A, HYP_L, HYP_R, GOAL_0), 
  dp(HYP_R, GOAL_0, HYP_NR, GOAL_1), 
  cp(PREM, _, GOAL_1, PREM_N, GOAL_2), 
  bp(PREM_N, GOAL_2, PREM_L, PREM_R, GOAL_3, GOAL_4), 
  mate(PREM_L, HYP_L, GOAL_3), 
  mate(PREM_R, HYP_NR, GOAL_4), 
  para_ba((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_fa(TRP_A),
  para_dist_fa(TRP_B).

para_dist_fa((PREM, CONC, GOAL)) :- 
  PREM = (_, $pos($fa($or(FORM_A, FORM_B)))), 
  decr_vdx_form(FORM_B, _), !, 
  fp($or($fa(FORM_A), FORM_B), GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  aap(HYP_A, GOAL_A, HYP_L, HYP_R, GOAL_0), 
  dp(HYP_L, GOAL_0, HYP_NL, GOAL_1), 
  cp(PREM, _, GOAL_1, PREM_N, GOAL_2), 
  bp(PREM_N, GOAL_2, PREM_L, PREM_R, GOAL_3, GOAL_4), 
  mate(PREM_L, HYP_NL, GOAL_3), 
  mate(PREM_R, HYP_R, GOAL_4), 
  para_ba((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_fa(TRP_A),
  para_dist_fa(TRP_B).

para_pull(H2G) :- 
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> para_pull(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R) -> 
  para_pull(H2G_L), !, para_pull(H2G_R) ;
  para_c_(H2G, H2G_N),
  para_pull(H2G_N).

para_dist_aux(ANTE, CONS, GOAL_I, HYP_O, GOAL_O) :- 
  fp($imp(ANTE, CONS), GOAL_I, HYP_T, HYP_O, GOAL_T, GOAL_O), 
  aap(HYP_T, GOAL_T, PREM, CONC, GOAL_N),
  para_dist(PREM, CONC, GOAL_N), !. 

para_dist_help(A_OR_B, A_TO_P, B_TO_Q, GOAL, P, Q, GOAL_P, GOAL_Q) :- 
  bp(A_OR_B, GOAL, A, B, GOAL_A, GOAL_B),
  bp(A_TO_P, GOAL_A, NA, P, GOAL_ANA, GOAL_P),
  mate(A, NA, GOAL_ANA), 
  bp(B_TO_Q, GOAL_B, NB, Q, GOAL_BNB, GOAL_Q),
  mate(B, NB, GOAL_BNB). 

para_dist_close(DIR, HYP_P, HYP_Q, CONC, GOAL) :- 
  bp(CONC, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R),
  ap(HYP_L, DIR, GOAL_L, HYP_NP, GOAL_NP), 
  mate(HYP_P, HYP_NP, GOAL_NP),
  ap(HYP_R, DIR, GOAL_R, HYP_NQ, GOAL_NQ), 
  mate(HYP_Q, HYP_NQ, GOAL_NQ).

para_dist(PREM, CONC, GOAL) :- 
  mate(PREM, CONC, GOAL) -> true  
;
  cdp(PREM, CONC, GOAL, PREM_N, CONC_N, GOAL_N) ->
  para_dist(PREM_N, CONC_N, GOAL_N), !
;
  hyp_sf(PREM, $pos($and(_, _))) -> 
  abpl(PREM, CONC, GOAL, PREM_L, CONC_L, GOAL_L, PREM_R, CONC_R, GOAL_R), 
  para_dist(PREM_L, CONC_L, GOAL_L),
  para_dist(PREM_R, CONC_R, GOAL_R), ! 
; 
  hyp_sf(PREM, $pos($or(FORM_A, FORM_B))),
  distribute(FORM_A, TEMP_A),  
  distribute(FORM_B, TEMP_B),
  para_dist_aux(FORM_A, TEMP_A, GOAL, HYP_A, GOAL_A), 
  para_dist_aux(FORM_B, TEMP_B, GOAL_A, HYP_B, GOAL_B), 
  (
    TEMP_A = $and(FORM_L, FORM_R) -> 
    fp($and($or(FORM_L, TEMP_B), $or(FORM_R, TEMP_B)), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 

    % [FORM_A, FORM_B, FORM_L, FORM_R, TEMP_B] = PAS, 
    % ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 

    para_dist_help(PREM, HYP_A, HYP_B, GOAL_T, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    aap(HYP_TA, GOAL_TA, HYP_FL, HYP_FR, GOAL_FLR), 
    para_dist_close(l, HYP_FL, HYP_FR, HYP_T, GOAL_FLR), 
    para_dist_close(r, HYP_TB, HYP_TB, HYP_T, GOAL_TB), 
    para_dist(HYP_C, CONC, GOAL_C), !

    % PREM : FA | FB, 
    % HYP_A : FA => (FL & FR), 
    % HYP_B : FB => TB, 
    % |- HYP_T : (FL | TB) & (FR | TB)
    
  ;
    TEMP_B = $and(FORM_L, FORM_R) -> 
    fp($and($or(FORM_L, TEMP_A), $or(FORM_R, TEMP_A)), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 

    % [FORM_A, FORM_B, TEMP_A, FORM_L, FORM_R] = PAS,
    % ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 

    para_dist_help(PREM, HYP_A, HYP_B, GOAL_T, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    aap(HYP_TB, GOAL_TB, HYP_FL, HYP_FR, GOAL_FLR), 
    para_dist_close(l, HYP_FL, HYP_FR, HYP_T, GOAL_FLR), 
    para_dist_close(r, HYP_TA, HYP_TA, HYP_T, GOAL_TA), 
    para_dist(HYP_C, CONC, GOAL_C), !

    % PREM : FA | FB, 
    % HYP_A : FA => TA, 
    % HYP_B : FB => (FL & FR), 
    % |- HYP_T : (FL | TA) & (FR | TA)
    
  ;
    para_dist_help(PREM, HYP_A, HYP_B, GOAL_B, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    ap(CONC, l, GOAL_TA, HYP_NTA, GOAL_NTA), 
    mate(HYP_TA, HYP_NTA, GOAL_NTA), 
    ap(CONC, r, GOAL_TB, HYP_NTB, GOAL_NTB), 
    mate(HYP_TB, HYP_NTB, GOAL_NTB)
  ).  

% dummy :- 
%   prove(_),
%   random_pluck(_, _, _),
%   tt_term(_, _, _),
%   maplist_count(_, _, _, _, _, _),
%   atom_firstchar(_, _),
%   inst_with_lvs(_, _),
%   names_from_e(_, _),
%   names_from_s(_, _),
%   tptp_name(_, _),
%   first_char(_, _),
%   path_cat(_, _),
%   path_cat_id(_, _, _),
%   solve(_, _, _),
%   true.