:- [basic].

term_poseq_term(Var, _) :- var(Var), !.
term_poseq_term(_, Var) :- var(Var), !.
term_poseq_term((FUN $ TERMS_A), (FUN $ TERMS_B)) :- 
  length(TERMS_A, LTH),
  length(TERMS_B, LTH).

term_poseq_term(_, TERM_A, TERM_B) :- 
  term_poseq_term(TERM_A, TERM_B).
term_poseq_term(OPQEs, TERM_A, TERM_B) :- 
  member((_, QE), OPQEs), 
  inst_with_lvs(QE, ("=" $ [TERM_L, TERM_R])),
  ( 
    term_poseq_term(TERM_A, TERM_L) ; 
    term_poseq_term(TERM_A, TERM_R) ; 
    term_poseq_term(TERM_B, TERM_R) ; 
    term_poseq_term(TERM_B, TERM_L) 
  ).



%%%%%%% Decomposition to Equational goals %%%%%%%

intro_eqs(MONO, [], [], GOAL, MONO, [], GOAL).

intro_eqs(MONO, [TERM_A | TERMS_A], [TERM_B | TERMS_B], GOAL, Iff, [(ONE, SubGOAL) | HGS], GOAL_N) :-
  apply_c(MONO, TERM_A, GOAL, MONOA, GOAL_A), 
  apply_c(MONOA, TERM_B, GOAL_A, MONOAB, GOAL_AB), 
  apply_b(MONOAB, GOAL_AB, ONE, TempMONO, SubGOAL, GOAL_T), 
  intro_eqs(TempMONO, TERMS_A, TERMS_B, GOAL_T, Iff, HGS, GOAL_N). 

break_eq_fun(OPEs, ONE, GOAL, HGS) :- 
  ONE = (_, ~ (("=" $ [TERM_A, TERM_B]))),
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A = (FUN $ TERMS_A),
  TERM_B = (FUN $ TERMS_B),
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  cmap(term_poseq_term(OPEs), TERMS_A, TERMS_B),
  mk_mono_fun(LTH, FUN, MONOForm),
  apply_t(MONOForm, GOAL, MONO, GOAL0),
  intro_eqs(MONO, TERMS_A, TERMS_B, GOAL0, OPE, HGS, GOAL1),
  apply_x(OPE, ONE, GOAL1).

break_eq_rel(OPEs, OPA, ONA, GOAL, HGS) :- 
  OPA = (_, (REL $ TERMS_A)),
  ONA = (_, ~ ((REL $ TERMS_B))),
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  cmap(term_poseq_term(OPEs), TERMS_A, TERMS_B),
  mk_mono_rel(LTH, REL, MONOForm),
  apply_t(MONOForm, GOAL, MONO, GOAL0),
  intro_eqs(MONO, TERMS_A, TERMS_B, GOAL0, IMP, HGS, GOAL1),
  apply_b(IMP, GOAL1, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  apply_x(OPA, HYP_L, GOAL_L), 
  apply_x(HYP_R, ONA, GOAL_R). 

subst_fun_mul(OPEs, ONE, GOAL, NewOPEs) :-
  ONE = (_, ~ (("=" $ [TERM_A, TERM_B]))), 
  (
    TERM_A == TERM_B -> 
    (eq_refl(ONE, GOAL), NewOPEs = OPEs) ;
    subst_fun_mul_0(OPEs, ONE, GOAL, NewOPEs)
  ).

subst_fun_mul_0(OPEs, ONF, GOAL, OPEs) :- 
  ONF = (_, ~ (("=" $ [TERM_A, TERM_B]))), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONF, GOAL).

subst_fun_mul_0(OPEs, ONE, GOAL, NewOPEs) :-
  break_eq_fun(OPEs, ONE, GOAL, HGS),
  subst_fun_mul_aux(OPEs, HGS, NewOPEs). 

subst_fun_mul_0(OPQEs, ONE, GOAL, NewOPQEs) :- 
  ONE = (_, ~ (("=" $ [TERM_A0, TERM_C]))), 
  pluck_uniq(OPQEs, OPQE, REST),
  rp([c], [OPQE], GOAL, [PRE_OPE], GOAL_T), 
  PRE_OPE = (_, (("=" $ [_, _]))),
  orient_hyp(PRE_OPE, GOAL_T, OPE, GOAL0),
  OPE = (_, (("=" $ [TERM_A1, TERM_B]))),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  apply_s(("=" $ [TERM_B, TERM_C]), GOAL0, NewONE, NewOPE, GOAL1, GOAL2), 
  subst_fun_mul(REST, NewONE, GOAL1, NewOPQEs), 
  eq_trans(OPE, NewOPE, ONE, GOAL2).

subst_fun_mul_aux(OPEs, [], OPEs).

subst_fun_mul_aux(OPEs, [(ONE, GOAL) | HGS], NewOPEs) :-
  subst_fun_mul(OPEs, ONE, GOAL, TempOPEs),
  subst_fun_mul_aux(TempOPEs, HGS, NewOPEs).

subst_rel_mul(HYP_L, OPEs, HYP_R, GOAL, NewOPEs) :-  
  orient_literal_hyps(HYP_L, HYP_R, PreOPA, ONA),
  orient_hyp(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel(OPEs, OPA, ONA, GOAL_T, HGS),
  subst_fun_mul_aux(OPEs, HGS, NewOPEs). 

subst_fun_add(EQNS, (HYP, GOAL)) :-
  subst_fun_add(EQNS, HYP, GOAL).

subst_fun_add(EQNS, ONE, GOAL) :-
  ONE = (_, ~ (("=" $ [TERM_A, TERM_B]))), 
  (
    TERM_A == TERM_B -> 
    eq_refl(ONE, GOAL) ;
    subst_fun_add_0(EQNS, ONE, GOAL)
  ).

subst_fun_add_0(_, ONF, GOAL) :- 
  ONF = (_, ~ (("=" $ [TERM_A, TERM_B]))), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONF, GOAL).

subst_fun_add_0(EQNS, ONE, GOAL) :-
  break_eq_fun(EQNS, ONE, GOAL, HGS),
  maplist(subst_fun_add(EQNS), HGS). 

subst_fun_add_0(OPQEs, ONE, GOAL) :- 
  ONE = (_, ~ (("=" $ [TERM_A0, TERM_C]))), 
  pluck_uniq(OPQEs, OPQE, REST),
  rp([c], [OPQE], GOAL, [PRE_OPE], GOAL_T), 
  PRE_OPE = (_, (("=" $ [_, _]))),
  orient_hyp(PRE_OPE, GOAL_T, OPE, GOAL0),
  OPE = (_, (("=" $ [TERM_A1, TERM_B]))),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  apply_s(("=" $ [TERM_B, TERM_C]), GOAL0, NewONE, NewOPE, GOAL1, GOAL2), 
  subst_fun_add(REST, NewONE, GOAL1), 
  eq_trans(OPE, NewOPE, ONE, GOAL2).

subst_rel_add(EQNS, HYP_L, HYP_R, GOAL) :-  
  orient_literal_hyps(HYP_L, HYP_R, PreOPA, ONA),
  orient_hyp(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel(EQNS, OPA, ONA, GOAL_T, HGS),
  maplist(subst_fun_add(EQNS), HGS).

pick_pivot(HYPS, HYP, GOAL, HYP_N, GOAL_N) :-
  rp([b, c, n], [HYP], GOAL, HGS),
  pluck(HGS, ([HYP_N], GOAL_N), REST), 
  maplist(pick_mate(HYPS), REST). 

pick_pivot_prop(HYPS, HYP, GOAL, HYP_N, GOAL_N) :-
  rp([b, n], [HYP], GOAL, HGS),
  pluck(HGS, ([HYP_N], GOAL_N), REST), 
  maplist(pick_mate(HYPS), REST). 

apply_aocs(ANTE, [AOC | AOCS], GOAL_I, CONS, GOAL_O) :-  
  rp([c], [AOC], GOAL_I, [IMP], GOAL_T),
  apply_b(IMP, GOAL_T, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  mate(ANTE, HYP_L, GOAL_L), 
  apply_aocs(HYP_R, AOCS, GOAL_R, CONS, GOAL_O).

apply_aocs(HYP, [], GOAL, HYP, GOAL). 

vcnf(PREM, HYPS, GOAL) :- 
  apply_n(PREM, GOAL, PREM_N, GOAL_N), !,
  vcnf(PREM_N, HYPS, GOAL_N).
 
vcnf(PREM, HYPS, GOAL) :- 
  apply_b(PREM, GOAL, PREM_A, PREM_B, GOAL_A, GOAL_B), !,
  vcnf(PREM_A, HYPS, GOAL_A),
  vcnf(PREM_B, HYPS, GOAL_B).

vcnf(PREM, HYPS, GOAL) :- 
  apply_c(PREM, _, GOAL, PREM_N, GOAL_N), !, 
  vcnf(PREM_N, HYPS, GOAL_N).

vcnf(PREM, HYPS, GOAL) :- 
  member(DIR, [true, false]),
  apply_a(PREM, DIR, GOAL, PREM_N, GOAL_N),
  vcnf(PREM_N, HYPS, GOAL_N).

vcnf(PREM, HYPS, GOAL) :- 
  member(HYP, HYPS), 
  mate(PREM, HYP, GOAL).

vacc_aux(TRP) :- 
  para__n(TRP, TRP_N) ->
  mate(TRP_N) ;
  mate(TRP).

vacc_aux((PREM, CONC, GOAL)) :- 
  pmt_cla(PREM, CONC, GOAL).

vacc(PREM, CONC, GOAL) :- 
  rp([d], [CONC], GOAL, [CONC_N], GOAL1), 
  rp([c], [PREM], GOAL1, [PREM_T], GOAL2), 
  member(DIR, [true, false]),
  apply_a(PREM_T, DIR, GOAL2, PREM_N, GOAL3), 
  paraab_choice((PREM_N, CONC_N, GOAL3), TRP_A, TRP_B),
  vacc_aux(TRP_A),
  vacc_aux(TRP_B).

pmt_cla(PREM, CONC, GOAL) :- 
  rp([a, d, n], [CONC], GOAL, HYPS, GOAL_T), 
  rp([b, c, n], [PREM], GOAL_T, HGS), 
  maplist(pick_mate(HYPS), HGS).

res(PYP0, PYP1, NYP, GOAL) :- 
  rp([a, d, n], [NYP], GOAL, HYPS, GOAL_T), 
  (
    res_core(PYP0, PYP1, HYPS, GOAL_T) ;
    res_core(PYP1, PYP0, HYPS, GOAL_T)
  ), !.

res_core(PYP0, PYP1, HYPS, GOAL) :- 
  apply_s(_, GOAL, NPVT, PPVT, GOAL_N, GOAL_P), 
  rp([b, c, n], [PYP0], GOAL_N, HGS0), 
  rp([b, c, n], [PYP1], GOAL_P, HGS1), !, 
  pluck(HGS0, ([HYP0], GOAL0), REST0), 
  mate_pn(HYP0, NPVT, GOAL0), 
  pluck(HGS1, ([HYP1], GOAL1), REST1), 
  mate_pn(PPVT, HYP1, GOAL1), 
  maplist(pick_mate([NPVT | HYPS]), REST0), 
  maplist(pick_mate([PPVT | HYPS]), REST1). 

dfu(DEFS, PREM, CONC, GOAL) :- 
  rp([a, d, n], [CONC], GOAL, HYPS, GOAL_T),
  rp([b, c, n], [PREM], GOAL_T, HGS),
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
    paran((HYP0, HYP1, DFP), (NewHYP0, NewHYP1, NewDFP)) ;
    paracd((HYP0, HYP1, DFP), (NewHYP0, NewHYP1, NewDFP))
  ), !,
  dff(Defs, NewHYP0, NewHYP1, NewDFP).

dff(Defs, HYP0, HYP1, GOAL) :- 
  paraab((HYP0, HYP1, GOAL), (HYP0L, HYP1L, GOAL_L), (HYP0R, HYP1R, GOAL_R)),
  dff(Defs, HYP0L, HYP1L, GOAL_L),
  dff(Defs, HYP0R, HYP1R, GOAL_R).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, Atom), 
  atomic_form(Atom), 
  member(Def, Defs), 
  rp([c], [Def], DFP, [IFF], DFP0),
  IFF = (_, ((Atom <> _))), !,
  apply_a(IFF, true, DFP0, IMP, DFP1), 
  apply_b(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Ante, DFP2), 
  dff(Defs, HYP0, Cons, DFP3).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, ~ Atom), 
  atomic_form(Atom), 
  member(Def, Defs), 
  rp([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, (Atom <> _)), !,
  apply_a(IFF, false, DFP0, IMP, DFP1), 
  apply_b(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Cons, DFP3), 
  dff(Defs, HYP0, Ante, DFP2).



%%%%%%%%%%%%%%%% SAT SOLVER %%%%%%%%%%%%%%%% 

lit_num(ANA, ~ ATOM, NEG) :- !,
  get_assoc(ATOM, ANA, NUM), 
  NEG is - NUM.

lit_num(ANA, ATOM, NUM) :- !,
  get_assoc(ATOM, ANA, NUM).

cla_hyp_nums(ANA, (_, CLA), NUMS) :- 
  cla_lits(CLA, LITS), 
  cmap(lit_num(ANA), LITS, NUMS). 

% cla_lits((_, CF), LITS) :- 
%   cf_lits(CF, LITS).

cla_hyp_atoms((_, CLA), ATOMS) :-
  cla_lits(CLA, LITS),
  cmap(lit_atom, LITS, ATOMS). 

add_to_sat_table(CH, TBL_I, TBL_O) :- 
  cla_hyp_atoms(CH, ATOMS), 
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
  foldl(add_to_sat_table, CHS, (1, EMP, EMP), (_, ANA, NAA)).
  
add_cla_hyp_to_ctx(CH, (NUM_I, CTX_I), (NUM_O, CTX_O)) :- 
  num_succ(NUM_I, NUM_O), 
  put_assoc(NUM_I, CTX_I, CH, CTX_O).

mk_sat_ctx(CHS, CTX) :- 
  empty_assoc(EMP), 
  foldl(add_cla_hyp_to_ctx, CHS, (1, EMP), (_, CTX)).
  
string_numbers(STR, NUMS) :- 
  split_string(STR, " ", "", STRS), 
  cmap(string_number, STRS, NUMS).

nums_dimacs(NUMS, Str) :- 
  maplist(number_string, NUMS, Strs),
  strings_concat_with(" ", Strs, TempStr),
  string_concat(TempStr, " 0", Str).

num_lit(NAA, NUM, LIT) :- 
  NUM < 0 -> 
  NEG is - NUM, 
  get_assoc(NEG, NAA, ATOM),
  LIT = ~ ATOM
;
  get_assoc(NUM, NAA, LIT).

lits_cla([], ff).
lits_cla(Lits, Cla) :- lits_cla_core(Lits, Cla).

lits_cla_core([Lit], Lit).
lits_cla_core([Lit | Lits], (Lit \/ Cla)) :- lits_cla_core(Lits, Cla).

nums_cla(NAA, NUMS, CLA) :- 
  cmap(num_lit(NAA), NUMS, LITS),
  lits_cla(LITS, CLA). 

line_sat_insts(_, LINE, SIS, SIS) :- 
  split_string(LINE, " ", "", [_, "d" | _]), !.

line_sat_insts(NAA, LINE, [rup(SIDS, SID, CLA) | SIS], SIS) :- 
  string_numbers(LINE, [SID | NUMS]),
  append(CLA_NUMS, [0 | REST], NUMS), 
  nums_cla(NAA, CLA_NUMS, CLA),
  append(SIDS, [0], REST). 
  
file_sat_insts(NAA, FILE, SIS) :-
  read_file_strings(FILE, LINES), 
  foldl(line_sat_insts(NAA), LINES, SIS, []).

nums_maxvar(NUMS, MaxVar) :-
  cmap(abs, NUMS, Nats),
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

find_new_unit_core([LIT], _, LIT) :- !.
find_new_unit_core([LIT_A | LITS_A], LITS_B, LIT) :- 
  member(LIT_B, LITS_B), 
  complements(LIT_A, LIT_B), !,
  find_new_unit_core(LITS_A, LITS_B, LIT). 
find_new_unit_core([LIT | _], _, LIT).

find_new_unit((_, FORM), HYPS, LIT) :- 
  cla_lits(FORM, LITS_A),
  cmap(hyp_form, HYPS, LITS_B), 
  find_new_unit_core(LITS_A, LITS_B, LIT).

unit_propagate(PREM, (HYPS_I, GOAL_I), ([HYP_O | HYPS_I], GOAL_O)) :- 
  find_new_unit(PREM, HYPS_I, LIT), 
  apply_s(LIT, GOAL_I, HYP_T, HYP_O, GOAL_T, GOAL_O),
  rp([n], [HYP_T], GOAL_T, [HYP_C], GOAL_C), 
  rp([b, n], [PREM], GOAL_C, HGS), 
  cmap(pick_mate([HYP_C | HYPS_I]), HGS).

get_sat_cla(CTX, SID, CLA) :- 
  get_assoc(SID, CTX, CLA).
  
put_sat_cla(CTX_I, SID, CLA, CTX_O) :- 
  put_assoc(SID, CTX_I, CLA, CTX_O).

use_sat_inst(CTX, del(_), GOAL, CTX, GOAL).

use_sat_inst(CTX, rup(SIDS, SID, CLA), GOAL, CTX_N, GOAL_N) :- 
  apply_s(CLA, GOAL, NYP, PYP, GOAL_T, GOAL_N), 
  put_sat_cla(CTX, SID, PYP, CTX_N),
  rp([a, n], [NYP], GOAL_T, HYPS_I, GOAL_I), 
  cmap(get_sat_cla(CTX), SIDS, PREMS), !,
  foldl_cut(unit_propagate, PREMS, (HYPS_I, GOAL_I), ([HYP | HYPS_O], GOAL_O)), !,
  member(CMP, HYPS_O),
  mate(HYP, CMP, GOAL_O), !.

use_sat_insts(CTX, [SI | SIS], GOAL) :- 
  use_sat_inst(CTX, SI, GOAL, CTX_N, GOAL_N), 
  (
    SIS = [] -> 
    SI = rup(_, SID, _), 
    get_sat_cla(CTX_N, SID, CLA), 
    use_pf(CLA, GOAL_N)
  ;
    use_sat_insts(CTX_N, SIS, GOAL_N)
  ).

sat(CHS, GOAL) :-
  mk_sat_tables(CHS, ANA, NAA),
  cmap(cla_hyp_nums(ANA), CHS, NUMSS),
  numss_dimacs(NUMSS, DIMACS),
  write_file("temp.cnf", DIMACS), !,
  shell("./cadical -q temp.cnf temp.drat", _), !,
  shell("./drat-trim temp.cnf temp.drat -L temp.lrat", _), !,

  write("Reading LRAT file...\n\n"),
  file_sat_insts(NAA, "temp.lrat", SIS), 

  write("Constructing SAT context...\n\n"),
  mk_sat_ctx(CHS, CTX), 

  write("Using SAT instructions...\n\n"),
  use_sat_insts(CTX, SIS, GOAL),
  delete_file("temp.cnf"),
  delete_file("temp.drat"),
  delete_file("temp.lrat"),
  true.


eskm(AOCS, H2G) :- 
  para_mate(H2G) -> true 
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
  rp([c], [AOC], GOAL, [HYP], GOAL_T), 
  apply_b(HYP, GOAL_T, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  apply_x(PREM, HYP_L, GOAL_L),
  eskm(REST, (HYP_R, CONC, GOAL_R)).

skm(AOCS, H2G) :- 
  para_mate(H2G) -> true 
;
  para_c_(H2G, H2G_N), 
  skm(AOCS, H2G_N)
;
  para_cd_lax(H2G, H2G_N), 
  skm(AOCS, H2G_N)
;
  paraab(H2G, H2G_L, H2G_R),
  skm(AOCS, H2G_L), 
  skm(AOCS, H2G_R)
;
  H2G = (PREM, CONC, GOAL),
  pluck(AOCS, AOC, REST),
  rp([c], [AOC], GOAL, [HYP], GOAL_T), 
  apply_b(HYP, GOAL_T, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  apply_x(PREM, HYP_L, GOAL_L),
  skm(REST, (HYP_R, CONC, GOAL_R)).



spl_exp([], [], GOAL, [], GOAL).

spl_exp([PREM | PREMS], HYPS_I, GOAL_I, [HYP | HYPS_O], GOAL_O) :- 
  pluck(HYPS_I, HYP_I, REST), 
  (
    apply_a(PREM, true, GOAL_I, HYP_T, GOAL_T) ;
    apply_a(PREM, false, GOAL_I, HYP_T, GOAL_T) 
  ), 
  (
    apply_b(HYP_T, GOAL_T, HYP_A, HYP_B, GOAL_A, GOAL_B) ;
    apply_b(HYP_T, GOAL_T, HYP_B, HYP_A, GOAL_B, GOAL_A) 
  ), 
  mate(HYP_A, HYP_I, GOAL_A), 
  rp([d, n], [HYP_B], GOAL_B, [HYP], GOAL),
  spl_exp(PREMS, REST, GOAL, HYPS_O, GOAL_O).

eqf(HYPS, EQN, ([HYP], GOAL)) :- 
  member(CMP, HYPS), 
  subst_rel_add([EQN], CMP, HYP, GOAL).

rwa(AYP, TRP) :- 
  TRP = (PREM, _, GOAL), 
  (
    para_mate(TRP) -> true ; 
    paran(TRP, TRP_N) -> rwa(AYP, TRP_N) ; 
    paraab(TRP, TRP_L, TRP_R), 
    rwa(AYP, TRP_L), 
    rwa(AYP, TRP_R)
  ;
    mate(AYP, PREM, GOAL) 
  ).

pmt((PREM, CONC, GOAL)) :- 
  rp([a, n], [CONC], GOAL, HYPS, GOAL_T), 
  rp([b, n], [PREM], GOAL_T, HGS), 
  maplist(pick_mate(HYPS), HGS).

speq(TRP) :- 
  para_cd(TRP, TEMP) -> speq(TEMP) ;
  a_para(TRP, TEMP),
  para_mate(TEMP). 

scj(H2G) :- 
  pmt(H2G) -> true ;
  paran(H2G, H2G_N) -> scj(H2G_N) ;
  a_para(H2G, H2G_N),
  scj(H2G_N).

/*

esimp_fork_not(TRP, TRP_A, TRP_B) :- 
  TRP = ((_, ~ FORM), _, _),
  bool_simp(FORM, NORM),
  para_s_(~ NORM, TRP, TRP_A, TRP_B).

esimp_not(X) :- 
  para_falsehood(X) -> true ;
  para_mate(X) -> true ;
  paran(X, Y), 
  esimp_not(Y).
  
esimp_bct(X) :- para_falsehood(X).
esimp_bct(X) :- 
  para_b_(X, Y, Z), 
  para_mlc(Y),
  para_mlc(Z).
esimp_bct(X) :- 
  paraab(X, Y, Z), 
  para_mate(Y),
  para_mate(Z).

esimp_bct((PREM, CONC, GOAL)) :- 
  apply_aa(PREM, GOAL, HYP_L, HYP_R, GOAL_T), 
  (
    use_falsehood(HYP_L, GOAL_T) ; 
    use_falsehood(HYP_R, GOAL_T) ; 
    mate(HYP_L, CONC, GOAL_T) ;
    mate(HYP_R, CONC, GOAL_T) ;
    mate(HYP_L, HYP_R, GOAL_T) ;
    (
      (HYP = HYP_L ; HYP = HYP_R),
      TRP = (HYP, CONC, GOAL_T),
      (para_b_(TRP, TRP_A, TRP_B) ; para_b_(TRP, TRP_B, TRP_A)), 
      para_falsehood(TRP_A),
      (para__n(TRP_B, TRP_C) ; true),
      para_mate(TRP_C)
    )
  ).

esimp_bct((PREM, _, GOAL)) :- 
  apply_b(PREM, GOAL, PREM_L, PREM_R, GOAL_L, GOAL_R), 
  apply_aa(PREM_L, GOAL_L, PREM_LL, PREM_LR, GOAL_LT), 
  mate(PREM_LL, PREM_LR, GOAL_LT),
  apply_aa(PREM_R, GOAL_R, PREM_RL, PREM_RR, GOAL_RT), 
  mate(PREM_RL, PREM_RR, GOAL_RT).

esimp_fork_bct((HYP_A, HYP_B, GOAL), (HYP_A, HYP_L, GOAL_L), (HYP_R, HYP_B, GOAL_R)) :- 
  hyp_sign_form(HYP_A, SIGN, FORM), 
  break_bct(FORM, BCT, FORM_A, FORM_B), 
  bool_simp(FORM_A, NORM_A),
  bool_simp(FORM_B, NORM_B),
  apply_bct(BCT, NORM_A, NORM_B, NORM), 
  apply_uct(SIGN, NORM, SF), 
  fps(SF, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

esimp_fork_qtf((HYP_A, HYP_B, GOAL), (HYP_A, HYP_L, GOAL_L), (HYP_R, HYP_B, GOAL_R)) :- 
  hyp_sign_form(HYP_A, SIGN, FORM), 
  break_qtf(FORM, QTF, SUB_FORM), 
  bool_simp(SUB_FORM, SUB_NORM),
  apply_uct(QTF, SUB_NORM, NORM), 
  apply_uct(SIGN, NORM, SF), 
  fps(SF, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

esimp_qtf(X) :- 
  para_falsehood(X) -> true ;
  para_mate(X) -> true ;
  para_c_(X, Y) ->
  esimp_qtf(Y) ;
  para_d_(X, Y) ->
  esimp_qtf(Y).

*/

% para_simp_e(X) :- para_falsehood(X), !.
% para_simp_e(X) :- para_mate(X), !.
% para_simp_e(X) :- paran(X, Y), !, para_simp_e(Y).
% para_simp_e(TRP) :- 
%   TRP = ((_, FORM), _, _), 
%   break_a(true, FORM, FORM_A), !, 
%   break_a(false, FORM, FORM_B), 
%   bool_simp(FORM_A, NORM_A), 
%   bool_simp(FORM_B, NORM_B), 

  
% para_simp_e(X) :- 
%   para_falsehood(X) -> true ;
%   para_mate(X) -> true ;
%   esimp_fork_not(X, Y, Z) -> 
%   para_n_(Y, Y1),
%   para__n(Y1, Y2), 
%   para_simp_e(Y2), 
%   esimp_not(Z)
% ;
%   esimp_fork_bct(X, Y, Z) -> 
%   paraab(Y, Y1, Y2), 
%   para_simp_e(Y1), 
%   para_simp_e(Y2), 
%   esimp_bct(Z)
% ;
%   esimp_fork_qtf(X, Y, Z) -> 
%   paracd(Y, Y1), 
%   para_simp_e(Y1), 
%   esimp_qtf(Z).
% 
% mscj(H2G) :- 
%   para_mate(H2G) -> true ;
%   paran(H2G, H2G_N) -> mscj(H2G_N) ;
%   para__d(H2G, H2G_N) -> mscj(H2G_N) ;
%   para_c_(H2G, H2G_N) -> mscj(H2G_N) ;
%   a_para(H2G, H2G_N),
%   mscj(H2G_N).
% 
orig_aux(PREM, GOAL, CONC) :- 
  mate(PREM, CONC, GOAL) ;
  pmt_cla(PREM, CONC, GOAL) ;
  para_clausal((PREM, CONC, GOAL)).

sup_aux(HYPS, _, ([HYP], GOAL)) :- member_rev(CMP, HYPS), mate(HYP, CMP, GOAL).
sup_aux(HYPS, EQN, ([HYP], GOAL)) :- 
  member_rev(CMP, HYPS), 
  subst_rel_add([EQN], HYP, CMP, GOAL). 

/*
gs_aux(HYP, CMP, GOAL, HYP_N, GOAL_N) :- 
  (
    apply_b(CMP, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B) ;
    apply_b(CMP, GOAL, HYP_B, HYP_A, GOAL_B, GOAL_A)
  ),
  rp([n], [HYP, HYP_A], GOAL_A, [HYP_0, HYP_1], GOAL_C), 
  mate(HYP_0, HYP_1, GOAL_C),
  rp([n], [HYP_B], GOAL_B, [HYP_N], GOAL_N). 

urr_aux(SRC, AUX, TGT, GOAL) :- 
  (
    apply_b(AUX, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B) ;
    apply_b(AUX, GOAL, HYP_B, HYP_A, GOAL_B, GOAL_A)
  ),
  rp([n], [SRC], GOAL_A, [SRC_BODY], GOAL_C), 
  rp([n], [HYP_A], GOAL_C, [HYP_NA], GOAL_D), 
  mate(SRC_BODY, HYP_NA, GOAL_D),
  rp([n], [TGT], GOAL_B, [TGT_BODY], GOAL_E), 
  rp([n], [HYP_B], GOAL_E, [HYP_NB], GOAL_F), 
  mate(TGT_BODY, HYP_NB, GOAL_F).
  
urr(PREMS, CONCS, ([PREM], GOAL)) :- 
  ground(PREM), 
  (member(CMP, CONCS) ; member(CMP, PREMS)),
  ground(CMP), 
  mate(PREM, CMP, GOAL), !.

urr(PREMS, CONCS, ([PREM], GOAL)) :- 
  (member(CMP, CONCS) ; member(CMP, PREMS)),
  mate(PREM, CMP, GOAL).

urr(PREMS, CONCS, ([PREM], GOAL)) :-
member(CONC, CONCS),
member(AUX, PREMS),
  urr_aux(PREM, AUX, CONC, GOAL).
  
gs(PREMS, CONCS, ([PREM], GOAL)) :- 
  ground(PREM), 
  (member(CMP, CONCS) ; member(CMP, PREMS)),
  ground(CMP), 
  mate(PREM, CMP, GOAL), !.
gs(PREMS, CONCS, ([PREM], GOAL)) :- 
  (member(CMP, CONCS) ; member(CMP, PREMS)),
  mate(PREM, CMP, GOAL).
gs(PREMS, CONCS, ([PREM], GOAL)) :- 
  pluck(PREMS, AUX, REST), 
  gs_aux(PREM, AUX, GOAL, PREM_N, GOAL_N),
  gs(REST, CONCS, ([PREM_N], GOAL_N)).
*/

inrw(EQ, ([PREM], GOAL), CONC) :- 
  subst_rel_add([EQ], PREM, CONC, GOAL).

%%%%%%%%%%%%%%%% MAIN PROOF COMPILATION %%%%%%%%%%%%%%%%

infer(v, ig, [PREM], CONC, GOAL) :- 
  rp([d], [CONC], GOAL, [CONC_N], GOAL_A), 
  rp([c], [PREM], GOAL_A, [PREM_N], GOAL_B), 
  para_clausal((PREM_N, CONC_N, GOAL_B)).

infer(e, para_dist, [PREM], CONC, GOAL) :- 
  para_dist((PREM, CONC, GOAL)).

infer(_, para_pull, [PREM], CONC, GOAL) :-
  rp([d], [CONC], GOAL, [HYP], GOAL_T), 
  para_pull((PREM, HYP, GOAL_T)).

infer(e, para_e1, [PREM], CONC, GOAL) :- 
  para_e1((PREM, CONC, GOAL)).

infer(e, para_push, [PREM], CONC, GOAL) :-
  para_push((PREM, CONC, GOAL)). 

infer(_, rnm, [PREM | _], CONC, GOAL) :- 
  mate(PREM, CONC, GOAL).

infer(e, simp, [PREM | _], CONC, GOAL) :-
  para_simp(e, (PREM, CONC, GOAL)).

infer(PRVR, skm, [PREM | AOCS], CONC, GOAL) :- 
  PRVR = e -> 
  eskm(AOCS, (PREM, CONC, GOAL)) 
;
  rp([d], [CONC], GOAL, [CONC_N], GOAL1), 
  skm(AOCS, (PREM, CONC_N, GOAL1)).

infer(_, ngt, [PREM], CONC, GOAL) :- 
  apply_n(CONC, GOAL, TEMP, GOAL_T), 
  mate(PREM, TEMP, GOAL_T).
  
infer(_, dff, [PREM | PREMS], CONC, GOAL) :- 
  sort(PREMS, DEFS),
  dff(DEFS, PREM, CONC, GOAL).

infer(_, dfu, [PREM | PREMS], CONC, GOAL) :- 
  dfu(PREMS, PREM, CONC, GOAL).

infer(v, sat, PREMS, _, GOAL) :-
  sat(PREMS, GOAL).

infer(v, gs, PREMS, CONC, GOAL) :-
  rp([a,d,n], [CONC], GOAL, HYPS_TEMP, GOAL_TEMP), 
  append(HYPS_TEMP, PREMS, HYPS),
  pblx(q, HYPS, GOAL_TEMP).

infer(_, rwa, [PREM_A, PREM_B], CONC, GOAL) :-
  rp([d], [CONC], GOAL, [HYP_C], GOAL_C), 
  rp([c], [PREM_B], GOAL_C, [HYP_B], GOAL_B), 
  rp([c], [PREM_A], GOAL_B, [HYP_A], GOAL_A), 
  rwa(HYP_B, (HYP_A, HYP_C, GOAL_A)).

infer(v, gaoc, AOCS, GAOC, GOAL) :- 
  rp([d], [GAOC], GOAL, [IMP], GOAL0), 
  IMP = (_, ~ ((_ => _))),
  apply_aa(IMP, GOAL0, ANTE, CONS, GOAL1), 
  apply_aocs(ANTE, AOCS, GOAL1, TEMP, GOAL2), 
  para_lax((TEMP, CONS, GOAL2)).
  
infer(PRVR, res, [PYP0, PYP1], NYP, GOAL) :- 
  member(PRVR, [v, e]),
  res(PYP0, PYP1, NYP, GOAL).
  
infer(e, orig, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  orig_aux(PREM, GOAL, CONC).

infer(v, orig, [PREM], CONC, GOAL) :- 
  mate(PREM, CONC, GOAL) ;
  pmt_cla(PREM, CONC, GOAL) ;
  infer(v, para_clausal, [PREM], CONC, GOAL). 

infer(v, inrw, [PREM], CONC, GOAL) :- 
  rp([n,a,d], [CONC], GOAL, [CONC_EQ | CONCS], GOAL_A), 
  rp([n,c,b], [PREM], GOAL_A, [([PREM_EQ], GOAL_B) | HSGS]),
  mate(PREM_EQ, CONC_EQ, GOAL_B),
  maplist(inrw(CONC_EQ), HSGS, CONCS).

infer(v, ttsc, [], CONC, GOAL) :- 
  rp([a, d, n], [CONC], GOAL, HYPS, TEMP), 
  pluck(HYPS, HYP_A, [HYP_B, HYP_C]), 
  HYP_A = (_, (("=" $ [_, _]))), 
  subst_rel_add([HYP_A], HYP_B, HYP_C, TEMP).
  
infer(_, eqf, [PREM], CONC, GOAL) :- 
  rp([a, d, n], [CONC], GOAL, HYPS, GOAL_T), 
  pluck(HYPS, HYP, REST), 
  HYP = (_, (("=" $ [_, _]))), 
  rp([b, c, n], [PREM], GOAL_T, HGS), 
  maplist(eqf(REST, HYP), HGS).

infer(_, eqr, [PREM], CONC, GOAL) :- eqr(PREM, CONC, GOAL).

infer(v, updr, [PREM], CONC, GOAL) :- 
  rp([d], [CONC], GOAL, [CONC_N], GOAL0),
  rp([c], [PREM], GOAL0, [PREM_N], GOAL1),
  (
    apply_a(PREM_N, true, GOAL1, PREM_D, GOAL2) ;
    apply_a(PREM_N, false, GOAL1, PREM_D, GOAL2)
  ),
  mate(PREM_D, CONC_N, GOAL2).

infer(e, fnnf, [PREM], CONC, GOAL) :- 
  fnnf((PREM, CONC, GOAL)).

infer(_, rwe, [PREM_L, PREM_R], CONC, GOAL) :- 
  rp([d], [CONC], GOAL, [TEMP_C], GOAL0), 
  rp([c], [PREM_L], GOAL0, [TEMP_L], GOAL1), 
  rp([d], [TEMP_L], GOAL1, [BODY_L], GOAL2), 
  rp([c], [TEMP_C], GOAL2, [BODY_C], GOAL3), 
  rp([c], [PREM_R], GOAL3, [BODY_R], GOAL4), 
  rp([a, n], [BODY_C], GOAL4, HYPS, GOAL5), 
  pick_pivot_prop(HYPS, BODY_L, GOAL5, SRC, GOAL6), 
  pick_pivot_prop(HYPS, BODY_R, GOAL6, PRE_EQN, GOAL7), 
  PRE_EQN = (_, (("=" $ [_, _]))),
  orient_hyp(PRE_EQN, GOAL7, EQN, GOAL8),
  member_rev(TGT, HYPS),
  subst_rel_add([EQN], SRC, TGT, GOAL8). 
  
infer(_, (sup,DIR), [PREM_A, PREM_B], CONC, GOAL) :- 
  orient_dir(PREM_A, PREM_B, DIR, PREM_L, PREM_R),
  rp([a, d, n], [CONC], GOAL, HYPS, GOAL0), 
  pick_pivot(HYPS, PREM_L, GOAL0, SRC, GOAL1), 
  pick_pivot(HYPS, PREM_R, GOAL1, PRE_EQN, GOAL2), 
  PRE_EQN = (_, (("=" $ [_, _]))),
  orient_hyp(PRE_EQN, GOAL2, EQN, GOAL3),
  member_rev(TGT, HYPS),
  subst_rel_add([EQN], SRC, TGT, GOAL3). 

infer(_, sup, [PREM_A, PREM_B], CONC, GOAL) :- 
  orient_dir(PREM_A, PREM_B, _, PREM_L, PREM_R),
  rp([a, d, n], [CONC], GOAL, HYPS, GOAL_A), 
  pick_pivot(HYPS, PREM_R, GOAL_A, PRE_EQN, GOAL_B), 
  PRE_EQN = (_, (("=" $ [_, _]))),
  orient_hyp(PRE_EQN, GOAL_B, EQN, GOAL_C),
  rp([b, c, n], [PREM_L], GOAL_C, HGS),
  maplist(sup_aux(HYPS, EQN), HGS).

infer(v, spl, [PREM | PREMS], CONC, GOAL) :- 
  rp([a, d, n], [CONC], GOAL, HYPS0, GOAL0), 
  spl_exp(PREMS, HYPS0, GOAL0, HYPS1, GOAL1),
  append(HYPS0, HYPS1, HYPS),
  pblx(q, [PREM | HYPS], GOAL1).

infer(_, para, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  para((PREM, CONC, GOAL)).

infer(_, sbsm, [PREM], CONC, GOAL) :- 
  sbsm(PREM, CONC, GOAL).

infer(v, cnf, [PREM], CONC, GOAL) :- 
  rp([a, d, n], [CONC], GOAL, HYPS, TEMP), 
  vcnf(PREM, HYPS, TEMP).

infer(v, acc, [PREM], CONC, GOAL) :- 
  vacc(PREM, CONC, GOAL).

infer(v, ppr, [PREM], CONC, GOAL) :-
  ppr(PREM, CONC, GOAL) ;
  ppr((PREM, CONC, GOAL)).

infer(v, paras, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  para_choice((PREM, CONC, GOAL)).

infer(v, paral, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  para_lax((PREM, CONC, GOAL)).

infer(v, para_vac, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  para_vac((PREM, CONC, GOAL)).

% infer(_, mscj, [PREM], CONC, GOAL) :- 
%   mscj((PREM, CONC, GOAL)).

infer(e, speq, [PREM], CONC, GOAL) :- 
  speq((PREM, CONC, GOAL)).

infer(_, scj, [PREM], CONC, GOAL) :- 
  rp([d], [CONC], GOAL, [HYP0], GOAL0), 
  rp([c], [PREM], GOAL0, [HYP1], GOAL1), 
  scj((HYP1, HYP0, GOAL1)).

infer(v, vnnf, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  vnnf((PREM, CONC, GOAL)).

infer(_, para_clausal, PREMS, CONC, GOAL) :- 
  rp([d, n], [CONC], GOAL, [HYP_C], GOAL_C), 
  member(PREM, PREMS),
  rp([c, n], [PREM], GOAL_C, [HYP_P], GOAL_P), 
  para_clausal((HYP_P, HYP_C, GOAL_P)).

infer(v, simp, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  para_simp(v, (PREM, CONC, GOAL)).

report_infer_failure(MODE, PRVR, HINTS, PREMS, CONC, GOAL) :- 
  write("\nInference failed, hints : "), 
  write(HINTS), 
  write("\n\n"), 
  (
    MODE = verbose ->
    write("\nInference failed, premises =\n\n"),
    writeln_list(PREMS)
  ;
    true
  ),
  write("\nInference failed, conclusion =\n\n"), 
  write(CONC), 
  write("\n\n"),
  (
    MODE = verbose ->
    open("proof_trace.pl", write, STRM), 
    write(STRM, ":- [basic].\n\n"), 
    write_term_punct(STRM, debug_prvr(PRVR)),
    write_term_punct(STRM, debug_hints(HINTS)), 
    write_term_punct(STRM, debug_ctx(PREMS)), 
    write_term_punct(STRM, debug_hyp(CONC)), 
    write_term_punct(STRM, debug_goal(GOAL)), 
    close(STRM), 
    throw(compilation_failed)
  ;
    true
  ).

timed_infer(TIME, SLVR, HINT, PREMS, CONC, GOAL) :- 
  timed_call(
    TIME,
    infer(SLVR, HINT, PREMS, CONC, GOAL), 
    (
      write("Inference failed prematurely. "),
      report_infer_failure(verbose, SLVR, HINT, PREMS, CONC, GOAL), 
      false
    ),
    (
      write("Inference timed out. "),
      report_infer_failure(fast, SLVR, HINT, PREMS, CONC, GOAL), 
      false
    )
  ).

originate(STRM, SLVR, NAME, FORM_P, CNT, FORM_C) :-
  put_char(STRM, 'S'), 
  put_form(STRM, FORM_C), 
  put_char(STRM, 'P'), 
  put_string(STRM, NAME),
  num_succ(CNT, SCNT),
  num_succ(SCNT, SSCNT),
  GOAL = (PRF, SSCNT), 
  timed_infer(30, SLVR, orig, [(SCNT, FORM_P)], (CNT, ~ FORM_C), GOAL), !,
  ground_all("" $ [], PRF),
  put_prf(STRM, PRF). 

subprove(STRM, SLVR, CNT, HINT, PREMS, FORM) :-   
  put_char(STRM, 'S'), 
  put_form(STRM, FORM), 
  num_succ(CNT, SCNT),
  GOAL = (PRF, SCNT), !,
  timed_infer(30, SLVR, HINT, PREMS, (CNT, ~ FORM), GOAL), !, 
  ground_all("" $ [], PRF),
  put_prf(STRM, PRF). 

set_tup_nth(0, (_, Y), X, (X, Y)) :- !.
set_tup_nth(NUM, (X, T0), Y, (X, T1)) :- 
  num_pred(NUM, PRED), 
  set_tup_nth(PRED, T0, Y, T1).

get_tup_nth(0, (X, _), X) :- !.
get_tup_nth(NUM, (_, TUP), ELEM) :- 
  num_pred(NUM, PRED), 
  get_tup_nth(PRED, TUP, ELEM).

get_ps_ctx(PS, CTX)    :- get_tup_nth(0, PS, CTX).
get_ps_sol(PS, SOL)    :- get_tup_nth(1, PS, SOL).
get_ps_prob(PS, PROB)  :- get_tup_nth(2, PS, PROB).
get_ps_strm(PS, STRM)  :- get_tup_nth(3, PS, STRM).
get_ps_prvr(PS, PRVR)  :- get_tup_nth(4, PS, PRVR).

set_ps_ctx(PS_O, CTX, PS_N) :- set_tup_nth(0, PS_O, CTX, PS_N).
set_ps_sol(PS_O, SOL, PS_N) :- set_tup_nth(1, PS_O, SOL, PS_N).

prove(STRM, SLVR, PROB, [orig(NAME, FORM_C) | SOL], CTX, CNT) :- 
  get_assoc(NAME, PROB, FORM_P),
  originate(STRM, SLVR, NAME, FORM_P, CNT, FORM_C),
  put_assoc(CNT, CTX, FORM_C, CTX_N),
  num_succ(CNT, SUCC), !,
  prove(STRM, SLVR, PROB, SOL, CTX_N, SUCC), !.

prove(STRM, SLVR, PROB, [add(FORM) | SOL], CTX, CNT) :- 
  justified(CNT, FORM),
  put_char(STRM, 'T'), 
  put_form(STRM, FORM), 
  put_assoc(CNT, CTX, FORM, CTX_N), 
  num_succ(CNT, SUCC), !,
  prove(STRM, SLVR, PROB, SOL, CTX_N, SUCC), !.

prove(STRM, SLVR, PROB, [inf(HINT, IDS, FORM) | SOL], CTX, CNT) :- 
  get_context(CTX, IDS, PREMS), !,
  subprove(STRM, SLVR, CNT, HINT, PREMS, FORM),
  put_assoc(CNT, CTX, FORM, CTX_N),
  num_succ(CNT, SUCC), !, 
  prove(STRM, SLVR, PROB, SOL, CTX_N, SUCC), !.

prove(STRM, _, _, [], _, CNT) :- 
  num_pred(CNT, PRED),
  put_prf(STRM, t(~ ff, x(PRED, CNT))), !.

para_push(TRP) :- 
  para_mate(TRP) -> true 
;
  paraab(TRP, TRP_L, TRP_R) -> 
  para_push(TRP_L), !,
  para_push(TRP_R)
;
  TRP = (PREM, CONC, GOAL), 
  PREM = (_, (! FORM)), 
  push_qtf(FORM, NORM),
  apply_s(! NORM, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP_L0 = (PREM, HYP_A, GOAL_A), 
  paracd(TRP_L0, TRP_L1),
  para_push(TRP_L1), 
  para_dist_fa((HYP_B, CONC, GOAL_B))
;
  TRP = (PREM, CONC, GOAL), 
  PREM = (_, (? FORM)), 
  push_qtf(FORM, NORM), 
  apply_s(? NORM, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP_L0 = (PREM, HYP_A, GOAL_A), 
  para_dc(TRP_L0, TRP_L1),
  para_push(TRP_L1), 
  para_dist_ex((HYP_B, CONC, GOAL_B)).

para_dist_ex(TRP) :- para_mate(TRP).

para_dist_ex(TRP) :- 
  para_d_(TRP, TRP_T), 
  para_mate(TRP_T).

para_dist_ex((PREM, CONC, GOAL)) :- 
  PREM = (_, (? ((FORM_A \/ FORM_B)))), !, 
  apply_s(? FORM_A \/ ? FORM_B, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para_d_(TRP, TRP_0), 
  para_ba(TRP_0, TRP_L0, TRP_R0),
  para__c(TRP_L0, TRP_L1), 
  para_mate(TRP_L1), 
  para__c(TRP_R0, TRP_R1),
  para_mate(TRP_R1), 
  para_ba((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_ex(TRP_A),
  para_dist_ex(TRP_B).

para_dist_ex((PREM, CONC, GOAL)) :- 
  PREM = (_, (? ((FORM_A /\ FORM_B)))),
  decr_vdx_form(FORM_A, _), !, 
  apply_s(FORM_A /\ ? FORM_B, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para_d_(TRP, TRP0),
  para_ab(TRP0, TRP_L, TRP_R), 
  para__c(TRP_R, TRP_R0), 
  para_mate(TRP_L), 
  para_mate(TRP_R0), 
  para_ab((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_ex(TRP_A), 
  para_dist_ex(TRP_B).
  
para_dist_ex((PREM, CONC, GOAL)) :- 
  PREM = (_, ? (FORM_A /\ FORM_B)), 
  decr_vdx_form(FORM_B, _), !, 
  apply_s(? FORM_A /\ FORM_B, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para_d_(TRP, TRP0),
  para_ab(TRP0, TRP_L, TRP_R), 
  para__c(TRP_L, TRP_L0), 
  para_mate(TRP_L0), 
  para_mate(TRP_R), 
  para_ab((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_ex(TRP_A), 
  para_dist_ex(TRP_B). 

para_dist_fa(TRP) :- para_mate(TRP).

para_dist_fa(TRP) :- 
  para_c_(TRP, TRP_T),
  para_mate(TRP_T).

para_dist_fa((PREM, CONC, GOAL)) :- 
  PREM = (_, (! ((FORM_A /\ FORM_B)))), !, 
  apply_s(! FORM_A /\ ! FORM_B, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  TRP = (PREM, HYP_A, GOAL_A), 
  para__b(TRP, TRP_L0, TRP_R0),
  para__d(TRP_L0, TRP_L1), 
  para_c_(TRP_L1, TRP_L2), 
  para_a_(true, TRP_L2, TRP_L3),
  para_mate(TRP_L3), 
  para__d(TRP_R0, TRP_R1), 
  para_c_(TRP_R1, TRP_R2), 
  para_a_(false, TRP_R2, TRP_R3), 
  para_mate(TRP_R3), 
  para_ab((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_fa(TRP_A),
  para_dist_fa(TRP_B).

para_dist_fa((PREM, CONC, GOAL)) :- 
  PREM = (_, ! (FORM_A \/ FORM_B)), 
  decr_vdx_form(FORM_A, _), !, 
  apply_s(FORM_A \/ ! FORM_B, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  apply_aa(HYP_A, GOAL_A, HYP_L, HYP_R, GOAL_0), 
  apply_d(HYP_R, GOAL_0, HYP_NR, GOAL_1), 
  apply_c(PREM, _, GOAL_1, PREM_N, GOAL_2), 
  apply_b(PREM_N, GOAL_2, PREM_L, PREM_R, GOAL_3, GOAL_4), 
  mate(PREM_L, HYP_L, GOAL_3), 
  mate(PREM_R, HYP_NR, GOAL_4), 
  para_ba((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_fa(TRP_A),
  para_dist_fa(TRP_B).

para_dist_fa((PREM, CONC, GOAL)) :- 
  PREM = (_, ! (FORM_A \/ FORM_B)), 
  decr_vdx_form(FORM_B, _), !, 
  apply_s(! FORM_A \/ FORM_B, GOAL, HYP_A, HYP_B, GOAL_A, GOAL_B), 
  apply_aa(HYP_A, GOAL_A, HYP_L, HYP_R, GOAL_0), 
  apply_d(HYP_L, GOAL_0, HYP_NL, GOAL_1), 
  apply_c(PREM, _, GOAL_1, PREM_N, GOAL_2), 
  apply_b(PREM_N, GOAL_2, PREM_L, PREM_R, GOAL_3, GOAL_4), 
  mate(PREM_L, HYP_NL, GOAL_3), 
  mate(PREM_R, HYP_R, GOAL_4), 
  para_ba((HYP_B, CONC, GOAL_B), TRP_A, TRP_B), 
  para_dist_fa(TRP_A),
  para_dist_fa(TRP_B).

para_pull(H2G) :- 
  para_mate(H2G) -> true ;
  paran(H2G, H2G_N) -> para_pull(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R) -> 
  para_pull(H2G_L), !, para_pull(H2G_R) ;
  para_c_(H2G, H2G_N),
  para_pull(H2G_N).

para_dist_aux(ANTE, CONS, GOAL_I, HYP_O, GOAL_O) :- 
  apply_s((ANTE => CONS), GOAL_I, HYP_T, HYP_O, GOAL_T, GOAL_O), 
  apply_aa(HYP_T, GOAL_T, PREM, CONC, GOAL_N),
  para_dist((PREM, CONC, GOAL_N)), !. 

para_dist_help(A_OR_B, A_TO_P, B_TO_Q, GOAL, P, Q, GOAL_P, GOAL_Q) :- 
  apply_b(A_OR_B, GOAL, A, B, GOAL_A, GOAL_B),
  apply_b(A_TO_P, GOAL_A, NA, P, GOAL_ANA, GOAL_P),
  mate(A, NA, GOAL_ANA), 
  apply_b(B_TO_Q, GOAL_B, NB, Q, GOAL_BNB, GOAL_Q),
  mate(B, NB, GOAL_BNB). 

para_dist_close(DIR, HYP_P, HYP_Q, CONC, GOAL) :- 
  apply_b(CONC, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R),
  apply_a(HYP_L, DIR, GOAL_L, HYP_NP, GOAL_NP), 
  mate(HYP_P, HYP_NP, GOAL_NP),
  apply_a(HYP_R, DIR, GOAL_R, HYP_NQ, GOAL_NQ), 
  mate(HYP_Q, HYP_NQ, GOAL_NQ).

para_dist(TRP) :- para_mate(TRP), !.
para_dist(TRP) :- para_cd(TRP, NEW), !, para_dist(NEW).
para_dist(TRP) :- 
  TRP = ((_, (_ /\ _)), _, _), !,
  para_ab(TRP, TRP_A, TRP_B),
  para_dist(TRP_A),
  para_dist(TRP_B), !.
para_dist((PREM, CONC, GOAL)) :- 
  PREM = (_, (FORM_A \/ FORM_B)), !,
  distribute(FORM_A, TEMP_A),  
  distribute(FORM_B, TEMP_B),
  para_dist_aux(FORM_A, TEMP_A, GOAL, HYP_A, GOAL_A), 
  para_dist_aux(FORM_B, TEMP_B, GOAL_A, HYP_B, GOAL_B), 
  (
    TEMP_A = (FORM_L /\ FORM_R) -> 
    apply_s(((FORM_L \/ TEMP_B) /\  (FORM_R \/ TEMP_B)), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 

    % [FORM_A, FORM_B, FORM_L, FORM_R, TEMP_B] = PAS, 
    % ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 

    para_dist_help(PREM, HYP_A, HYP_B, GOAL_T, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    apply_aa(HYP_TA, GOAL_TA, HYP_FL, HYP_FR, GOAL_FLR), 
    para_dist_close(true, HYP_FL, HYP_FR, HYP_T, GOAL_FLR), 
    para_dist_close(false, HYP_TB, HYP_TB, HYP_T, GOAL_TB), 
    para_dist((HYP_C, CONC, GOAL_C)), !

    % PREM : FA | FB, 
    % HYP_A : FA => (FL & FR), 
    % HYP_B : FB => TB, 
    % |- HYP_T : (FL | TB) & (FR | TB)
    
  ;
    TEMP_B = (FORM_L /\ FORM_R) -> 
    apply_s(((FORM_L \/ TEMP_A) /\  (FORM_R \/ TEMP_A)), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 

    % [FORM_A, FORM_B, TEMP_A, FORM_L, FORM_R] = PAS,
    % ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 

    para_dist_help(PREM, HYP_A, HYP_B, GOAL_T, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    apply_aa(HYP_TB, GOAL_TB, HYP_FL, HYP_FR, GOAL_FLR), 
    para_dist_close(true, HYP_FL, HYP_FR, HYP_T, GOAL_FLR), 
    para_dist_close(false, HYP_TA, HYP_TA, HYP_T, GOAL_TA), 
    para_dist((HYP_C, CONC, GOAL_C)), !

    % PREM : FA | FB, 
    % HYP_A : FA => TA, 
    % HYP_B : FB => (FL & FR), 
    % |- HYP_T : (FL | TA) & (FR | TA)
    
  ;
    para_dist_help(PREM, HYP_A, HYP_B, GOAL_B, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    apply_a(CONC, true, GOAL_TA, HYP_NTA, GOAL_NTA), 
    mate(HYP_TA, HYP_NTA, GOAL_NTA), 
    apply_a(CONC, false, GOAL_TB, HYP_NTB, GOAL_NTB), 
    mate(HYP_TB, HYP_NTB, GOAL_NTB)
  ).  

/*

para_dist(PREM, CONC, GOAL) :- 
  mate(PREM, CONC, GOAL) -> true  
;
  apply_cd(PREM, CONC, GOAL, PREM_N, CONC_N, GOAL_N) ->
  para_dist(PREM_N, CONC_N, GOAL_N), !
;
  hyp_sf(PREM, ((_ /\ _))) -> 
  abpl(PREM, CONC, GOAL, PREM_L, CONC_L, GOAL_L, PREM_R, CONC_R, GOAL_R), 
  para_dist(PREM_L, CONC_L, GOAL_L),
  para_dist(PREM_R, CONC_R, GOAL_R), ! 
; 
  hyp_sf(PREM, ((FORM_A \/ FORM_B))),
  distribute(FORM_A, TEMP_A),  
  distribute(FORM_B, TEMP_B),
  para_dist_aux(FORM_A, TEMP_A, GOAL, HYP_A, GOAL_A), 
  para_dist_aux(FORM_B, TEMP_B, GOAL_A, HYP_B, GOAL_B), 
  (
    TEMP_A = (FORM_L /\ FORM_R) -> 
    apply_s(((FORM_L \/ TEMP_B) /\  (FORM_R \/ TEMP_B)), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 

    % [FORM_A, FORM_B, FORM_L, FORM_R, TEMP_B] = PAS, 
    % ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 

    para_dist_help(PREM, HYP_A, HYP_B, GOAL_T, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    apply_aa(HYP_TA, GOAL_TA, HYP_FL, HYP_FR, GOAL_FLR), 
    para_dist_close(true, HYP_FL, HYP_FR, HYP_T, GOAL_FLR), 
    para_dist_close(false, HYP_TB, HYP_TB, HYP_T, GOAL_TB), 
    para_dist(HYP_C, CONC, GOAL_C), !

    % PREM : FA | FB, 
    % HYP_A : FA => (FL & FR), 
    % HYP_B : FB => TB, 
    % |- HYP_T : (FL | TB) & (FR | TB)
    
  ;
    TEMP_B = (FORM_L /\ FORM_R) -> 
    apply_s(((FORM_L \/ TEMP_A) /\  (FORM_R \/ TEMP_A)), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 

    % [FORM_A, FORM_B, TEMP_A, FORM_L, FORM_R] = PAS,
    % ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 

    para_dist_help(PREM, HYP_A, HYP_B, GOAL_T, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    apply_aa(HYP_TB, GOAL_TB, HYP_FL, HYP_FR, GOAL_FLR), 
    para_dist_close(true, HYP_FL, HYP_FR, HYP_T, GOAL_FLR), 
    para_dist_close(false, HYP_TA, HYP_TA, HYP_T, GOAL_TA), 
    para_dist(HYP_C, CONC, GOAL_C), !

    % PREM : FA | FB, 
    % HYP_A : FA => TA, 
    % HYP_B : FB => (FL & FR), 
    % |- HYP_T : (FL | TA) & (FR | TA)
    
  ;
    para_dist_help(PREM, HYP_A, HYP_B, GOAL_B, HYP_TA, HYP_TB, GOAL_TA, GOAL_TB),
    apply_a(CONC, true, GOAL_TA, HYP_NTA, GOAL_NTA), 
    mate(HYP_TA, HYP_NTA, GOAL_NTA), 
    apply_a(CONC, false, GOAL_TB, HYP_NTB, GOAL_NTB), 
    mate(HYP_TB, HYP_NTB, GOAL_NTB)
  ).  
*/ 