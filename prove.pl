:- [basic].
% :- [check].
:- [solve].

get_context(PROB, PIDS, CTX) :- 
  maplist(prob_id_hyp(PROB), PIDS, CTX).

pick_mate(HYPS_A, (HYPS_B, GOAL)) :- 
  member(HYP_A, HYPS_A), 
  member(HYP_B, HYPS_B), 
  mate(HYP_A, HYP_B, GOAL).

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

pmt_cla(PREM, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  many([b, c, s], ([PREM], GOAL_T), HGS), 
  maplist(pick_mate(HYPS), HGS).

res(PYP0, PYP1, HYPS, GOAL) :- 
  fp(_, GOAL, NPVT, PPVT, GOAL_N, GOAL_P), 
  many([b, c, s], ([PYP0], GOAL_N), HGS0), 
  many([b, c, s], ([PYP1], GOAL_P), HGS1), !, 
  pluck(HGS0, ([HYP0], GOAL0), REST0), 
  mate_pn(HYP0, NPVT, GOAL0), 
  pluck(HGS1, ([HYP1], GOAL1), REST1), 
  mate_pn(PPVT, HYP1, GOAL1), 
  maplist(pick_mate([NPVT | HYPS]), REST0), 
  maplist(pick_mate([PPVT | HYPS]), REST1). 

bf_pull(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> bf_pull(H2G_N) ;
  para_ab(H2G, H2G_L, H2G_R) -> 
  bf_pull(H2G_L), !, bf_pull(H2G_R) ;
  para_c_(H2G, H2G_N),
  bf_pull(H2G_N).

eqr_aux(_, ([HYP], GOAL)) :- 
  use_lc(HYP, GOAL).

eqr_aux(_, ([HYP], GOAL)) :- 
  HYP = (_, (- _ = _)),
  eq_refl(HYP, GOAL).

eqr_aux(HYPS, HG) :- 
  pick_mate(HYPS, HG).

eqr(PREM, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  many([b, c, s], ([PREM], GOAL_T), HGS), !,
  maplist(eqr_aux(HYPS), HGS).

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
    para_s((HYP0, HYP1, DFP), (NewHYP0, NewHYP1, NewDFP)) ;
    para_cd((HYP0, HYP1, DFP), (NewHYP0, NewHYP1, NewDFP))
  ), !,
  dff(Defs, NewHYP0, NewHYP1, NewDFP).

dff(Defs, HYP0, HYP1, GOAL) :- 
  para_ab((HYP0, HYP1, GOAL), (HYP0L, HYP1L, GOAL_L), (HYP0R, HYP1R, GOAL_R)), 
  dff(Defs, HYP0L, HYP1L, GOAL_L),
  dff(Defs, HYP0R, HYP1R, GOAL_R).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, (+ Atom)), 
  uatom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, (+ Atom <=> _)), !,
  ap(IFF, l, DFP0, IMP, DFP1), 
  bp(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Ante, DFP2), 
  dff(Defs, HYP0, Cons, DFP3).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, (- Atom)), 
  uatom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, (+ Atom <=> _)), !,
  ap(IFF, r, DFP0, IMP, DFP1), 
  bp(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Cons, DFP3), 
  dff(Defs, HYP0, Ante, DFP2).



%%%%%%%%%%%%%%%% SAT SOLVER %%%%%%%%%%%%%%%% 

lit_num(ANA, ~ ATOM, NEG) :- !,
  get_assoc(ATOM, ANA, NUM), 
  NEG is (- NUM).

lit_num(ANA, ATOM, NUM) :- !,
  get_assoc(ATOM, ANA, NUM).

cla_nums(ANA, CH, NUMS) :- 
  cla_lits(CH, LITS), 
  maplist_cut(lit_num(ANA), LITS, NUMS). 

cla_lits((_, (+ CF)), LITS) :- 
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
  NUM_O is NUM_I + 1, 
  put_assoc(ATOM, ANA_I, NUM_I, ANA_O),
  put_assoc(NUM_I, NAA_I, ATOM, NAA_O),
  TBL_O = (NUM_O, ANA_O, NAA_O).
  
mk_sat_tables(CHS, ANA, NAA) :- 
  empty_assoc(EMP), 
  foldl(cla_table, CHS, (1, EMP, EMP), (_, ANA, NAA)).
  
cla_ctx(CLA, (NUM_I, CTX_I), (NUM_O, CTX_O)) :- 
  NUM_O is NUM_I + 1, 
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
  NEG is (- NUM), 
  get_assoc(NEG, NAA, ATOM),
  LIT = (~ ATOM)
;
  get_assoc(NUM, NAA, LIT).

lits_cla([], $false).

lits_cla(Lits, Cla) :- 
  lits_cla_core(Lits, Cla).

lits_cla_core([Lit], Lit).

lits_cla_core([Lit | Lits], Lit | Cla) :- 
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
  file_strings(FILE, LINES), 
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

% line_rup(_, LINE, del(SID)) :-
%   split_string(LINE, " ", "", ["d", NUM_STR]),
%   number_string(SID, NUM_STR).
% 
% line_rup(NAA, LINE, rup(SIDS, SID, CLA)) :- 
%   string_numbers(LINE, [SID | NUMS]),
%   append(CLA_NUMS, [0 | REST], NUMS), 
%   nums_cla(NAA, CLA_NUMS, CLA),
%   append(SIDS, [0], REST).

unit_propagate(PREM, (HYPS_I, GOAL_I), ([HYP | HYPS_I], GOAL_O)) :- 
  many([b, s], ([PREM], GOAL_I), HGS), 
  pluck(HGS, ([HYP], GOAL_O), REST),
  maplist_cut(pick_mate(HYPS_I), REST).

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
  mate(HYP, CMP, GOAL_O).

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

sat(CLAS, GOAL) :-
  mk_sat_tables(CLAS, ANA, NAA),
  maplist_cut(cla_nums(ANA), CLAS, NUMSS),
  numss_dimacs(NUMSS, DIMACS),
  write_file("temp.cnf", DIMACS), !,
  shell("cadical -q temp.cnf temp.drat", _), !,
  shell("drat-trim temp.cnf temp.drat -L temp.lrat", _), !,
  file_sat_insts(NAA, "temp.lrat", SIS), 
  mk_sat_ctx(CLAS, CTX), 
  use_sat_insts(CTX, SIS, GOAL),
  delete_file("temp.cnf"),
  delete_file("temp.drat"),
  delete_file("temp.lrat").



%%%%%%%%%%%%%%%% UNDIRECTED MATRIX %%%%%%%%%%%%%%%%

replace_skm(SKMS, TERM_I, TERM_O) :- 
  var(TERM_I) -> false 
; 
  TERM_I =.. [FUN | TERMS_I], 
  (
    atom_concat(skm, _, FUN) -> 
    get_assoc(FUN, SKMS, NUM), 
    TERM_O = @(NUM)
  ;  
    maplist_cut(replace_skm(SKMS), TERMS_I, TERMS_O), 
    TERM_O =.. [FUN | TERMS_O]
  ).

matrixify(VARS, (FI, SF), (FO, a(MAT_L, MAT_R))) :-
  aab(SF, SF_L, SF_R), !,
  matrixify(VARS, (FI, SF_L), (FT, MAT_L)),
  matrixify(VARS, (FT, SF_R), (FO, MAT_R)).

matrixify(VARS, (FI, SF), (FO, b(MAT_L, MAT_R))) :- 
  bb(SF, SF_L, SF_R), !,
  matrixify(VARS, (FI, SF_L), (FT, MAT_L)),
  matrixify(VARS, (FT, SF_R), (FO, MAT_R)).

matrixify(VARS, (FI, SF), (FO, c(VAR, MAT))) :- 
  cb(VAR, SF, SF_N), !,
  matrixify([VAR | VARS], (FI, SF_N), (FO, MAT)). 

matrixify(VARS, (FI, SF), (FO, d(SKM, MAT))) :- 
  type_sf(d, SF), !,
  atom_concat(skm, FI, SKM), 
  FT is FI + 1, 
  SKM_TERM =.. [SKM | VARS],
  dt(SKM_TERM, SF, SF_N), 
  matrixify(VARS, (FT, SF_N), (FO, MAT)). 

matrixify(VARS, (FI, SF), (FO, MAT)) :- 
  sb(SF, SF_N), !,
  matrixify(VARS, (FI, SF_N), (FO, MAT)). 

matrixify(_, (FI, SA), (FI, SA)) :- 
  signed_atom(SA).

add_mat((ID, SF), (FI, [(GD, ID, SF) | CTX], [(GD, MAT) | MATS]), (FO, CTX, MATS)) :- 
  matrixify([], (FI, SF), (FO, MAT)).

matrixify_all(HYPS, CTX, MATS) :- 
  foldl(add_mat, HYPS, (0, CTX, MATS), (_, [], [])).

startable(a(MAT_L, MAT_R)) :- 
  startable(MAT_L) ;
  startable(MAT_R).

startable(b(MAT_L, MAT_R)) :- 
  startable(MAT_L),
  startable(MAT_R).

startable(c(_, MAT)) :- startable(MAT).
startable(d(_, MAT)) :- startable(MAT).
startable(+ _). 
startable(SF) :- lc(SF). 

mem_mod_symm(SF, SFS) :- 
  erient_stom(SF, SF_N), 
  member_syn(SF_N, SFS).

solve(MATS) :- 
  pluck(MATS, (GD, MAT), REST), 
  solve(start, REST, [], [], (GD, MAT), _).

solve(MODE, MATS, PATH, LEM_I, (a(GD_L, GD_R), a(MAT_L, MAT_R)), LEM_I) :- !, 
  (
    solve(MODE, [(GD_R, MAT_R) | MATS], PATH, LEM_I, (GD_L, MAT_L), _) ;
    solve(MODE, [(GD_L, MAT_L) | MATS], PATH, LEM_I, (GD_R, MAT_R), _)
  ).

solve(start, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O) :- !,
  startable(MAT_R),
  solve(start, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T),
  solve(start, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O).

solve(match, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O) :- !,
  (
    solve(match, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T),
    solve(block, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O)
  ;
    solve(match, MATS, PATH, LEM_I, (GD_R, MAT_R), LEM_T),
    solve(block, MATS, PATH, LEM_T, (GD_L, MAT_L), LEM_O)
  ).
  
solve(block, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O) :- !,
  solve(block, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T),
  solve(block, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O).

solve(MODE, MATS, PATH, LEM_I, (c(TERM, GD), c(TERM, MAT)), LEM_O) :- !,
  solve(MODE, MATS, PATH, LEM_I, (GD, MAT), LEM_O). 

solve(MODE, MATS, PATH, LEM_I, (d(SKM, GD), d(SKM, MAT)), LEM_O) :- !,
  solve(MODE, MATS, PATH, LEM_I, (GD, MAT), LEM_O). 

solve(match, _, [CMP | _], LEM, (m, SA), LEM) :- 
  connect_sfs(CMP, SA).
  
solve(start, MATS, PATH, LEM_I, (GD, SF), LEM_O) :-
  pos_atom(SF), 
  solve(block, MATS, PATH, LEM_I, (GD, SF), LEM_O).

solve(block, _, _, LEM, (c, SF), LEM) :-
  contradiction(SF).

solve(block, _, _, LEM, (m, SA), LEM) :- 
  mem_mod_symm(SA, LEM), !.

solve(block, _, PATH, LEM, (m, SA), LEM) :- 
  member(CMP, PATH),
  connect_sfs(CMP, SA).

solve(block, MATS, PATH, LEM, (m, SA), [SA | LEM]) :- 
  \+ mem_mod_symm(SA, PATH),
  pluck(MATS, (GD, MAT), REST), 
  solve(match, REST, [SA | PATH], LEM, (GD, MAT), _). 
 
complement_on_path(PATH, HYP, (ID, SA_B)) :- 
  HYP = (_, SA_A),
  complements(SA_A, SA_T),
  erient_stom(SA_T, SA_B),
  get_assoc(SA_B, PATH, ID).
 
mtrx_zero((CTX, _, _, GOAL)) :- 
  member((c, HYP), CTX), 
  use_contra(HYP, GOAL).
  
mtrx_zero((CTX, PATH, _, GOAL)) :- 
  member((m, HYP), CTX), 
  atomic_hyp(HYP),
  complement_on_path(PATH, HYP, CMP),
  mate(HYP, CMP, GOAL).

mtrx_one((CTX, PATH, SKMS, GOAL), (REST, PATH, SKMS, GOAL)) :- 
  pluck(CTX, (e, _), REST). 

mtrx_one((CTX, PATH_I, SKMS, GOAL), (REST, PATH_O, SKMS, GOAL)) :- 
  pluck(CTX, (m, HYP), REST), 
  atomic_hyp(HYP),
  HYP = (ID, SA), 
  put_assoc(SA, PATH_I, ID, PATH_O).

mtrx_one((CTX, PATH, SKMS, GOAL), ([(GD, HYP_N) | REST], PATH, SKMS, GOAL_N)) :- 
  pluck(CTX, (GD, HYP), REST), 
  sp(HYP, GOAL, HYP_N, GOAL_N).

mtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD_L, HYP_L), (GD_R, HYP_R) | REST], PATH, SKMS, GOAL_N)
) :- 
  pluck(CTX, (a(GD_L, GD_R), HYP), REST), 
  ap(HYP, l, GOAL, HYP_L, GOAL_T), 
  ap(HYP, r, GOAL_T, HYP_R, GOAL_N). 

mtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD, HYP_N) | REST], PATH, SKMS, GOAL_N) 
) :- 
  pluck(CTX, (c(TERM, GD), HYP), REST), 
  replace_skm(SKMS, TERM, TERM_N), 
  cp(HYP, TERM_N, GOAL, HYP_N, GOAL_N).

mtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD, HYP_N) | REST], PATH, SKMS_N, GOAL_N) 
) :- 
  pluck(CTX, (d(SKM, GD), HYP), REST), 
  GOAL = (_, FP, _), 
  put_assoc(SKM, SKMS, FP, SKMS_N), 
  dp(HYP, GOAL, HYP_N, GOAL_N).

mtrx_two(
  (CTX, PATH, SKMS, GOAL), 
  (GD_L, HYP_L), 
  (REST, PATH, SKMS, GOAL_L), 
  (GD_R, HYP_R), 
  (REST, PATH, SKMS, GOAL_R) 
) :- 
  pluck(CTX, (b(GD_L, GD_R), HYP), REST), 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

mtrx_fcs(
  (GD, HYP), 
  (CTX, PATH, SKMS, GOAL)
) :- 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R) -> 
  GD = b(GD_L, GD_R), 
  mtrx_fcs((GD_L, HYP_L), (CTX, PATH, SKMS, GOAL_L)), !,
  mtrx_fcs((GD_R, HYP_R), (CTX, PATH, SKMS, GOAL_R))
;
  mtrx(([(GD, HYP) | CTX], PATH, SKMS, GOAL)).

mtrx(MS) :- 
  mtrx_zero(MS) -> true ; 
  mtrx_one(MS, MS_N) -> mtrx(MS_N) ; 
  mtrx_two(MS, MH_L, MS_L, MH_R, MS_R), !,
  mtrx_fcs(MH_L, MS_L), !, 
  mtrx_fcs(MH_R, MS_R), !. 

mtrx(HYPS, GOAL) :- 
  matrixify_all(HYPS, CTX, MATS),
  solve(MATS), 
  term_variables(CTX, VARS),
  maplist_cut('='(e), VARS),
  empty_assoc(EMP), !, 
  mtrx((CTX, EMP, EMP, GOAL)).



%%%%%%%%%%%%%%%% DIRECTED MATRIX %%%%%%%%%%%%%%%%

member_dsf((DIR, SF), DSFS) :- 
  erient_stom(SF, SF_N), 
  member_syn((DIR, SF_N), DSFS).

ditrixify(DIR, VARS, (FI, SF), (FO, a(DIT_L, DIT_R))) :-
  aab(SF, SF_L, SF_R), !,
  ditrixify(DIR, VARS, (FI, SF_L), (FT, DIT_L)),
  ditrixify(DIR, VARS, (FT, SF_R), (FO, DIT_R)).

ditrixify(DIR, VARS, (FI, SF), (FO, b(DIT_L, DIT_R))) :- 
  bb(SF, SF_L, SF_R), !,
  ditrixify(DIR, VARS, (FI, SF_L), (FT, DIT_L)),
  ditrixify(DIR, VARS, (FT, SF_R), (FO, DIT_R)).

ditrixify(DIR, VARS, (FI, SF), (FO, c(VAR, DIT))) :- 
  cb(VAR, SF, SF_N), !,
  ditrixify(DIR, [VAR | VARS], (FI, SF_N), (FO, DIT)). 

ditrixify(DIR, VARS, (FI, SF), (FO, d(SKM, DIT))) :- 
  type_sf(d, SF), !,
  atom_concat(skm, FI, SKM), 
  FT is FI + 1, 
  SKM_TERM =.. [SKM | VARS],
  dt(SKM_TERM, SF, SF_N), 
  ditrixify(DIR, VARS, (FT, SF_N), (FO, DIT)). 

ditrixify(DIR, VARS, (FI, SF), (FO, DIT)) :- 
  sb(SF, SF_N), !,
  ditrixify(DIR, VARS, (FI, SF_N), (FO, DIT)). 

ditrixify(DIR, _, (FI, SA), (FI, (DIR, SA))) :- 
  signed_atom(SA).

dtrx_startable(a(MAT_L, MAT_R)) :- 
  dtrx_startable(MAT_L) ;
  dtrx_startable(MAT_R).

dtrx_startable(b(MAT_L, MAT_R)) :- 
  dtrx_startable(MAT_L),
  dtrx_startable(MAT_R).

dtrx_startable(c(_, MAT)) :- dtrx_startable(MAT).
dtrx_startable(d(_, MAT)) :- dtrx_startable(MAT).
dtrx_startable((_, (+ _))). 
dtrx_startable((_, SF)) :- lc(SF). 

dtrx_solve(DITS) :- 
  pluck(DITS, (GD, DIT), REST), 
  dtrx_solve(start, REST, [], [], (GD, DIT), _).

dtrx_solve(MODE, DITS, PATH, LEM_I, (a(GD_L, GD_R), a(DIT_L, DIT_R)), LEM_I) :- !, 
  (
    dtrx_solve(MODE, [(GD_R, DIT_R) | DITS], PATH, LEM_I, (GD_L, DIT_L), _) ;
    dtrx_solve(MODE, [(GD_L, DIT_L) | DITS], PATH, LEM_I, (GD_R, DIT_R), _)
  ).

dtrx_solve(start, DITS, PATH, LEM_I, (b(GD_L, GD_R), b(DIT_L, DIT_R)), LEM_O) :- !,
  dtrx_startable(DIT_R),
  dtrx_solve(start, DITS, PATH, LEM_I, (GD_L, DIT_L), LEM_T),
  dtrx_solve(start, DITS, PATH, LEM_T, (GD_R, DIT_R), LEM_O).

dtrx_solve(match, DITS, PATH, LEM_I, (b(GD_L, GD_R), b(DIT_L, DIT_R)), LEM_O) :- !,
  (
    dtrx_solve(match, DITS, PATH, LEM_I, (GD_L, DIT_L), LEM_T),
    dtrx_solve(block, DITS, PATH, LEM_T, (GD_R, DIT_R), LEM_O)
  ;
    dtrx_solve(match, DITS, PATH, LEM_I, (GD_R, DIT_R), LEM_T),
    dtrx_solve(block, DITS, PATH, LEM_T, (GD_L, DIT_L), LEM_O)
  ).
  
dtrx_solve(block, DITS, PATH, LEM_I, (b(GD_L, GD_R), b(DIT_L, DIT_R)), LEM_O) :- !,
  dtrx_solve(block, DITS, PATH, LEM_I, (GD_L, DIT_L), LEM_T),
  dtrx_solve(block, DITS, PATH, LEM_T, (GD_R, DIT_R), LEM_O).

dtrx_solve(MODE, DITS, PATH, LEM_I, (c(TERM, GD), c(TERM, DIT)), LEM_O) :- !,
  dtrx_solve(MODE, DITS, PATH, LEM_I, (GD, DIT), LEM_O). 

dtrx_solve(MODE, DITS, PATH, LEM_I, (d(SKM, GD), d(SKM, DIT)), LEM_O) :- !,
  dtrx_solve(MODE, DITS, PATH, LEM_I, (GD, DIT), LEM_O). 

dtrx_solve(match, _, [CMP | _], LEM, (DIR, (DIR, SA)), LEM) :- 
  connect_dsfs(CMP, (DIR, SA)).
  
dtrx_solve(start, DITS, PATH, LEM_I, (GD, (DIR, SF)), LEM_O) :-
  pos_atom(SF), 
  dtrx_solve(block, DITS, PATH, LEM_I, (GD, (DIR, SF)), LEM_O).

dtrx_solve(block, _, _, LEM, (c, (_, SF)), LEM) :-
  contradiction(SF).

dtrx_solve(block, _, _, LEM, (DIR, (DIR, SA)), LEM) :- 
  member_dsf((DIR, SA), LEM), !.

dtrx_solve(block, _, PATH, LEM, (DIR, (DIR, SA)), LEM) :- 
  member(CMP, PATH),
  connect_dsfs(CMP, (DIR, SA)).

dtrx_solve(block, DITS, PATH, LEM, (DIR, (DIR, SA)), [(DIR, SA) | LEM]) :- 
  \+ member_dsf((DIR, SA), PATH),
  pluck(DITS, (GD, DIT), REST), 
  dtrx_solve(match, REST, [(DIR, SA) | PATH], LEM, (GD, DIT), _). 
 
flip(l, r).
flip(r, l).

dtrx_zero((CTX, _, _, GOAL)) :- 
  member((c, HYP), CTX), 
  use_contra(HYP, GOAL).
  
dtrx_zero((CTX, PATH, _, GOAL)) :- 
  member((DIR, HYP), CTX), 
  flip(DIR, FLP), 
  HYP = (_, SA_A),
  complements(SA_A, SA_T),
  erient_stom(SA_T, SA_B),
  get_assoc((FLP, SA_B), PATH, ID),
  mate(HYP, (ID, SA_B), GOAL).

dtrx_one((CTX, PATH, SKMS, GOAL), (REST, PATH, SKMS, GOAL)) :- 
  pluck(CTX, (e, _), REST). 

dtrx_one((CTX, PATH_I, SKMS, GOAL), (REST, PATH_O, SKMS, GOAL)) :- 
  pluck(CTX, (DIR, HYP), REST), 
  flip(DIR, _),
  atomic_hyp(HYP),
  HYP = (ID, SA), 
  put_assoc((DIR, SA), PATH_I, ID, PATH_O).

dtrx_one((CTX, PATH, SKMS, GOAL), ([(GD, HYP_N) | REST], PATH, SKMS, GOAL_N)) :- 
  pluck(CTX, (GD, HYP), REST), 
  sp(HYP, GOAL, HYP_N, GOAL_N).

dtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD_L, HYP_L), (GD_R, HYP_R) | REST], PATH, SKMS, GOAL_N)
) :- 
  pluck(CTX, (a(GD_L, GD_R), HYP), REST), 
  ap(HYP, l, GOAL, HYP_L, GOAL_T), 
  ap(HYP, r, GOAL_T, HYP_R, GOAL_N). 

dtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD, HYP_N) | REST], PATH, SKMS, GOAL_N) 
) :- 
  pluck(CTX, (c(TERM, GD), HYP), REST), 
  replace_skm(SKMS, TERM, TERM_N), 
  cp(HYP, TERM_N, GOAL, HYP_N, GOAL_N).

dtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD, HYP_N) | REST], PATH, SKMS_N, GOAL_N) 
) :- 
  pluck(CTX, (d(SKM, GD), HYP), REST), 
  GOAL = (_, FP, _), 
  put_assoc(SKM, SKMS, FP, SKMS_N), 
  dp(HYP, GOAL, HYP_N, GOAL_N).

dtrx_two(
  (CTX, PATH, SKMS, GOAL), 
  (GD_L, HYP_L), 
  (REST, PATH, SKMS, GOAL_L), 
  (GD_R, HYP_R), 
  (REST, PATH, SKMS, GOAL_R) 
) :- 
  pluck(CTX, (b(GD_L, GD_R), HYP), REST), 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

dtrx_fcs(
  (GD, HYP), 
  (CTX, PATH, SKMS, GOAL)
) :- 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R) -> 
  GD = b(GD_L, GD_R), 
  dtrx_fcs((GD_L, HYP_L), (CTX, PATH, SKMS, GOAL_L)), !,
  dtrx_fcs((GD_R, HYP_R), (CTX, PATH, SKMS, GOAL_R))
;
  dtrx(([(GD, HYP) | CTX], PATH, SKMS, GOAL)).

dtrx(MS) :- 
  dtrx_zero(MS) -> true ; 
  dtrx_one(MS, MS_N) -> dtrx(MS_N) ; 
  dtrx_two(MS, MH_L, MS_L, MH_R, MS_R), !,
  dtrx_fcs(MH_L, MS_L), !, 
  dtrx_fcs(MH_R, MS_R), !. 
  
dtrx(HYP_L, HYP_R, GOAL) :- 
  hyp_sf(HYP_L, SF_L),
  hyp_sf(HYP_R, SF_R),
  ditrixify(l, [], (0, SF_L), (TEMP, DIT_L)),
  ditrixify(r, [], (TEMP, SF_R), (_, DIT_R)),
  dtrx_solve([(GD_L, DIT_L), (GD_R, DIT_R)]), 
  term_variables((GD_L, GD_R), VARS),
  maplist_cut('='(e), VARS),
  empty_assoc(EMP), 
  dtrx(([(GD_L, HYP_L), (GD_R, HYP_R)], EMP, EMP, GOAL)).

eskm(AOCS, H2G) :- 
  para_m(H2G) -> true 
;
  para_ab(H2G, H2G_L, H2G_R) -> 
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
  paral_cd(H2G, H2G_N), 
  skm(AOCS, H2G_N)
;
  para_ab(H2G, H2G_L, H2G_R),
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
    para_s(TRP, TRP_N) -> rwa(AYP, TRP_N) ; 
    para_ab(TRP, TRP_L, TRP_R), 
    rwa(AYP, TRP_L), 
    rwa(AYP, TRP_R)
  ;
    mate(AYP, PREM, GOAL) 
  ).

pmt((PREM, CONC, GOAL)) :- 
  many_nb([a, s], [CONC], GOAL, HYPS, GOAL_T), 
  many([b, s], ([PREM], GOAL_T), HGS), 
  maplist(pick_mate(HYPS), HGS).

scj(H2G) :- 
  pmt(H2G) -> true ;
  para_s(H2G, H2G_N) -> scj(H2G_N) ;
  a_para(H2G, H2G_N),
  scj(H2G_N).

mscj(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> mscj(H2G_N) ;
  para__d(H2G, H2G_N) -> mscj(H2G_N) ;
  para_c_(H2G, H2G_N) -> mscj(H2G_N) ;
  a_para(H2G, H2G_N),
  mscj(H2G_N).

bf_dist_aux(ANTE, CONS, GOAL_I, HYP_O, GOAL_O) :- 
  fp(ANTE => CONS, GOAL_I, HYP_T, HYP_O, GOAL_T, GOAL_O), 
  aap(HYP_T, GOAL_T, PREM, CONC, GOAL_N),
  bf_dist(PREM, CONC, GOAL_N), !. 

bf_dist(PREM, CONC, GOAL) :- 
  mate(PREM, CONC, GOAL) -> true  
;
  cdp(PREM, CONC, GOAL, PREM_N, CONC_N, GOAL_N) ->
  bf_dist(PREM_N, CONC_N, GOAL_N), !
;
  hyp_sf(PREM, + (_ & _)) -> 
  abpl(PREM, CONC, GOAL, PREM_L, CONC_L, GOAL_L, PREM_R, CONC_R, GOAL_R), 
  bf_dist(PREM_L, CONC_L, GOAL_L),
  bf_dist(PREM_R, CONC_R, GOAL_R), ! 
; 
  hyp_sf(PREM, + (FORM_A | FORM_B)),
  distribute(FORM_A, TEMP_A),  
  distribute(FORM_B, TEMP_B),
  bf_dist_aux(FORM_A, TEMP_A, GOAL, HYP_A, GOAL_A), 
  bf_dist_aux(FORM_B, TEMP_B, GOAL_A, HYP_B, GOAL_B), 
  (
    TEMP_A = (FORM_L & FORM_R) -> 
    fp((FORM_L | TEMP_B) & (FORM_R | TEMP_B), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 
    [FORM_A, FORM_B, FORM_L, FORM_R, TEMP_B] = PAS, 
    ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 
    bf_dist(HYP_C, CONC, GOAL_C), !
  ;
    TEMP_B = (FORM_L & FORM_R) -> 
    fp((FORM_L | TEMP_A) & (FORM_R | TEMP_A), GOAL_B, HYP_T, HYP_C, GOAL_T, GOAL_C), 
    [FORM_A, FORM_B, TEMP_A, FORM_L, FORM_R] = PAS,
    ablx(PAS, [PREM, HYP_A, HYP_B, HYP_T], GOAL_T), 
    bf_dist(HYP_C, CONC, GOAL_C), !
  ;
    [FORM_A, FORM_B, TEMP_A, TEMP_B] = PAS,
    ablx(PAS, [PREM, HYP_A, HYP_B, CONC], GOAL_B), !
  ).  


%%%%%%%%%%%%%%%% MAIN PROOF COMPILATION %%%%%%%%%%%%%%%%

infer(_, rnm, [PREM | _], CONC, GOAL) :- 
  mate(PREM, CONC, GOAL).

infer(PRVR, skm, [PREM | AOCS], CONC, GOAL) :- 
  PRVR = e -> 
  eskm(AOCS, (PREM, CONC, GOAL)) 
;
  skm(AOCS, (PREM, CONC, GOAL)).

infer(_, ngt, [PREM], CONC, GOAL) :- 
  sp(CONC, GOAL, TEMP, GOAL_T), 
  mate(PREM, TEMP, GOAL_T).

infer(v, aft, PREMS, CONC, GOAL) :- 
  tblx([CONC | PREMS], GOAL).

infer(v, daft, [PREM], CONC, GOAL) :- 
  tblx(PREM, CONC, GOAL).
  
infer(_, dff, [PREM | PREMS], CONC, GOAL) :- 
  sort(PREMS, DEFS),
  dff(DEFS, PREM, CONC, GOAL).

infer(_, dfu, [PREM | PREMS], CONC, GOAL) :- 
  dfu(PREMS, PREM, CONC, GOAL).

infer(v, sat, PREMS, _, GOAL) :-
  sat(PREMS, GOAL).
  
infer(v, pblx, PREMS, CONC, GOAL) :-
  pblx(p, [CONC | PREMS], GOAL).

infer(m, subst, [PREM], CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP_C], GOAL0), 
  many_nb([c], [PREM], GOAL0, [HYP_P], GOAL1), 
  ( 
    mate(HYP_P, HYP_C, GOAL1) ;
    pblx(p, [HYP_P, HYP_C], GOAL1)
  ).

infer(m, eq, [], CONC, GOAL) :-
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  pluck(HYPS, EQ, [HYP_A, HYP_B]),
  EQ = (_, (+ _ = _)), 
  subst_rel_mul(HYP_A, [EQ], HYP_B, GOAL_T, []). 

infer(m, refl, [], CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP], GOAL_T), 
  eq_refl(HYP, GOAL_T).

infer(_, bf_pull, [PREM], CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP], GOAL_T), 
  bf_pull((PREM, HYP, GOAL_T)).

infer(_, bf_push, [PREM], CONC, GOAL) :-
  bf_push((PREM, CONC, GOAL)).

infer(_, rwa, [PREM_A, PREM_B], CONC, GOAL) :-
  many_nb([d], [CONC], GOAL, [HYP_C], GOAL_C), 
  many_nb([c], [PREM_B], GOAL_C, [HYP_B], GOAL_B), 
  many_nb([c], [PREM_A], GOAL_B, [HYP_A], GOAL_A), 
  rwa(HYP_B, (HYP_A, HYP_C, GOAL_A)).

infer(v, gaoc, AOCS, GAOC, GOAL) :- 
  many_nb([d], [GAOC], GOAL, [IMP], GOAL0), 
  IMP = (_, (- (_ => _))),
  aap(IMP, GOAL0, ANTE, CONS, GOAL1), 
  apply_aocs(ANTE, AOCS, GOAL1, TEMP, GOAL2), 
  paral((TEMP, CONS, GOAL2)).
  
infer(PRVR, res, [PYP0, PYP1], NYP, GOAL) :- 
  member(PRVR, [m, v, e]),
  many_nb([a, d, s], [NYP], GOAL, HYPS, GOAL_T), 
  (
    res(PYP0, PYP1, HYPS, GOAL_T) ;
    res(PYP1, PYP0, HYPS, GOAL_T)
  ), !.

infer(_, pmt, [PREM], CONC, GOAL) :- pmt_cla(PREM, CONC, GOAL).

% infer(m, cnn, [PREM], CONC, GOAL) :- 
%   pmt_cla(PREM, CONC, GOAL) ;
%   dtrx(PREM, CONC, GOAL) ; 
%   bfm((PREM, CONC, GOAL)). 

infer(_, eqf, [PREM], CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  pluck(HYPS, HYP, REST), 
  HYP = (_, (+ _ = _)), 
  many([b, c, s], ([PREM], GOAL_T), HGS), 
  maplist(eqf(REST, HYP), HGS).

infer(_, cperm, [PREM], CONC, GOAL) :- 
  eqr(PREM, CONC, GOAL).

infer(_, eqr, [PREM], CONC, GOAL) :- 
  eqr(PREM, CONC, GOAL).

infer(v, updr, [PREM], CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [CONC_N], GOAL0),
  many_nb([c], [PREM], GOAL0, [PREM_N], GOAL1),
  (
    ap(PREM_N, l, GOAL1, PREM_D, GOAL2) ;
    ap(PREM_N, r, GOAL1, PREM_D, GOAL2)
  ),
  mate(PREM_D, CONC_N, GOAL2).

infer(e, fnnf, [PREM], CONC, GOAL) :- 
  fnnf((PREM, CONC, GOAL)).

infer(_, rwe, [PREM_L, PREM_R], CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [TEMP_C], GOAL0), 
  many_nb([c], [PREM_L], GOAL0, [TEMP_L], GOAL1), 
  many_nb([d], [TEMP_L], GOAL1, [BODY_L], GOAL2), 
  many_nb([c], [TEMP_C], GOAL2, [BODY_C], GOAL3), 
  many_nb([c], [PREM_R], GOAL3, [BODY_R], GOAL4), 
  many_nb([a, s], [BODY_C], GOAL4, HYPS, GOAL5), 
  pick_pivot_prop(HYPS, BODY_L, GOAL5, SRC, GOAL6), 
  pick_pivot_prop(HYPS, BODY_R, GOAL6, PRE_EQN, GOAL7), 
  PRE_EQN = (_, (+ _ = _)),
  erient_hyp(PRE_EQN, GOAL7, EQN, GOAL8),
  member_rev(TGT, HYPS),
  subst_rel_add([EQN], SRC, TGT, GOAL8). 
  
infer(_, (sup, DIR), [PREM_A, PREM_B], CONC, GOAL) :- 
  orient_dir(PREM_A, PREM_B, DIR, PREM_L, PREM_R),
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL0), 
  pick_pivot(HYPS, PREM_L, GOAL0, SRC, GOAL1), 
  pick_pivot(HYPS, PREM_R, GOAL1, PRE_EQN, GOAL2), 
  PRE_EQN = (_, (+ _ = _)),
  erient_hyp(PRE_EQN, GOAL2, EQN, GOAL3),
  member_rev(TGT, HYPS),
  subst_rel_add([EQN], SRC, TGT, GOAL3). 

infer(v, spl, [PREM | PREMS], CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS0, GOAL0), 
  spl_exp(PREMS, HYPS0, GOAL0, HYPS1, GOAL1),
  append(HYPS0, HYPS1, HYPS),
  pblx(q, [PREM | HYPS], GOAL1).
  
infer(e, bf_dist, [PREM], CONC, GOAL) :- 
  bf_dist(PREM, CONC, GOAL).

infer(e, simp, [PREM], CONC, GOAL) :- 
  esimp((PREM, CONC, GOAL)).

% infer(m, bf, [PREM], CONC, GOAL) :- 
%   bfe((PREM, CONC, GOAL)).

infer(e, bf, [PREM], CONC, GOAL) :- 
  bfe((PREM, CONC, GOAL)).

infer(e, bf2, [PREM], CONC, GOAL) :- 
  bfe2((PREM, CONC, GOAL)).

infer(_, para, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  para((PREM, CONC, GOAL)).

infer(v, parad, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  parad((PREM, CONC, GOAL)).

infer(v, paras, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  paras((PREM, CONC, GOAL)).

infer(v, paral, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  paral((PREM, CONC, GOAL)).

infer(_, mscj, [PREM], CONC, GOAL) :- 
  mscj((PREM, CONC, GOAL)).

infer(_, scj, [PREM], CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [HYP0], GOAL0), 
  many_nb([c], [PREM], GOAL0, [HYP1], GOAL1), 
  scj((HYP1, HYP0, GOAL1)).

infer(v, vnnf, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  vnnf((PREM, CONC, GOAL)).

infer(_, parac, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  parac((PREM, CONC, GOAL)).

infer(_, paratf, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  paratf((PREM, CONC, GOAL)).

infer(_, dtrx, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  dtrx(PREM, CONC, GOAL).

infer(v, mtrx, PREMS, CONC, GOAL) :- 
  mtrx([CONC | PREMS], GOAL).

infers(PRVR, [TAC | TACS], PREMS, CONC, GOAL) :- 
  infer(PRVR, TAC, PREMS, CONC, GOAL) -> true ;  
  infers(PRVR, TACS, PREMS, CONC, GOAL).

report_failure(PRVR, HINTS, PREMS, CONC, PROB, PRF, GOAL) :- 
  write("\nInference failed, hints : "), 
  write(HINTS), nl, nl,
  write("\nInference failed, premises :\n\n"),
  write_list(PREMS), 
  format("\nInference failed, conclusion : ~w\n\n", CONC), 
  open("debug_trace.pl", write, Stream), 
  write(Stream, ":- [main].\n\n"), 
  format(Stream, '~w.\n\n', debug_prvr(PRVR)), 
  format(Stream, '~w.\n\n', debug_hints(HINTS)), 
  format(Stream, '~w.\n\n', debug_ctx(PREMS)), 
  format(Stream, '~w.\n\n', debug_hyp(CONC)), 
  format(Stream, '~w.\n\n', debug_goal(GOAL)), 
  format(Stream, '~w.\n\n', debug_prob(PROB)), 
  format(Stream, '~w.\n\n', debug_prf(PRF)), 
  close(Stream), 
  % throw(compilation_failure),
  true.

subprove(STRM, HINTS, PIDS, CID, FORM, PROB_I, PROB_O) :-   
  % format("Adding lemma ~w\n\n", CID),
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  put_id(STRM, CID), 
  get_context(PROB_I, PIDS, CTX),
  GOAL = (PRF, 0, 0), 
  timed_call(
    60,
    infers(PRVR, HINTS, CTX, (CID, (- FORM)), GOAL), 
    (report_failure(PRVR, HINTS, CTX, (CID, (- FORM)), none, none, GOAL), false)
  ), !,
  ground_all(c, PRF),
  % put_assoc(CID, PROB_I, - FORM, SUB_PROB),
  % (
  %   check(SUB_PROB, 0, PRF) ->  true ; 
  %   format("ID at error = ~w\n\n", CID),
  %   format("Prob at error = ~w\n\n", SUB_PROB),
  %   report_failure(PRVR, HINTS, CTX, (CID, (- FORM)), SUB_PROB, PRF, GOAL)
  % ),
  put_prf(STRM, PRF), 
  put_assoc(CID, PROB_I, + FORM, PROB_O).

prove(STRM, LAST, PRVR, [del(PID) | SOL], PROB) :- 
  % format("Deleting lemma ~w\n\n", PID),
  put_char(STRM, 'W'), 
  put_id(STRM, PID), 
  del_assoc(PID, PROB, _, PROB_N),
  prove(STRM, LAST, PRVR, SOL, PROB_N). 

prove(STRM, _, PRVR, [add(JST, CID, CONC) | SOL], PROB) :- 
  % format("Adding lemma ~w\n\n", CID),
  put_char(STRM, 'T'), 
  % write("Justification : "), write(JST), nl,
  % format("Adding axiom : ~w\n", CONC),
  % format("With context : ~w\n", PROB),
  % justified(PROB, CONC, JST),
  % write("Justified.\n\n"),
  put_sf(STRM, + CONC), 
  put_atoms(STRM, JST),
  put_id(STRM, CID), 
  put_assoc(CID, PROB, + CONC, PROB_N),
  prove(STRM, CID, PRVR, SOL, PROB_N). 

prove(STRM, _, PRVR, [inf(HINTS, PIDS, CID, FORM) | SOL], PROB) :- 
  get_assoc(CID, PROB, SF) -> 
  SF = (+ FORM), 
  prove(STRM, CID, PRVR, SOL, PROB)
;
  subprove(STRM, HINTS, PIDS, CID, FORM, PROB, PROB_N),
  prove(STRM, CID, PRVR, SOL, PROB_N).

prove(STRM, LAST, _, [], _) :- 
  put_prf(STRM, t(- $false, [neg_false], x(0), x(LAST, x(0)))).

prove(PRVR, TPTP, TSTP, TXTX) :- 
  set_prolog_flag(stack_limit, 2_147_483_648),
  style_check(-singleton),
  pose(TPTP, PIDS, PROB),
  solve(PRVR, PIDS, TSTP, SOL),
  open(TXTX, write, STRM, [encoding(octet)]),
  prove(STRM, none, PRVR, SOL, PROB),
  close(STRM).
