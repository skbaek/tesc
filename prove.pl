:- [basic].

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
  bf__s(TRP, TRP_N) ->
  mate(TRP_N) ; 
  mate(TRP).

vacc_aux((PREM, CONC, GOAL)) :- 
  pmt_cla(PREM, CONC, GOAL).

vacc(PREM, CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [CONC_N], GOAL1), 
  many_nb([c], [PREM], GOAL1, [PREM_T], GOAL2), 
  member(DIR, [l,r]),
  ap(PREM_T, DIR, GOAL2, PREM_N, GOAL3), 
  paras_ab((PREM_N, CONC_N, GOAL3), TRP_A, TRP_B), 
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

eqr_aux(_, ([HYP], GOAL)) :- 
  use_lc(HYP, GOAL).

eqr_aux(_, ([HYP], GOAL)) :- 
  HYP = (_, $neg(_ = _)),
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

lit_sl($not(ATOM), $neg(ATOM)) :- !.
lit_sl(ATOM, $pos(ATOM)).

form_sls($or(LIT, FORM), [SL | SLS]) :- !,
  lit_sl(LIT, SL),
  form_sls(FORM, SLS). 
  
form_sls(LIT, [SL]) :- lit_sl(LIT, SL).

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
  shell("cadical -q temp.cnf temp.drat", _), !,
  shell("drat-trim temp.cnf temp.drat -L temp.lrat", _), !,

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
  body_lits(BODY, LITS), !, 
  try(subsume_cla(LITS), CLAS, ID).

map_signed_atoms(_, []).

map_signed_atoms(HYPS, [([HYP], GOAL) | HGS]) :- 
  use_lc(HYP, GOAL) ->
  map_signed_atoms(HYPS, HGS) ;
  ground(HYP) -> 
  (pick_mate(HYPS, ([HYP], GOAL)), !, map_signed_atoms(HYPS, HGS)) ;
  (pick_mate(HYPS, ([HYP], GOAL)),  map_signed_atoms(HYPS, HGS)). 
  


%%%%%%%%%%%%%%%% MAIN PROOF COMPILATION %%%%%%%%%%%%%%%%

infer(_, rnm, [PREM | _], _, CONC, GOAL) :- 
  mate(PREM, CONC, GOAL).

infer(PRVR, skm, [PREM | AOCS], _, CONC, GOAL) :- 
  PRVR = e -> 
  eskm(AOCS, (PREM, CONC, GOAL)) 
;
  skm(AOCS, (PREM, CONC, GOAL)).

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
  find_subsumer(CNT, CLAS, CONC, NAME),
  member((o(NAME), HYP), PREMS), 
  pmt_cla((o(NAME), HYP), CONC, GOAL), !.

infer(m, simplify, [PREM_A, PREM_B], _, CONC, GOAL) :- 
  res(PREM_A, PREM_B, CONC, GOAL).
  
infer(_, orig, PREMS, CLAS, CONC, GOAL) :- 
  infer(_, id, PREMS, CLAS, CONC, GOAL) ;
  infer(_, opmt, PREMS, CLAS, CONC, GOAL) ;
  infer(_, parac, PREMS, CLAS, CONC, GOAL). 

infer(_, eqf, [PREM], _, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  pluck(HYPS, HYP, REST), 
  HYP = (_, $pos(_ = _)), 
  many([b, c, s], ([PREM], GOAL_T), HGS), 
  maplist(eqf(REST, HYP), HGS).

infer(_, cperm, [PREM], _, CONC, GOAL) :- 
  eqr(PREM, CONC, GOAL).

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

infer(v, sbsm, [PREM], _, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, TEMP), 
  (
    (member(HYP, HYPS), use_lc(HYP, TEMP)) -> 
    true
  ;
    many([b, c, s], ([PREM], TEMP), HGS), 
    map_signed_atoms(HYPS, HGS)
  ).


  %  maplist(pick_mate(HYPS), HGS). 

infer(v, cnf, [PREM], _, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, TEMP), 
  vcnf(PREM, HYPS, TEMP).

infer(v, acc, [PREM], _, CONC, GOAL) :- 
  vacc(PREM, CONC, GOAL).

infer(v, parad, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  parad((PREM, CONC, GOAL)).

infer(v, paras, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  paras((PREM, CONC, GOAL)).

infer(v, paral, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  paral((PREM, CONC, GOAL)).

infer(v, parav, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  parav((PREM, CONC, GOAL)).

infer(_, mscj, [PREM], _, CONC, GOAL) :- 
  mscj((PREM, CONC, GOAL)).

infer(_, scj, [PREM], _, CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [HYP0], GOAL0), 
  many_nb([c], [PREM], GOAL0, [HYP1], GOAL1), 
  scj((HYP1, HYP0, GOAL1)).

infer(v, vnnf, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  vnnf((PREM, CONC, GOAL)).

infer(_, parac, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  parac((PREM, CONC, GOAL)).

infer(_, paratf, PREMS, _, CONC, GOAL) :- 
  member(PREM, PREMS),
  paratf((PREM, CONC, GOAL)).

report_failure(PRVR, HINTS, PREMS, CLAS, CONC, PROB, PRF, GOAL) :- 
  write("\nInference failed, hints : "), 
  write(HINTS), nl, nl,
  write("\nInference failed, premises :\n\n"),
  write_list(PREMS), 
  format("\nInference failed, conclusion : ~w\n\n", CONC), 
  open("debug_trace.pl", write, Stream), 
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
  throw(compilation_timeout),
  false.

subprove(STRM, OCLAS, CNT, HINT, PREMS, FORM) :-   
  % format("Adding lemma ~w\n\n", CID),
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  num_succ(CNT, SCNT),
  GOAL = (PRF, SCNT), 
  timed_call(
    100,
    infer(PRVR, HINT, PREMS, OCLAS, (n(CNT), $neg(FORM)), GOAL), 
    (report_failure(PRVR, HINT, PREMS, OCLAS, (n(CNT), $neg(FORM)), none, none, GOAL), false)
  ), !,
  ground_all(c, PRF),
  % put_assoc(CID, PROB_I, - FORM, SUB_PROB),
  % (
  %   check(SUB_PROB, 0, PRF) ->  true ; 
  %   format("ID at error = ~w\n\n", CID),
  %   format("Prob at error = ~w\n\n", SUB_PROB),
  %   report_failure(PRVR, HINTS, CTX, (CID, $neg(FORM)), SUB_PROB, PRF, GOAL)
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

% PS = (PROB, SOL, LAST, CNT, STRM, PRVR, OHYPS, OCLAS, nil)
get_ps_prob(PS, PROB)  :- get_tup_nth(0, PS, PROB).
get_ps_sol(PS, SOL)    :- get_tup_nth(1, PS, SOL).
get_ps_last(PS, LAST)  :- get_tup_nth(2, PS, LAST).
get_ps_cnt(PS, CNT)    :- get_tup_nth(3, PS, CNT).
get_ps_strm(PS, STRM)  :- get_tup_nth(4, PS, STRM).
get_ps_ohyps(PS, HYPS) :- get_tup_nth(6, PS, HYPS).
get_ps_oclas(PS, CLAS) :- get_tup_nth(7, PS, CLAS).

set_ps_prob(PS_O, PROB, PS_N)  :- set_tup_nth(0, PS_O, PROB, PS_N).
set_ps_sol(PS_O, SOL, PS_N)    :- set_tup_nth(1, PS_O, SOL, PS_N).
set_ps_last(PS_O, LAST, PS_N)  :- set_tup_nth(2, PS_O, LAST, PS_N).
set_ps_cnt(PS_O, CNT, PS_N)    :- set_tup_nth(3, PS_O, CNT, PS_N).

use_inst(PS, add(FORM), PS_N) :- 
  get_ps_prob(PS, PROB),
  get_ps_strm(PS, STRM),
  get_ps_cnt(PS, CNT),
  num_succ(CNT, SCNT),
  justified(SCNT, $pos(FORM), CNT_N),
  put_char(STRM, 'T'), 
  put_sf(STRM, $pos(FORM)), 
  put_assoc(n(CNT), PROB, $pos(FORM), PROB_N), 
  set_ps_prob(PS, PROB_N, PS1), 
  set_ps_last(PS1, n(CNT), PS2), 
  set_ps_cnt(PS2, CNT_N, PS_N), 
  true.
  
use_inst(PS, inf(HINT, IDS, FORM), PS_N) :- 
  get_ps_strm(PS, STRM),
  get_ps_prob(PS, PROB),
  get_ps_cnt(PS, CNT),
  format("Constructing subproof with ID = ~w, hint = ~w\n\n", [CNT, HINT]),
  get_ps_oclas(PS, OCLAS),
  (
    IDS == $orig -> 
    get_ps_ohyps(PS, PREMS) ;
    get_context(PROB, IDS, PREMS)
  ),
  num_succ(CNT, SCNT),
  subprove(STRM, OCLAS, CNT, HINT, PREMS, FORM),
  put_assoc(n(CNT), PROB, $pos(FORM), PROB_N),
  set_ps_prob(PS, PROB_N, PS1), 
  set_ps_last(PS1, n(CNT), PS2), 
  set_ps_cnt(PS2, SCNT, PS_N), 
  true.

use_inst(PS, del(ID), PS_N) :- 
  % format("Deleting lemma ~w\n\n", PID),
  get_ps_strm(PS, STRM),
  get_ps_prob(PS, PROB_O),
  put_char(STRM, 'W'), 
  put_id(STRM, ID), 
  del_assoc(ID, PROB_O, _, PROB_N), !, 
  set_ps_prob(PS, PROB_N, PS_N).
  
prove(PS0) :- 
  get_ps_sol(PS0, [INST | SOL]), 
  set_ps_sol(PS0, SOL, PS1), !, 
  use_inst(PS1, INST, PS2), !, 
  prove(PS2).

prove(PS) :- 
  get_ps_sol(PS, []), 
  get_ps_strm(PS, STRM), 
  get_ps_last(PS, LAST),
  get_ps_cnt(PS, CNT),
  put_prf(STRM, t($neg($false), x(LAST, n(CNT)))).

% dummy :- 
%   prove(_),
%   random_pluck(_, _, _),
%   tt_term(_, _, _),
%   maplist_count(_, _, _, _, _, _),
%   prover_abrv(_, _),
%   inst_with_lvs(_, _),
%   names_from_e(_, _),
%   names_from_s(_, _),
%   tptp_name(_, _),
%   first_char(_, _),
%   path_cat(_, _),
%   path_cat_id(_, _, _),
%   solve(_, _, _),
%   true.