% :- module(vsolve, [vsolve/2]).

:- [basic].

rul_hint(superposition, sup).
rul_hint(forward_demodulation, (sup,true)).
rul_hint(backward_demodulation, (sup,true)).
rul_hint(resolution, res).
rul_hint(subsumption_resolution, res).
rul_hint(extensionality_resolution, res).
rul_hint(trivial_inequality_removal, eqr).
rul_hint(equality_resolution, eqr).
rul_hint(equality_factoring, eqf).
rul_hint(cnf_transformation, cnf).
rul_hint(instance_generation, ig).
rul_hint(factoring, sbsm).
rul_hint(avatar_component_clause, acc).
rul_hint(avatar_contradiction_clause, sbsm).
rul_hint(duplicate_literal_removal, sbsm).
rul_hint(condensation, sbsm).
rul_hint(negated_conjecture, para_clausal).  
rul_hint(flattening, para_clausal).  
rul_hint(ennf_transformation, paras).  
rul_hint(rectify, para_vac).
rul_hint(true_and_false_elimination, simp).
rul_hint(unit_resulting_resolution, gs).
rul_hint(global_subsumption, gs).
rul_hint(pure_predicate_removal, ppr).
rul_hint(nnf_transformation, vnnf).  
rul_hint(avatar_sat_refutation, sat).
rul_hint(sat_instgen_refutation, sat).
rul_hint(unused_predicate_definition_removal, updr).
rul_hint(avatar_split_clause, spl).
rul_hint(inner_rewriting, inrw).
% rul_hint(inequality_splitting_name_introduction, isni).
rul_hint(definition_folding, dff).
rul_hint(definition_unfolding, dfu).
rul_hint(choice_axiom, gaoc).
rul_hint(skolemisation, skm).  

rul_hint(RUL, _) :- 
  format('Rule not found : ~w', RUL), 
  throw(no_tactic_for_rule). 

lit_arity($not($rel(_, TERMS)), ARI) :- length(TERMS, ARI).
lit_arity($rel(_, TERMS), ARI) :- length(TERMS, ARI).

pred_def_norm_or($or(FORM, $not(ATOM)), FORM, ATOM) :- atomic_form(ATOM).
pred_def_norm_or($or(FORM_A, FORM_B), $or(FORM_A, FORM_C), ATOM) :- 
  pred_def_norm_or(FORM_B, FORM_C, ATOM).

pred_def_norm(PRD, $fa(FORM), ARI, $fa(NORM)) :- 
  pred_def_norm(PRD, FORM, ARI, NORM).
pred_def_norm(PRD, $or(FORM_A, FORM_B), ARI, $iff($rel(PRD, TERMS), FORM)) :- 
  pred_def_norm_or($or(FORM_A, FORM_B), FORM, $rel(PRD, TERMS)), 
  length(TERMS, ARI).
pred_def_norm(PRD, $iff(ATOM, FORM), ARI, $iff(ATOM, FORM)) :- 
  ATOM = $rel(PRD, TERMS),
  length(TERMS, ARI).

tup_inst(
  (CNM, true, FORM, some(file(_, PNM_ATOM))),
  orig(PNM, CNM, FORM) 
) :-
  atom_string(PNM_ATOM, PNM), !.

tup_inst(
  (CNM, false, FORM, some(introduced(inequality_splitting_name_introduction,[new_symbols(naming,[PRD])]))), 
  add([isni, PRD, ARI], CNM, FORM)
) :- 
  lit_arity(FORM, ARI).

tup_inst(
  (CNM, false, $iff($rel(PRD, []), FORM), some(introduced(avatar_definition,[new_symbols(naming,[PRD])]))), 
  add([def, PRD, 0], CNM, $iff($rel(PRD, []), FORM))
) :- 
  PRD \= $not(_).

tup_inst(
  (CNM, false, FORM, some(introduced(predicate_definition_introduction,[new_symbols(naming, [PRD])]))),
  add([def, PRD, ARI], CNM, NORM)
) :- 
  pred_def_norm(PRD, FORM, ARI, NORM).

tup_inst(
  (CNM, _, FORM, some(introduced(theory_tautology_sat_conflict, []))),
  inf(ttsc, [], CNM, FORM)
) :- !.

tup_inst(
  (CNM, _, FORM, some(introduced(RUL, _))),
  add([HINT], CNM, FORM)
) :- 
  RUL \= predicate_definition_introduction,
  RUL \= avatar_definition,
  rul_hint(RUL, HINT).
  
tup_inst(
  (CNM, _, FORM, some(inference(RUL, _, PNM_ATOMS))),
  inf(HINT, PNMS, CNM, FORM)
) :-
  maplist_cut(atom_string, PNM_ATOMS, PNMS),
  rul_hint(RUL, HINT).

tup_inst(X, _) :-
  write("Cannot process annotated formula = ~w\n", X),
  throw(annotated_formula_processing_failure).

compare_tups(ORD, (ID_A, _, _, _), (ID_B, _, _, _)) :- 
  atom_concat('f', TEMP_A, ID_A),
  atom_number(TEMP_A, NUM_A),
  atom_concat('f', TEMP_B, ID_B),
  atom_number(TEMP_B, NUM_B),
  compare(ORD, NUM_A, NUM_B).
compare_tups(_, X, Y) :- 
  format("Cannot compare ~w with ~w\n", [X,Y]),
  throw(name_comparison_failure).

reduce_gaocs([], []).

reduce_gaocs([INST | SOL], [INST | SOL_N]) :- 
  INST \= add([gaoc], _, _), 
  reduce_gaocs(SOL, SOL_N).
  
reduce_gaocs([add([gaoc], NAME, FORM) | SOL], SOL_N) :- 
  get_adds(FORM, NAMES, ADDS), 
  reduce_gaocs(SOL, SOL_T), !,
  append(ADDS, [inf(gaoc, NAMES, NAME, FORM) | SOL_T], SOL_N). 

get_adds(FORM, NAMES, ADDS) :- 
  strip_fas(FORM, ARI, $imp(ANTE, CONC)),
  mk_vars(asc, ARI, VARS), !, 
  get_adds(ARI, VARS, 0, ANTE, CONC, NAMES, ADDS),
  true.

get_adds(ARI, VARS, NUM, $ex(ANTE), CONS, [aoc(NUM) | NAMES], [skm(FUN, ARI, aoc(NUM), AOC) | ADDS]) :- !, 
  num_succ(NUM, SUCC),
  SKM = $fun(FUN, VARS), 
  substitute_form(safe, SKM, ANTE, ANTE_N), 
  add_fas(ARI, $imp($ex(ANTE), ANTE_N), AOC), 
  get_adds(ARI, VARS, SUCC, ANTE_N, CONS, NAMES, ADDS).
  
get_adds(ARI, _, _, ANTE, CONS, [], []) :- 
  add_fas(ARI, ANTE, ANTE_N), 
  add_fas(ARI, CONS, CONS_N), 
  para_lax((($par(0), ANTE_N), ($par(1), $not(CONS_N)), (_, 2))).

vsolve(TSTP, SOL) :- 
  tptp_sol(TSTP, UNSORTED), !,
  predsort(compare_tups, UNSORTED, SORTED), !,
  maplist_cut(tup_inst, SORTED, INSTS), !,
  reduce_gaocs(INSTS, REDUCED),
  relabel(REDUCED, SOL).