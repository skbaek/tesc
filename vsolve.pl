% :- module(vsolve, [vsolve/2]).

:- [basic].
:- [tstp].

rul_hint(superposition, (sup, l)).  
rul_hint(forward_demodulation, (sup, l)).
rul_hint(backward_demodulation, (sup, r)).
rul_hint(resolution, res).
rul_hint(subsumption_resolution, res).
rul_hint(trivial_inequality_removal, eqr).
rul_hint(equality_resolution, eqr).
rul_hint(equality_factoring, eqf).

rul_hint(cnf_transformation, cnf).
rul_hint(factoring, sbsm).
rul_hint(avatar_component_clause, acc).
rul_hint(avatar_contradiction_clause, sbsm).
rul_hint(duplicate_literal_removal, sbsm).

rul_hint(negated_conjecture, para_clausal).  
rul_hint(flattening, para_clausal).  
rul_hint(ennf_transformation, paras).  
rul_hint(rectify, parav).
rul_hint(true_and_false_elimination, paratf).
rul_hint(pure_predicate_removal, ppr).
rul_hint(nnf_transformation, vnnf).  

rul_hint(avatar_sat_refutation, sat).
rul_hint(unused_predicate_definition_removal, updr).
rul_hint(avatar_split_clause, spl).
rul_hint(definition_folding, dff).
rul_hint(definition_unfolding, dfu).
rul_hint(choice_axiom, gaoc).
rul_hint(skolemisation, skm).  

rul_hint(RUL, _) :- 
  format('Rule not found : ~w', RUL), 
  throw(no_tactic_for_rule). 

pred_def_norm_or($or(FORM, $not(ATOM)), FORM, ATOM) :- unsigned_atom(ATOM).
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
  (ID, conjecture, FORM, file(_, NAME)),
  orig(NAME, ID, $not(FORM))
). 
  
tup_inst(
 (ID, axiom, FORM, file(_, NAME)),
 orig(NAME, ID, FORM) 
).

tup_inst(
  (ID, plain, $iff($rel(PRD, []), FORM), introduced(avatar_definition,[new_symbols(naming,[PRD])])), 
  add([def, PRD, 0], ID, $iff($rel(PRD, []), FORM))
) :- 
  PRD \= $not(_).

tup_inst(
  (NAME, plain, FORM, introduced(predicate_definition_introduction,[new_symbols(naming, [PRD])])),
  add([def, PRD, ARI], NAME, NORM)
) :- 
  pred_def_norm(PRD, FORM, ARI, NORM).

tup_inst(
  (ID, _, FORM, introduced(RUL, _)),
  add([HINT], ID, FORM)
) :- 
  RUL \= predicate_definition_introduction,
  RUL \= avatar_definition,
  rul_hint(RUL, HINT).
  
tup_inst(
  (ID, _, FORM, inference(RUL, _, IDS)),
  inf(HINT, IDS, ID, FORM)
) :-
  rul_hint(RUL, HINT).

tup_inst(X, _) :-
  write("Cannot process : "),
  write(X), nl, nl,
  throw(solution_failure).

compare_tups(ORD, (ID_A, _, _, _), (ID_B, _, _, _)) :- 
  atom_concat('f', TEMP_A, ID_A),
  atom_number(TEMP_A, NUM_A),
  atom_concat('f', TEMP_B, ID_B),
  atom_number(TEMP_B, NUM_B),
  compare(ORD, NUM_A, NUM_B).


reduce_gaocs([], []).

reduce_gaocs([INST | SOL], [INST | SOL_N]) :- 
  INST \= add([gaoc], _, _), 
  reduce_gaocs(SOL, SOL_N).
  
reduce_gaocs([add([gaoc], NAME, FORM) | SOL], SOL_N) :- 
  get_adds(FORM, NAMES, ADDS), 
  % maplist(mk(del), NAMES, DELS), !,
  reduce_gaocs(SOL, SOL_T), !,
  append(ADDS, [inf(gaoc, NAMES, NAME, FORM) | SOL_T], SOL_N). 

get_adds(FORM, NAMES, ADDS) :- 
  strip_fas(FORM, ARI, $imp(ANTE, CONC)),
  mk_vars(asc, ARI, VARS), !, 
  % explicate_form(ANTE, ANTE_N),
  % explicate_form(CONC, CONC_N),
  get_adds(ARI, VARS, 0, ANTE, CONC, NAMES, ADDS),
  true.

get_adds(ARI, VARS, NUM, $ex(ANTE), CONS, [aoc(NUM) | NAMES], [skm(FUN, ARI, aoc(NUM), AOC) | ADDS]) :- !, 
  num_succ(NUM, SUCC),
  SKM = $fun(FUN, VARS), 
  substitute_form(safe, SKM, ANTE, ANTE_N), 
  add_fas(ARI, $imp($ex(ANTE), ANTE_N), AOC), 
  get_adds(ARI, VARS, SUCC, ANTE_N, CONS, NAMES, ADDS), 
  % implicate_form(TEMP, AOC),
  true.
  
get_adds(ARI, _, _, ANTE, CONS, [], []) :- 
  add_fas(ARI, ANTE, ANTE_N), 
  add_fas(ARI, CONS, CONS_N), 
  paral((($par(0), $pos(ANTE_N)), ($par(1), $neg(CONS_N)), (_, 2))).

vsolve(TSTP, SOL) :- 
  tstp_sclas(TSTP, UNSORTED), !,
  predsort(compare_tups, UNSORTED, SORTED), !,
  maplist_cut(tup_inst, SORTED, INSTS), !,
  % insert_dels(INSTS, _, DELETED), !,
  reduce_gaocs(INSTS, REDUCED),
  relabel(REDUCED, SOL),
  true.
