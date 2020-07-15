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

rul_hint(negated_conjecture, parac).  
rul_hint(flattening, parac).  
rul_hint(ennf_transformation, paras).  
rul_hint(rectify, parav).
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

rul_hint(RUL, _) :- 
  format('Rule not found : ~w', RUL), 
  throw(no_tactic_for_rule). 

pred_def_norm_or($or(FORM, $not(ATOM)), FORM, ATOM) :- unsigned_atom(ATOM).
pred_def_norm_or($or(FORM_A, FORM_B), $or(FORM_A, FORM_C), ATOM) :- 
  pred_def_norm_or(FORM_B, FORM_C, ATOM).

pred_def_norm(PRD, $fa(FORM), ARI, $fa(NORM)) :- 
  pred_def_norm(PRD, FORM, ARI, NORM).
% pred_def_norm($or(FORM, $not(ATOM)), $iff(ATOM, FORM)).
pred_def_norm(PRD, $or(FORM_A, FORM_B), ARI, $iff(ATOM, FORM)) :- 
  pred_def_norm_or($or(FORM_A, FORM_B), FORM, ATOM), 
  ATOM =.. [PRD | TERMS],
  length(TERMS, ARI).

pred_def_norm(PRD, $iff(ATOM, FORM), ARI, $iff(ATOM, FORM)) :- 
  ATOM =.. [PRD | TERMS],
  length(TERMS, ARI).

v_tup_inst(
  (ID, conjecture, FORM, _),
  inf(orig, $orig, ID, $not(FORM) )
). 
  
v_tup_inst(
 (ID, axiom, FORM, _),
 inf(orig, $orig, ID, FORM) 
).

v_tup_inst(
  (ID, plain, $iff(PRD, FORM), introduced(avatar_definition,[new_symbols(naming,[PRD])])), 
  add([def, PRD, 0], ID, $iff(PRD, FORM))
) :- 
  PRD \= $not(_).

v_tup_inst(
  (NAME, plain, FORM, introduced(predicate_definition_introduction,[new_symbols(naming, [PRD])])),
  add([def, PRD, ARI], NAME, NORM)
) :- 
  pred_def_norm(PRD, FORM, ARI, NORM).

v_tup_inst(
  (ID, _, FORM, introduced(RUL, _)),
  add([HINT], ID, FORM)
) :- 
  RUL \= predicate_definition_introduction,
  RUL \= avatar_definition,
  rul_hint(RUL, HINT).
  
v_tup_inst(
  (ID, _, FORM, inference(RUL, _, IDS)),
  inf(HINT, IDS, ID, FORM)
) :-
  rul_hint(RUL, HINT).

v_tup_inst(X, _) :-
  write("Cannot process : "),
  write(X), nl, nl,
  throw(solution_failure).

v_cmp_sclas(ORD, (ID_A, _, _, _), (ID_B, _, _, _)) :- 
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
    (
      IDS == $orig -> 
      SEEN = SEEN_T,
      INSTS_O = [INST | INSTS_T]
    ; 
      sort(IDS, IDS_S), 
      update_seen(SEEN_T, IDS_S, SEEN, DELS), 
      append([INST | DELS], INSTS_T, INSTS_O)
    )
  ).

reduce_gaocs([], []).

reduce_gaocs([INST | SOL], [INST | SOL_N]) :- 
  INST \= add([gaoc], _, _), 
  reduce_gaocs(SOL, SOL_N).
  
reduce_gaocs([add([gaoc], NAME, FORM) | SOL], SOL_N) :- 
  get_adds(FORM, NAMES, ADDS), 
  maplist(mk(del), NAMES, DELS), !,
  reduce_gaocs(SOL, SOL_T), !,
  append([ADDS, [inf(gaoc, NAMES, NAME, FORM) | DELS], SOL_T], SOL_N). 

get_adds(FORM, NAMES, ADDS) :- 
  format("ADD for : ~w\n\n", FORM),
  strip_fas(FORM, ARI, $imp(ANTE, CONC)), 
  mk_vars(asc, ARI, VARS), !, 
  explicate_form(ANTE, ANTE_N),
  explicate_form(CONC, CONC_N),
  get_adds(ARI, VARS, 0, ANTE_N, CONC_N, NAMES, ADDS),
  true.

get_adds(ARI, VARS, NUM, $ex(ANTE), CONS, [aoc(NUM) | NAMES], [skm(FUN, ARI, aoc(NUM), AOC) | ADDS]) :- !, 
  num_succ(NUM, SUCC),
  SKM = ^(FUN, VARS), 
  safe_subst_form(SKM, ANTE, ANTE_N), 
  add_fas(ARI, $imp($ex(ANTE), ANTE_N), TEMP), 
  get_adds(ARI, VARS, SUCC, ANTE_N, CONS, NAMES, ADDS), 
  implicate_form(TEMP, AOC).
  
get_adds(ARI, _, _, ANTE, CONS, [], []) :- 
  add_fas(ARI, ANTE, ANTE_N), 
  add_fas(ARI, CONS, CONS_N), 
  paral((('@0', $pos(ANTE_N)), ('@1', $neg(CONS_N)), (_, 2))).

% axiomatic(TYPE) :- member(TYPE, [lemma, axiom, hypothesis, conjecture, negated_conjecture]).

% pull_ovs(_, [], FORM, FORM).
% pull_ovs(CNT, [NUM | NUMS], FORM, NORM) :- 
%   safe_subst_form(NUM, #(CNT), FORM, TEMP), 
%   num_succ(CNT, SUCC),
%   pull_ovs(SUCC, NUMS, TEMP, NORM).
% 
% pull_ovs(FORM, NORM) :- 
%   ovs(FORM, OVS), 
%   reverse(OVS, REV),
%   pull_ovs(0, REV, FORM, NORM).
% 
% report_sol_failure(CTX, ANT) :- 
%   write("\nSolution failed, annotation : "), 
%   write(ANT), nl, nl,
%   % write("\nInference failed, premises :\n\n"),
%   % write_list(PREMS), 
%   % format("\nInference failed, conclusion : ~w\n\n", CONC), 
%   open("debug_trace.pl", write, Stream), 
%   write(Stream, ":- [main].\n\n"), 
%   format(Stream, '~w.\n\n', debug_ctx(CTX)), 
%   format(Stream, '~w.\n\n', debug_ant(ANT)), 
%   close(Stream).

relabel(SOL_I, SOL_O) :- 
  empty_assoc(EMP),  
  relabel_sol((EMP, EMP), EMP, 0, SOL_I, SOL_O).

try_del_assoc(KEY, ASC_I, ASC_O) :- 
  del_assoc(KEY, ASC_I, _, ASC_O) ->
  true   
;
  ASC_O = ASC_I.

relabel_inst(DICT, NI, CNT, del(NAME), DICT, NI_N, CNT, del(ID)) :-    
  redirect_id(NI, NAME, ID), 
  try_del_assoc(NAME, NI, NI_N).

relabel_inst(DICT, NI, CNT, add(NAME, FORM), DICT, NI_N, CNT_N, add(NORM)) :-    
  resymb_form(DICT, FORM, NORM),
  num_succ(CNT, CNT_N),
  put_assoc(NAME, NI, CNT, NI_N).

relabel_inst((RDICT, FDICT), NI, CNT, add([def, REL, ARI], NAME, FORM), (RDICT_N, FDICT), NI_N, SSCNT, add(NORM)) :-    
  num_succ(CNT, SCNT),
  num_succ(SCNT, SSCNT),
  put_assoc(NAME, NI, CNT, NI_N), 
  put_assoc((REL, ARI), RDICT, SCNT, RDICT_N),
  resymb_form((RDICT_N, FDICT), FORM, NORM).

relabel_inst((RDICT, FDICT), NI, CNT, skm(FUN, ARI, NAME, FORM), (RDICT, FDICT_N), NI_N, SSCNT, add(NORM)) :-    
  num_succ(CNT, SCNT),
  num_succ(SCNT, SSCNT),
  put_assoc(NAME, NI, CNT, NI_N), 
  put_assoc((FUN, ARI), FDICT, SCNT, FDICT_N),
  resymb_form((RDICT, FDICT_N), FORM, NORM).

relabel_inst(DICT, NI, CNT, inf(HINT, NAMES, NAME, FORM), DICT, NI_N, CNT_N, inf(HINT, IDS, NORM)) :-    
  num_succ(CNT, CNT_N),
  (
    NAMES = $orig -> 
    IDS = $orig 
  ;
    maplist_cut(redirect_id(NI), NAMES, IDS)
  ),
  put_assoc(NAME, NI, CNT, NI_N),
  resymb_form(DICT, FORM, NORM).

relabel_sol(DICT, NI, CNT, [INST | SOL], [INST_N | SOL_N]) :- 
  relabel_inst(DICT, NI, CNT, INST, DICT_N, NI_N, CNT_N, INST_N),   
  relabel_sol(DICT_N, NI_N, CNT_N, SOL, SOL_N). 

relabel_sol(_, _, _, [], []).

solve(v, TSTP, SOL) :- 
  tstp_sclas(TSTP, UNSORTED), !, 
  predsort(v_cmp_sclas, UNSORTED, SORTED), !,
  maplist_cut(v_tup_inst, SORTED, INSTS), !,
  insert_dels(INSTS, _, DELETED), !,
  reduce_gaocs(DELETED, REDUCED),
  relabel(REDUCED, SOL),
  true.