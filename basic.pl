%%%%%%%%%%%%%%%% GENERIC %%%%%%%%%%%%%%%% 

timed_call(TIME, GOAL, ALT) :- timed_call(TIME, GOAL, ALT, ALT). 
  
timed_call(TIME, GOAL, EARLY, LATE) :- 
  catch(
    call_with_time_limit(
      TIME, 
      (call(GOAL) -> true ; throw(premature_failure))
    ),
    ERROR, 
    (ERROR = premature_failure -> call(EARLY) ; call(LATE))
  ).  

ground_all(TERM, EXP) :- 
  term_variables(EXP, VARS),
  maplist_cut('='(TERM), VARS).



%%%%%%%%%%%%%%%% SYNTACTIC %%%%%%%%%%%%%%%% 

type_form(a, $and(_, _)). 
type_form(a, $not($or(_, _))). 
type_form(a, $not($imp(_, _))). 
type_form(a, $iff(_, _)). 
type_form(b, $not($and(_, _))). 
type_form(b, $or(_, _)). 
type_form(b, $imp(_, _)). 
type_form(b, $not($iff(_, _))). 
type_form(c, $fa(_)). 
type_form(c, $not($ex(_))). 
type_form(d, $not($fa(_))). 
type_form(d, $ex(_)). 
type_form(n, $not($not(_))).
type_hyp(TYPE, (_, FORM)) :- type_form(TYPE, FORM).

hyp_form((_, FORM), FORM).

atomic_form($rel(_, _)).
literal(AF) :- atomic_form(AF).
literal($not(AF)) :- atomic_form(AF).

complements(FORM_A, $not(FORM_B)) :- FORM_A == FORM_B.
complements($not(FORM_A), FORM_B) :- FORM_A == FORM_B.

incr_var_term(VAR, _) :- var(VAR), !, false.
incr_var_term($var(NUM), $var(SUCC)) :- !, num_succ(NUM, SUCC).
incr_var_term($dst(STR), $dst(STR)) :- !.
incr_var_term($fun(FUN, TERMS_I), $fun(FUN, TERMS_O)) :- 
  maplist_cut(incr_var_term, TERMS_I, TERMS_O).

substitute_term(fast, _, _, VAR, VAR) :- var(VAR), !.
substitute_term(_, _, _, $dst(STR), $dst(STR)) :- !.
substitute_term(safe, _, _, VAR, _) :- var(VAR), !, false.
substitute_term(_, CNT, TERM_S, $var(NUM), TERM_O) :- !, 
  CNT = NUM -> TERM_O = TERM_S 
; 
  CNT < NUM -> 
  num_pred(NUM, PRED), 
  TERM_O = $var(PRED) 
; 
  TERM_O = $var(NUM).
substitute_term(MODE, NUM, TERM, $fun(FUN, TERMS_I), $fun(FUN, TERMS_O)) :- !, 
  maplist_cut(substitute_term(MODE, NUM, TERM), TERMS_I, TERMS_O).

resymb_term(_, VAR, VAR) :- var(VAR), !.
resymb_term(_, $var(NUM), $var(NUM)) :- !.
resymb_term(_, $dst(STR), $dst(STR)) :- !.
resymb_term(DICT, $fun(FUN_I, TERMS_I), $fun(FUN_O, TERMS_O)) :- 
  length(TERMS_I, ARI),
  maplist_cut(resymb_term(DICT), TERMS_I, TERMS_O), !, 
  (
    get_assoc((FUN_I, ARI), DICT, IDX) -> 
    FUN_O = $par(IDX)
  ;    
    FUN_O = FUN_I
  ).

log_const($true).
log_const($false).

substitute_form(_, _, _, FORM, FORM) :- log_const(FORM), !.

substitute_form(MODE, NUM, TERM, $not(FORM), $not(FORM_N)) :- !,
  substitute_form(MODE, NUM, TERM, FORM, FORM_N).

substitute_form(MODE, NUM, TERM, FORM_I, FORM_O) :-
  decom_qtf(FORM_I, QTF, SUB_I), !, 
  num_succ(NUM, SUCC),
  ( 
    MODE = safe -> 
    incr_var_term(TERM, TERM_N) ; 
    TERM_N = TERM
  ),
  substitute_form(MODE, SUCC, TERM_N, SUB_I, SUB_O), 
  apply_uop(QTF, SUB_O, FORM_O). 

substitute_form(MODE, NUM, TERM, FORM, FORM_N) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !, 
  substitute_form(MODE, NUM, TERM, FORM_A, FORM_AN),
  substitute_form(MODE, NUM, TERM, FORM_B, FORM_BN),
  apply_bop(BCT, FORM_AN, FORM_BN, FORM_N). 

substitute_form(MODE, NUM, TERM, $rel(REL, TERMS_I), $rel(REL, TERMS_O)) :- 
  maplist_cut(substitute_term(MODE, NUM, TERM), TERMS_I, TERMS_O).

substitute_form(MODE, TERM, FORM, FORM_N) :- 
  substitute_form(MODE, 0, TERM, FORM, FORM_N).

resymb_form(_, FORM, FORM) :- log_const(FORM), !.

resymb_form(DICT, FORM, FORM_N) :-
  decom_uct(FORM, UCT, SUB), !, 
  resymb_form(DICT, SUB, SUB_N),
  apply_uop(UCT, SUB_N, FORM_N). 

resymb_form(DICT, FORM, FORM_N) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !,  
  resymb_form(DICT, FORM_A, FORM_AN),
  resymb_form(DICT, FORM_B, FORM_BN),
  apply_bop(BCT, FORM_AN, FORM_BN, FORM_N). 

resymb_form((RDICT, FDICT), $rel(REL_I, TERMS_I), $rel(REL_O, TERMS_O)) :- 
  maplist_cut(resymb_term(FDICT), TERMS_I, TERMS_O), !,  
  length(TERMS_O, ARI),
  (
    get_assoc((REL_I, ARI), RDICT, IDX) -> 
    REL_O = $par(IDX)
  ;
    REL_O = REL_I
  ).

break_a(l, $and(FORM, _), FORM).
break_a(r, $and(_, FORM), FORM).
break_a(l, $not($or(FORM, _)), $not(FORM)).
break_a(r, $not($or(_, FORM)), $not(FORM)).
break_a(l, $not($imp(FORM, _)), FORM).
break_a(r, $not($imp(_, FORM)), $not(FORM)).
break_a(l, $iff(FORM_A, FORM_B), $imp(FORM_A, FORM_B)).
break_a(r, $iff(FORM_A, FORM_B), $imp(FORM_B, FORM_A)).

break_b($not($and(FORM_A, FORM_B)), $not(FORM_A), $not(FORM_B)).
break_b($or(FORM_A, FORM_B), FORM_A, FORM_B).
break_b($imp(FORM_A, FORM_B), $not(FORM_A), FORM_B).
break_b($not($iff(FORM_A, FORM_B)), $not($imp(FORM_A, FORM_B)), $not($imp(FORM_B, FORM_A))).

break_c(TERM, $fa(FORM_I), FORM_O) :- substitute_form(fast, TERM, FORM_I, FORM_O).
break_c(TERM, $not($ex(FORM_I)), $not(FORM_O)) :- substitute_form(fast, TERM, FORM_I, FORM_O).

break_d(NUM, $not($fa(FORM_I)), $not(FORM_O)) :- 
  substitute_form(fast, $fun($par(NUM), []), FORM_I, FORM_O).
break_d(NUM, $ex(FORM_I), FORM_O) :-
  substitute_form(fast, $fun($par(NUM), []), FORM_I, FORM_O).

break_n($not($not(FORM)), FORM).



%%%%%%%%%%%%%%%% BASIC RULES %%%%%%%%%%%%%%%% 

apply_a(
  (PID, FORM_P),
  DIR, 
  (a(PID, DIR, PRF), CNT), 
  (CNT, FORM_C), 
  (PRF, SUCC)
) :- 
  num_succ(CNT, SUCC), 
  break_a(DIR, FORM_P, FORM_C), !.

apply_b(
  (PID, FORM), 
  (b(PID, PRF_A, PRF_B), CNT), 
  (CNT, FORM_A),
  (CNT, FORM_B),
  (PRF_A, SUCC),
  (PRF_B, SUCC)
) :- 
  num_succ(CNT, SUCC), 
  break_b(FORM, FORM_A, FORM_B), !.

apply_c(
  (PID, FORM_P), 
  TERM, 
  (c(PID, TERM, PRF), CNT), 
  (CNT, FORM_C),
  (PRF, SUCC)
) :- 
  num_succ(CNT, SUCC),
  break_c(TERM, FORM_P, FORM_C), !.

apply_d(
  (PID, FORM_P),
  (d(PID, PRF), CNT), 
  (CNT, FORM_C),
  (PRF, SUCC)
) :-
  num_succ(CNT, SUCC),
  break_d(CNT, FORM_P, FORM_C), !.

apply_s(
  FORM,
  (s(FORM, PRF_A, PRF_B), CNT), 
  (CNT, $not(FORM)),
  (CNT, FORM),
  (PRF_A, SUCC), 
  (PRF_B, SUCC)
) :-
  num_succ(CNT, SUCC), !.

apply_t(
  FORM,
  (t(FORM, PRF), CNT),
  (CNT, FORM),
  (PRF, SUCC)
) :- 
  num_succ(CNT, SUCC), !.

apply_n(
  (PID, $not($not(FORM))),
  (n(PID, PRF), CNT), 
  (CNT, FORM),
  (PRF, SUCC)
) :- 
  num_succ(CNT, SUCC), !.

apply_x(
  (PID, FORM_P), 
  (NID, $not(FORM_N)), 
  (x(PID, NID), _)
) :-
  unify_with_occurs_check(FORM_P, FORM_N), !.

justified(_, $not($false)). 
justified(_, $true). 
justified(_, $fa($rel('=', [$var(0), $var(0)]))).
justified(_, $fa($fa($imp($rel('=', [$var(1), $var(0)]), $rel('=', [$var(0), $var(1)]))))).
justified(_, $fa($fa($fa(
  $imp(
    $rel('=', [$var(2), $var(1)]), 
    $imp(
      $rel('=', [$var(1), $var(0)]), 
      $rel('=', [$var(2), $var(0)])
    )
))))).

justified(_, FORM) :- is_mono_rel(0, FORM). 
justified(_, FORM) :- is_mono_fun(0, FORM). 

% justified(_, + ((FUNA ^ []) = (FUNB ^ [])), [ne_eval]) :- 
%   atom_number(FUNA, NUMA),
%   atom_number(FUNB, NUMB),
%   NUMA \= NUMB.
% 
% justified(_, - ((FUNA ^ []) = (FUNB ^ [])), [ne_eval]) :- 
%   atom_number(FUNA, NUMA),
%   atom_number(FUNB, NUMB),
%   NUMA \= NUMB.

%justified(C, $pos($rel(par(C), TERMS))) :- maplist_cut(counter_safe(C), TERMS).
%justified(C, $pos($not($rel(par(C), TERMS)))) :- maplist_cut(counter_safe(C), TERMS).

justified(C, FORM) :- 
  strip_fas(FORM, ARI, $imp($ex(ANTE), CONS)), 
  counter_safe(C, ANTE),
  mk_vars(ARI, VARS), 
  substitute_form(safe, $fun($par(C), VARS), ANTE, TEMP),
  TEMP == CONS.

justified(C, FORM) :- 
  strip_fas(FORM, ARI, $iff($rel($par(C), VARS), BODY)), 
  counter_safe(C, BODY),
  mk_vars(ARI, VARS).

is_mono_rel(NUM, $fa($fa($imp($rel('=', [$var(1), $var(0)]), FORM)))) :- !,
  num_succ(NUM, SUCC), 
  is_mono_rel(SUCC, FORM). 
   
is_mono_rel(NUM, $imp($rel(REL, TERMS_A), $rel(REL, TERMS_B))) :- 
  mk_mono_args(NUM, TERMS_A, TERMS_B).

is_mono_fun(N, $fa($fa($imp($rel('=', [$var(1), $var(0)]), F)))) :- !,
  num_succ(N, SN), 
  is_mono_fun(SN, F). 
   
is_mono_fun(NUM, $rel('=', [$fun(FUN, TERMS_A), $fun(FUN, TERMS_B)])) :- 
  mk_mono_args(NUM, TERMS_A, TERMS_B).



%%%%%%%%%%%%%%%% DERIVED RULES %%%%%%%%%%%%%%%% 

apply(n, HYP, GOAL, [([HYP_O], GOAL_O)]) :- apply_n(HYP, GOAL, HYP_O, GOAL_O).
apply(a, HYP, GOAL, [([HYP_L, HYP_R], GOAL_O)]) :- apply_aa(HYP, GOAL, HYP_L, HYP_R, GOAL_O). 
apply(d, HYP, GOAL, [([HYP_O], GOAL_O)]) :- apply_d(HYP, GOAL, HYP_O, GOAL_O).
apply(c, HYP, GOAL, [([HYP_O], GOAL_O)]) :- apply_c(HYP, _, GOAL, HYP_O, GOAL_O).
apply(b, HYP, GOAL, [([HYP_L], GOAL_L), ([HYP_R], GOAL_R)]) :- apply_b(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

rp_aux(RULS, HYPS_A, HYPS_B, (HYPS_M, GOAL), IN, OUT) :- 
  append([HYPS_A, HYPS_M, HYPS_B], HYPS), !,
  rp_core(RULS, HYPS, GOAL, IN, OUT).

rp_core(RULS, HYPS, GOAL, IN, OUT) :-
  member(RUL, RULS), 
  append(HYPS_A, [HYP | HYPS_B], HYPS), 
  apply(RUL, HYP, GOAL, HSGS), !,
  foldl_cut(rp_aux(RULS, HYPS_A, HYPS_B), HSGS, IN, OUT), !.
rp_core(_, HYPS, GOAL, [(HYPS, GOAL) | OUT], OUT).

rp(RULS, HYPS, GOAL, HSGS) :- rp_core(RULS, HYPS, GOAL, HSGS, []).
rp(RULS, HYPS, GOAL, HYPS_O, GOAL_O) :- rp(RULS, HYPS, GOAL, [(HYPS_O, GOAL_O)]).

/*
many(RULS, (HYPS, GOAL), HGS) :-
  member(n, RULS), 
  pluck(HYPS, HYP, REST), 
  apply_n(HYP, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(a, RULS), 
  pluck(HYPS, HYP, REST), 
  apply_aa(HYP, GOAL, HYP_L, HYP_R, GOAL_T), !,
  many(RULS, ([HYP_R, HYP_L | REST], GOAL_T), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(d, RULS), 
  pluck(HYPS, HYP, REST), 
  apply_d(HYP, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(c, RULS), 
  pluck(HYPS, HYP, REST), 
  apply_c(HYP, _, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(b, RULS), 
  pluck(HYPS, HYP, REST), 
  apply_b(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), !, 
  many(RULS, ([HYP_L | REST], GOAL_L), HGSL), !,
  many(RULS, ([HYP_R | REST], GOAL_R), HGSR),
  append(HGSL, HGSR, HGS). 

many(_, HG, [HG]).

many_nb(RULS, HYPS, GOAL, HYP_NS, GOAL_N) :-
  many(RULS, (HYPS, GOAL), [(HYP_NS, GOAL_N)]).

*/

apply_aa(HYP, GOAL, HYP_L, HYP_R, GOAL_N) :- 
  apply_a(HYP, l, GOAL, HYP_L, GOAL_T), 
  apply_a(HYP, r, GOAL_T, HYP_R, GOAL_N). 

apply_ab(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) :- 
  apply_b(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_TL, GOAL_TR), 
  apply_a(HYP_A, l, GOAL_TL, HYP_AL, GOAL_L),
  apply_a(HYP_A, r, GOAL_TR, HYP_AR, GOAL_R).

apply_ab_rev(HYP_A, HYP_B, GOAL, HYP_AR, HYP_BL, GOAL_L, HYP_AL, HYP_BR, GOAL_R) :- 
  apply_b(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_TL, GOAL_TR), 
  apply_a(HYP_A, r, GOAL_TL, HYP_AR, GOAL_L),
  apply_a(HYP_A, l, GOAL_TR, HYP_AL, GOAL_R).

apply_sb_lem(HYP, GOAL, HYP_L, HYP_R, HYP_NL, GOAL_L, GOAL_R) :- 
  hyp_form(HYP, FORM), 
  break_b(FORM, FORM_L, _),
  apply_s(FORM_L, GOAL, HYP_NL, HYP_L, GOAL_NL, GOAL_L), 
  apply_b(HYP, GOAL_NL, HYP_PL, HYP_R, GOAL_PNL, GOAL_R), 
  mate(HYP_PL, HYP_NL, GOAL_PNL).

apply_cd(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  GOAL = (_, CNT), 
  apply_d(HYP_D, GOAL, HYP_N_D, GOAL_T), 
  apply_c(HYP_C, $fun($par(CNT), []), GOAL_T, HYP_N_C, GOAL_N). 

apply_d_lax(CNT_I, HYP_I, GOAL_I, CNT_O, HYP_O, GOAL_O) :-  
  apply_d(HYP_I, GOAL_I, HYP_T, GOAL_T) -> 
  ( 
    vac_qtf(HYP_I) -> CNT_T = CNT_I ;
    num_succ(CNT_I, CNT_T)
  ),
  apply_d_lax(CNT_T, HYP_T, GOAL_T, CNT_O, HYP_O, GOAL_O) 
;
  CNT_O = CNT_I, 
  HYP_O = HYP_I, 
  GOAL_O = GOAL_I. 
  
apply_c_vac(HYP_I, GOAL_I, HYP_O, GOAL_O) :-  
  vac_qtf(HYP_I),
  apply_c(HYP_I, _, GOAL_I, HYP_O, GOAL_O).

dp_vac(HYP_I, GOAL_I, HYP_O, GOAL_O) :-  
  vac_qtf(HYP_I),
  apply_d(HYP_I, GOAL_I, HYP_O, GOAL_O).

cp_lax(CNT, HYP_I, GOAL_I, HYP_O, GOAL_O) :-  
  vac_qtf(HYP_I) ->  
  (
    apply_c(HYP_I, _, GOAL_I, HYP_T, GOAL_T) -> 
    cp_lax(CNT, HYP_T, GOAL_T, HYP_O, GOAL_O)  
  ;
    HYP_O = HYP_I, 
    GOAL_O = GOAL_I
  )
;
  (
    num_pred(CNT, PRED) -> 
    apply_c(HYP_I, _, GOAL_I, HYP_T, GOAL_T),
    cp_lax(PRED, HYP_T, GOAL_T, HYP_O, GOAL_O)  
  ;
    HYP_O = HYP_I, 
    GOAL_O = GOAL_I
  ).

apply_cd_lax(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  type_hyp(d, HYP_D),
  type_hyp(c, HYP_C),
  apply_d_lax(0, HYP_D, GOAL, CNT, HYP_N_D, GOAL_T), 
  cp_lax(CNT, HYP_C, GOAL_T, HYP_N_C, GOAL_N). 
  
union([], []).

union([List | Lists], Set) :- 
  union(Lists, TempSet),
  union(List, TempSet, Set).

write_term_punct(STRM, TERM) :- 
  write_term(STRM, TERM, [nl(true), quoted(true), fullstop(true)]).

write_list(_, []).
write_list(STRM, [ELEM | LIST]) :- 
  write(STRM, ELEM),
  write_list(STRM, LIST).

writeln_list(_, []).
writeln_list(STRM, [ELEM | LIST]) :- 
  format(STRM, '~w\n', ELEM),
  writeln_list(STRM, LIST).

writeln_list([]).
writeln_list([Elem | List]) :- 
  format('~w\n', Elem),
  writeln_list(List).

strings_concat([], "").

strings_concat([Str | Strs], NewStr) :- 
  strings_concat(Strs, TempStr), 
  string_concat(Str, TempStr, NewStr). 

strings_concat_with(_, [], "").

strings_concat_with(_, [Str], Str).

strings_concat_with(Div, [Str | Strs], Result) :-
  strings_concat_with(Div, Strs, TempStr),
  strings_concat([Str, Div, TempStr], Result).

write_file(FILE, TERM) :-
  open(FILE, write, STRM),
  write(STRM, TERM),
  close(STRM).

pluck_uniq(List, Elem, REST) :- 
  pluck_uniq([], List, Elem, REST).

pluck_uniq(Acc, [Elem | List], Elem, REST) :- 
  \+ member(Elem, Acc),
  append(Acc, List, REST).

pluck_uniq(Acc, [Elem | List], Pick, REST) :- 
  pluck_uniq([Elem | Acc], List, Pick, REST).

pluck(0, LIST, [], LIST) :- !.
pluck(NUM, [ELEM | LIST], [ELEM | ELEMS], REST) :- 
  num_pred(NUM, PRED), 
  pluck(PRED, LIST, ELEMS, REST).
pluck(NUM, [ELEM | LIST], ELEMS, [ELEM | REST]) :- 
  pluck(NUM, LIST, ELEMS, REST).

pluck([Elem | Rem], Elem, Rem).

pluck([ElemA | List], ElemB, [ElemA | Rem]) :- 
  pluck(List, ElemB, Rem).

num_succ(NUM, SUCC) :-
  SUCC is NUM + 1.

num_pred(NUM, PRED) :-
  0 < NUM,
  PRED is NUM - 1.

prob_id_hyp(PROB, ID, (ID, SF)) :- 
  get_assoc(ID, PROB, SF).

% molecular(Exp) :- 
%   member(Exp, 
%     [ $fa(_), $ex(_), $not(_), 
%       $or(_, _), $and(_, _), $imp(_, _), $iff(_, _) ]).

lit_atom($not(ATOM), ATOM) :- !. 
lit_atom(ATOM, ATOM).

decom_uct(FORM, not, SUB) :- \+ var(FORM), FORM = $not(SUB). 
decom_uct(FORM, QTF, SUB) :- decom_qtf(FORM, QTF, SUB).
decom_qtf(FORM, ex, SUB) :- \+ var(FORM), FORM = $ex(SUB).
decom_qtf(FORM, fa, SUB) :- \+ var(FORM), FORM = $fa(SUB).

decom_bct(FORM, BCT, FORM_A, FORM_B) :- 
  \+ var(FORM),
  FORM = $TEMP, 
  TEMP =.. [BCT, FORM_A, FORM_B],
  member(BCT, [and, or, imp, iff]).

apply_uop(UCT, FORM, $SUB) :- 
  SUB =.. [UCT, FORM].

apply_bop(BCT, FORM_A, FORM_B, $SUB) :- 
  SUB =.. [BCT, FORM_A, FORM_B].

maplist_cut(_, []).

maplist_cut(GOAL, [Elem | List]) :- 
  call(GOAL, Elem), !, 
  maplist_cut(GOAL, List). 

maplist_cut(_, [], []).

maplist_cut(GOAL, [ElemA | ListA], [ElemB | ListB]) :- 
  call(GOAL, ElemA, ElemB), !, 
  maplist_cut(GOAL, ListA, ListB). 

maplist_cut(_, [], [], []).

maplist_cut(GOAL, [ElemA | ListA], [ElemB | ListB], [ElemC | ListC]) :- 
  call(GOAL, ElemA, ElemB, ElemC), !, 
  maplist_cut(GOAL, ListA, ListB, ListC). 

maplist_cut(_, [], [], [], []).

maplist_cut(GOAL, [ElemA | ListA], [ElemB | ListB], [ElemC | ListC], [ElemD | ListD]) :- 
  call(GOAL, ElemA, ElemB, ElemC, ElemD), !, 
  maplist_cut(GOAL, ListA, ListB, ListC, ListD). 

maplist_idx(_, _, []).

maplist_idx(GOAL, NUM, [Elem | List]) :- 
  call(GOAL, NUM, Elem), 
  num_succ(NUM, Succ),
  maplist_idx(GOAL, Succ, List).

maplist_idx(_, _, [], []).

maplist_idx(GOAL, NUM, [ElemA | ListA], [ElemB | ListB]) :- 
  call(GOAL, NUM, ElemA, ElemB), 
  num_succ(NUM, Succ),
  maplist_idx(GOAL, Succ, ListA, ListB).

mk_vars(NUM, VARS) :- 
  mk_vars(asc, NUM, VARS) ;
  mk_vars(desc, NUM, VARS).

mk_vars(DIR, NUM, VARS) :- 
  range(DIR, NUM, NUMS), 
  maplist([X,$var(X)]>>true, NUMS, VARS).

/* Monotonicity */

mk_mono_args(0, [], []).

mk_mono_args(NUM, [$var(NUMA) | VARSA], [$var(NUMB) | VARSB]) :-
  NUMA is (NUM * 2) - 1, 
  NUMB is (NUM * 2) - 2, 
  num_pred(NUM, PRED),
  mk_mono_args(PRED, VARSA, VARSB).

mk_mono_eq(NUM, FUN, $rel('=', [$fun(FUN, VARS_A), $fun(FUN, VARS_B)])) :- 
  mk_mono_args(NUM, VARS_A, VARS_B).

mk_mono_imp(NUM, REL, $imp($rel(REL, VARS_A), $rel(REL, VARS_B))) :- 
  mk_mono_args(NUM, VARS_A, VARS_B), !.

mk_mono_fun(NUM, FUN, MONO) :- 
  mk_mono_eq(NUM, FUN, Eq), 
  mk_mono(NUM, Eq, MONO), !.

mk_mono_rel(NUM, REL, MONO) :- 
  mk_mono_imp(NUM, REL, IMP), 
  mk_mono(NUM, IMP, MONO).

member_rev(Elem, [_ | List]) :-
  member_rev(Elem, List). 

member_rev(Elem, [Elem | _]).

mk_mono(0, Cons, Cons).

mk_mono(NUM, Cons, $fa($fa($imp($rel('=', [$var(1), $var(0)]), MONO)))) :-
  num_pred(NUM, Pred), 
  mk_mono(Pred, Cons, MONO), !.

orient_dir(OPF, ONF, l, OPF, ONF).
orient_dir(ONF, OPF, r, OPF, ONF).
orient_dir(OPF, ONF, a, OPF, ONF).
orient_dir(ONF, OPF, a, OPF, ONF).

orient_literal_hyps(HYP_P, HYP_N, HYP_P, HYP_N) :- 
  HYP_P = (_, $rel(_, _)), 
  HYP_N = (_, $not($rel(_, _))).

orient_literal_hyps(HYP_N, HYP_P, HYP_P, HYP_N) :- 
  HYP_P = (_, $rel(_, _)), 
  HYP_N = (_, $not($rel(_, _))).

strip_fas($fa(FORM), NUM, BODY) :- !,
  strip_fas(FORM, PRED, BODY), 
  num_succ(PRED, NUM).

strip_fas(Form, 0, Form).

inst_with_lvs($fa(FORM), BODY) :- !,
  substitute_form(fast, _, FORM, TEMP), 
  inst_with_lvs(TEMP, BODY).

inst_with_lvs(FORM, FORM).

add_fas(0, Form, Form). 
add_fas(NUM, Form, $fa(NewForm)) :-
  num_pred(NUM, Pred), 
  add_fas(Pred, Form, NewForm).

snd((_, X), X).

range(desc, 0, []). 
range(desc, NUM, [Pred | NUMs]) :- 
  num_pred(NUM, Pred),  
  range(desc, Pred, NUMs). 

range(asc, NUM, NUMS) :- 
  range(desc, NUM, REV),
  reverse(REV, NUMS).

stream_strings(STRM, STRS) :-
  read_line_to_string(STRM, STR), 
  (
    STR = end_of_file -> 
    STRS = [] 
  ;
    STRS = [STR | REST],
    stream_strings(STRM, REST)
  ).

read_file_strings(FILE, STRS) :-
  open(FILE, read, STRM), 
  stream_strings(STRM, STRS), 
  close(STRM).

foldl_cut(_, [], V, V).
foldl_cut(GOAL, [ELEM | LIST], V_I, V_O) :- 
  call(GOAL, ELEM, V_I, V_T), !, 
  foldl_cut(GOAL, LIST, V_T, V_O).

string_number(Str, NUM) :- 
  number_string(NUM, Str).

no_bv_term(_, VAR) :- var(VAR), !.
no_bv_term(CNT, $var(NUM)) :- !, NUM \= CNT.
no_bv_term(_, $dst(_)) :- !.
no_bv_term(CNT, $fun(_, TERMS)) :- 
  maplist_cut(no_bv_term(CNT), TERMS).

no_bv_form(_, $true).
no_bv_form(_, $false). 
no_bv_form(NUM, $not(FORM)) :- !, 
  no_bv_form(NUM, FORM). 
no_bv_form(NUM, FORM) :- 
  decom_qtf(FORM, _, SUB), !, 
  num_succ(NUM, SUCC),
  no_bv_form(SUCC, SUB).
no_bv_form(NUM, FORM) :- 
  decom_bct(FORM, _, FORM_A, FORM_B), !, 
  no_bv_form(NUM, FORM_A),
  no_bv_form(NUM, FORM_B).
no_bv_form(NUM, $rel(_, TERMS)) :- 
  maplist_cut(no_bv_term(NUM), TERMS).

vac_qtf((_, $fa(FORM))) :- no_bv_form(0, FORM).
vac_qtf((_, $not($fa(FORM)))) :- no_bv_form(0, FORM).
vac_qtf((_, $ex(FORM))) :- no_bv_form(0, FORM).
vac_qtf((_, $not($ex(FORM)))) :- no_bv_form(0, FORM).

no_fv_term(_, VAR) :- var(VAR), !, false.
no_fv_term(_, $dst(_)) :- !.
no_fv_term(CNT, $var(NUM)) :- !, NUM < CNT.
no_fv_term(CNT, $fun(_, TERMS)) :- 
  maplist_cut(no_fv_term(CNT), TERMS).

no_fv_form(_, FORM) :- log_const(FORM), !.
no_fv_form(NUM, $not(FORM)) :- !, 
  no_fv_form(NUM, FORM). 
no_fv_form(NUM, FORM) :- 
  decom_qtf(FORM, _, SUB), !, 
  num_succ(NUM, SUCC),
  no_fv_form(SUCC, SUB).
no_fv_form(NUM, FORM) :- 
  decom_bct(FORM, _, FORM_A, FORM_B), !, 
  no_fv_form(NUM, FORM_A),
  no_fv_form(NUM, FORM_B).
no_fv_form(NUM, $rel(_, TERMS)) :- 
  maplist_cut(no_fv_term(NUM), TERMS).

has_par_ge(CNT, EXP) :- 
  sub_term($par(NUM), EXP), 
  CNT =< NUM.

counter_safe(C, X) :- 
  ground(X), 
  \+ has_par_ge(C, X).

fnnf($imp(FORM_A, FORM_B), $or(NORM_A, NORM_B)) :- !, 
  fnnf($not(FORM_A), NORM_A), 
  fnnf(FORM_B, NORM_B).

fnnf($iff(FORM_A, FORM_B), $and(NORM_A, NORM_B)) :- !, 
  fnnf($imp(FORM_A, FORM_B), NORM_A), 
  fnnf($imp(FORM_B, FORM_A), NORM_B).

fnnf(FORM, NORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !, 
  fnnf(FORM_A, NORM_A), 
  fnnf(FORM_B, NORM_B),
  apply_bop(BCT, NORM_A, NORM_B, NORM).

fnnf(FORM, NORM) :- 
  decom_qtf(FORM, QTF, BODY), !, 
  fnnf(BODY, TEMP),
  apply_uop(QTF, TEMP, NORM).

fnnf($not($not(FORM)), NORM) :- !, fnnf(FORM, NORM).

fnnf($not($and(FORM_A, FORM_B)), $or(NORM_A, NORM_B)) :- !, 
  fnnf($not(FORM_A), NORM_A), 
  fnnf($not(FORM_B), NORM_B).

fnnf($not($or(FORM_A, FORM_B)), $and(NORM_A, NORM_B)) :- !, 
  fnnf($not(FORM_A), NORM_A), 
  fnnf($not(FORM_B), NORM_B).

fnnf($not($imp(FORM_A, FORM_B)), $and(NORM_A, NORM_B)) :- !, 
  fnnf(FORM_A, NORM_A), 
  fnnf($not(FORM_B), NORM_B).

fnnf($not($iff(FORM_A, FORM_B)), $and(NORM_A, NORM_B)) :- !, 
  fnnf($or($not(FORM_A), $not(FORM_B)), NORM_A), 
  fnnf($or(FORM_A, FORM_B), NORM_B).

fnnf($not($fa(FORM)), $ex(NORM)) :- !, 
  fnnf($not(FORM), NORM).

fnnf($not($ex(FORM)), $fa(NORM)) :- !, 
  fnnf($not(FORM), NORM).

fnnf(FORM, FORM). 

split_at(NUM, LIST, FST, SND) :- 
  split_at(NUM, [], LIST, FST, SND).

split_at(0, ACC, SND, FST, SND) :-
   reverse(ACC, FST).
  
split_at(NUM, ACC, [ELEM | LIST], FST, SND) :-
  num_pred(NUM, PRED), 
  split_at(PRED, [ELEM | ACC], LIST, FST, SND).

char_uct('~', not).
char_uct('!', fa).
char_uct('?', ex).

char_bct('|', or).
char_bct('&', and).
char_bct('>', imp).
char_bct('=', iff).



%%%%%%%%%%%%%%%% PUT %%%%%%%%%%%%%%%% 

put_list(STRM, _, []) :- 
  put_char(STRM, '.').

put_list(STRM, PTR, [ELEM | LIST]) :- 
  put_char(STRM, ','),
  call(PTR, STRM, ELEM),
  put_list(STRM, PTR, LIST), !.

put_end(STRM) :-
  put_char(STRM, '%').

put_bytes(_, []).

put_bytes(STRM, [BYTE | BYTES]) :- 
  put_byte(STRM, BYTE),
  put_bytes(STRM, BYTES).

put_bytes_dollar(STRM, BYTES) :- 
  put_bytes(STRM, BYTES), 
  put_end(STRM). 

put_string(STRM, STR) :- 
  string_codes(STR, BYTES), 
  put_bytes_dollar(STRM, BYTES).

put_atom(STRM, ATOM) :- 
  atom_codes(ATOM, BYTES),
  put_bytes_dollar(STRM, BYTES).

put_dir(STRM, l) :- 
  put_char(STRM, "<").

put_dir(STRM, r) :- 
  put_char(STRM, ">").

put_num(STRM, NUM) :- 
  number_codes(NUM, BYTES),
  put_bytes_dollar(STRM, BYTES).
 
put_name(STRM, NAME) :- 
  atom(NAME), !, 
  put_char(STRM, '\''), 
  put_atom(STRM, NAME).
put_name(STRM, NAME) :- 
  number(NAME), !,
  put_char(STRM, '#'), 
  put_num(STRM, NAME).
  
put_term(STRM, $var(NUM)) :- !, 
  put_char(STRM, '#'), 
  put_num(STRM, NUM).
put_term(STRM, $dst(STR)) :- !,
  put_char(STRM, '"'), 
  put_string(STRM, STR). 
put_term(STRM, $fun(FUN, TERMS)) :- 
  put_char(STRM, '^'), 
  put_functor(STRM, FUN), 
  put_terms(STRM, TERMS). 

put_terms(STRM, TERMS) :- 
  put_list(STRM, put_term, TERMS).

put_form(STRM, $true) :- !, put_char(STRM, 'T').
put_form(STRM, $false) :- !, put_char(STRM, 'F').
put_form(STRM, FORM) :- 
  decom_uct(FORM, UCT, SUB), !, 
  char_uct(CH, UCT),
  put_char(STRM, CH), 
  put_form(STRM, SUB).
put_form(STRM, FORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !, 
  char_bct(CH, BCT), !,
  put_char(STRM, CH), 
  put_form(STRM, FORM_A),
  put_form(STRM, FORM_B).
put_form(STRM, $rel(REL, TERMS)) :- 
  put_char(STRM, '^'), 
  put_functor(STRM, REL), 
  put_terms(STRM, TERMS).

put_functor(STRM, $par(NUM)) :- !,
  put_char(STRM, '@'), 
  put_num(STRM, NUM). 
put_functor(STRM, FTR) :- 
  put_char(STRM, '\''), 
  put_atom(STRM, FTR). 

put_prf(STRM, a(ID, DIR, PRF)) :- 
  put_char(STRM, 'A'), 
  put_num(STRM, ID), 
  put_dir(STRM, DIR),
  put_prf(STRM, PRF).
  
put_prf(STRM, b(ID, PRF_L, PRF_R)) :- 
  put_char(STRM, 'B'), 
  put_num(STRM, ID), 
  put_prf(STRM, PRF_L),
  put_prf(STRM, PRF_R).

put_prf(STRM, c(ID, TERM, PRF)) :- 
  put_char(STRM, 'C'), 
  put_num(STRM, ID), 
  put_term(STRM, TERM),
  put_prf(STRM, PRF).

put_prf(STRM, d(ID, PRF)) :- 
  put_char(STRM, 'D'), 
  put_num(STRM, ID), 
  put_prf(STRM, PRF).

put_prf(STRM, n(ID, PRF)) :- 
  put_char(STRM, 'N'), 
  put_num(STRM, ID), 
  put_prf(STRM, PRF).

put_prf(STRM, s(FORM, PRF_L, PRF_R)) :- 
  put_char(STRM, 'S'), 
  put_form(STRM, FORM), 
  put_prf(STRM, PRF_L),
  put_prf(STRM, PRF_R).

put_prf(STRM, h(ID, PRF)) :- 
  put_char(STRM, 'H'), 
  put_num(STRM, ID), 
  put_prf(STRM, PRF).

put_prf(STRM, t(FORM, PRF)) :- 
  put_char(STRM, 'T'), 
  put_form(STRM, FORM), 
  put_prf(STRM, PRF).

put_prf(STRM, x(PID, NID)) :- 
  put_char(STRM, 'X'), 
  put_num(STRM, PID), 
  put_num(STRM, NID).



%%%%%%%%%%%%%%%% TACTICS  %%%%%%%%%%%%%%%%

% eq_refl(CONC, GOAL)
% --- 
% GOAL := ... |- CONC : TERM = TERM, ...
eq_refl(CONC, GOAL) :- 
  apply_t($fa($rel('=', [$var(0), $var(0)])), GOAL, HYP0, GOAL_T), 
  apply_c(HYP0, _, GOAL_T, HYP1, GOAL_N), 
  apply_x(HYP1, CONC, GOAL_N).

% eq_symm(TERMA, TERMB, GOAL)
% --- 
% GOAL ::= PID : TERMA = TERMB, ... |- NID : TERMB = TERMA, ...
% IPF = PID + TERMA = TERMB
% INF = NID - TERMB = TERMA
eq_symm(OPF, ONF, GOAL) :- 
  OPF = (_, $rel('=', [TERM_A, TERM_B])), 
  ONF = (_, $not($rel('=', [TERM_B, TERM_A]))),
  apply_t($fa($fa($imp($rel('=', [$var(1), $var(0)]), $rel('=', [$var(0), $var(1)])))), GOAL, HYP0, GOAL0), 
  apply_c(HYP0, TERM_A, GOAL0, HYP1, GOAL1), 
  apply_c(HYP1, TERM_B, GOAL1, HYP2, GOAL2), 
  apply_b(HYP2, GOAL2, HYP3, HYP4, GOAL3, GOAL4), 
  mate_pn(OPF, HYP3, GOAL3), 
  mate_pn(HYP4, ONF, GOAL4). 

eq_symm(OPF, GOAL, NewOPF, GOAL_N) :- 
  OPF = (_, $rel('=', [TERM_A, TERM_B])), 
  apply_s(TERM_B = TERM_A, GOAL, ONF, NewOPF, GOAL_T, GOAL_N), 
  eq_symm(OPF, ONF, GOAL_T).

eq_trans(IPF0, IPF1, INF, GOAL) :- 
  IPF0 = (_, $rel('=', [TERM_A, TERM_B])), !,
  IPF1 = (_, $rel('=', [TERM_B, TERM_C])), !,
  INF =  (_, $not($rel('=', [TERM_A, TERM_C]))), !,
  apply_t($fa($fa($fa($imp($rel('=', [$var(2), $var(1)]), $imp($rel('=', [$var(1), $var(0)]), $rel('=', [$var(2), $var(0)])))))), GOAL, MONO0, GOAL0),  !,
  apply_c(MONO0, TERM_A, GOAL0, MONO1, GOAL1), !,
  apply_c(MONO1, TERM_B, GOAL1, MONO2, GOAL2), !,
  apply_c(MONO2, TERM_C, GOAL2, MONO3, GOAL3), !,
  apply_b(MONO3, GOAL3, MONO4, MONO5, GOAL4, GOAL5), !,
  mate(IPF0, MONO4, GOAL4), !,
  apply_b(MONO5, GOAL5, MONO6, MONO7, GOAL6, GOAL7), !,
  mate(IPF1, MONO6, GOAL6), !,
  mate(INF, MONO7, GOAL7), !.

terms_size([], 0).
terms_size([TERM | TERMS], SIZE) :- 
  term_size(TERM, SIZE_A), 
  terms_size(TERMS, SIZE_B), 
  SIZE is SIZE_A + SIZE_B.

term_size(VAR, 1) :- var(VAR), !.
term_size($fun(_, TERMS), SIZE) :- !,
  terms_size(TERMS, TEMP), 
  num_succ(TEMP, SIZE).
term_size(_, 1).

orient_equation($rel('=', [TERM_A, TERM_B]), $rel('=', [TERM_L, TERM_R])) :- 
  term_size(TERM_A, SIZE_A),
  term_size(TERM_B, SIZE_B), !,
  (
    SIZE_A < SIZE_B ->
    (
      TERM_L = TERM_B,
      TERM_R = TERM_A
    ;
      TERM_L = TERM_A,
      TERM_R = TERM_B
    )
  ;
    (
      TERM_L = TERM_A,
      TERM_R = TERM_B
    ;
      TERM_L = TERM_B,
      TERM_R = TERM_A
    )
  ).

orient_atom($rel(REL, TERMS), $rel(REL, TERMS)).
orient_atom($rel('=', [TERM_A, TERM_B]), $rel('=', [TERM_B, TERM_A])).

orient_literal(ATOM_I, ATOM_O) :- orient_atom(ATOM_I, ATOM_O).
orient_literal($not(ATOM_I), $not(ATOM_O)) :- orient_atom(ATOM_I, ATOM_O).

orient_hyp(HYP, GOAL, HYP, GOAL).
orient_hyp(HYP_I, GOAL_I, HYP_O, GOAL_O) :- 
  HYP_I = (_, $rel('=', [LHS, RHS])), 
  apply_s($rel('=', [RHS, LHS]), GOAL_I, HYP_T, HYP_O, GOAL_T, GOAL_O), 
  eq_symm(HYP_I, HYP_T, GOAL_T), !. 

use_pf((ID, $false), GOAL) :- 
  apply_t($not($false), GOAL, CMP, TEMP),
  apply_x((ID, $false), CMP, TEMP).

use_nt(HYP, GOAL) :- 
  HYP = (_, $not($true)),
  apply_t($true, GOAL, CMP, GOAL_N),
  apply_x(CMP, HYP, GOAL_N).

use_falsehood(HYP, GOAL) :- 
  use_pf(HYP, GOAL) ; 
  use_nt(HYP, GOAL).

use_contra(HYP, GOAL) :- 
  use_falsehood(HYP, GOAL) ;
  (
    apply_n(HYP, GOAL, HYP_N, GOAL_N) ;
    apply_a(HYP, l, GOAL, HYP_N, GOAL_N) ; 
    apply_a(HYP, r, GOAL, HYP_N, GOAL_N) 
  ),
  use_contra(HYP_N, GOAL_N) ;
  apply_b(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  use_contra(HYP_L, GOAL_L),
  use_contra(HYP_R, GOAL_R).

truth($true).
truth($not($false)).
falsehood($false).
falsehood($not($true)).

mate(HYP_A, HYP_B, GOAL) :- 
  mate_pn(HYP_A, HYP_B, GOAL) ;
  mate_pn(HYP_B, HYP_A, GOAL).
 
mate_pn(PYP, NYP, GOAL) :- 
  orient_hyp(PYP, GOAL, PYP_N, GOAL_N), 
  apply_x(PYP_N, NYP, GOAL_N).



%%%%%%%% GET %%%%%%%%

get_list(STRM, GTR, LIST) :- 
  get_char(STRM, CH), !,
  get_list(STRM, GTR, CH, LIST), !.

get_list(_, _, '.', []) :- !.
get_list(STRM, GTR, ',', [ELEM | LIST]) :- 
  call(GTR, STRM, ELEM), !,
  get_list(STRM, GTR, LIST), !.

get_until_dollar(STRM, BYTES) :- 
  get_byte(STRM, BYTE), !,
  get_until_dollar(STRM, BYTE, BYTES), !.

get_until_dollar(_, 37, []) :- !.
get_until_dollar(STRM, BYTE, [BYTE | BYTES]) :- 
  get_until_dollar(STRM, BYTES), !.
  
get_string(STRM, STR) :- 
  get_until_dollar(STRM, BYTES), 
  string_codes(STR, BYTES).

get_atom(STRM, ATOM) :- 
  get_string(STRM, STR),
  atom_string(ATOM, STR).

get_role(STRM, ROLE) :- 
  get_char(STRM, CH),
  (
    CH = 'A', ROLE = axiom ;
    CH = 'P', ROLE = plain
  ).

get_annot(STRM, ANNOT) :-
  get_char(STRM, CH),
  get_annot(STRM, CH, ANNOT).
get_annot(STRM, '1', some(GT)) :- get_gt(STRM, GT). 
get_annot(_, '0', none).

get_af(STRM, (NAME, ROLE, FORM, ANNOT)) :- 
  get_name(STRM, NAME), 
  get_role(STRM, ROLE), 
  get_form(STRM, FORM), 
  get_annot(STRM, ANNOT).

get_gt(STRM, ANNOT) :- 
  get_char(STRM, CH),
  get_gt(STRM, CH, ANNOT).
get_gt(STRM, '^', ANNOT) :-
  get_atom(STRM, FUN),
  get_gts(STRM, GTS), 
  ANNOT =.. [FUN | GTS].
get_gt(STRM, ';', ANNOT) :- get_gts(STRM, ANNOT). 

get_num(STRM, NUM) :- 
  get_string(STRM, STR),
  number_string(NUM, STR).

get_dir(STRM, DIR) :- 
  get_char(STRM, CH),
  (
    CH = '<' -> DIR = l ;
    CH = '>' -> DIR = r
  ).

get_term(STRM, TERM) :-
  get_char(STRM, CH), 
  get_term(STRM, CH, TERM).

get_term(STRM, '#', $var(NUM)) :- get_num(STRM, NUM).
get_term(STRM, '"', $dst(STR)) :- get_string(STRM, STR).
get_term(STRM, '^', $fun(FUN, TERMS)) :- 
  get_functor(STRM, FUN), 
  get_terms(STRM, TERMS).

get_terms(STRM, TERMS) :- get_list(STRM, get_term, TERMS).

get_gts(STRM, GTS) :- get_list(STRM, get_gt, GTS).

get_form(STRM, FORM) :-
  get_char(STRM, CH), 
  get_form_aux(STRM, CH, FORM).

get_functor(STRM, FTR) :- 
  get_char(STRM, CH), 
  get_functor(STRM, CH, FTR).

get_functor(STRM, '@', $par(NUM)) :- get_num(STRM, NUM).
get_functor(STRM, '\'', ATOM) :- get_atom(STRM, ATOM).

get_form_aux(_, 'T', $true).
get_form_aux(_, 'F', $false).

get_form_aux(STRM, '^', $rel(REL, TERMS)) :- 
  get_functor(STRM, REL), 
  get_terms(STRM, TERMS).

get_form_aux(STRM, CH, FORM) :- 
  char_uct(CH, UCT), 
  get_form(STRM, SUB), 
  apply_uop(UCT, SUB, FORM).

get_form_aux(STRM, CH, FORM) :- 
  char_bct(CH, BCT), 
  get_form(STRM, SUB_A), 
  get_form(STRM, SUB_B), 
  apply_bop(BCT, SUB_A, SUB_B, FORM).

get_name(STRM, ID) :- 
  get_char(STRM, CH), !, 
  get_name(STRM, CH, ID).
get_name(STRM, '#', NUM) :- 
  get_num(STRM, NUM).
get_name(STRM, '\'', ATOM) :- 
  get_atom(STRM, ATOM).
  
get_prf(STRM, PRF) :- 
  get_char(STRM, CH), !, 
  get_prf(STRM, CH, PRF).

get_prf(STRM, 'A', a(PID, DIR, SUB)) :- 
  get_num(STRM, PID),  
  get_dir(STRM, DIR),
  get_prf(STRM, SUB).  
  
get_prf(STRM, 'B', b(PID, SUB_L, SUB_R)) :- 
  get_num(STRM, PID), 
  get_prf(STRM, SUB_L), 
  get_prf(STRM, SUB_R).

get_prf(STRM, 'C', c(PID, TERM, SUB)) :- 
  get_num(STRM, PID), 
  get_term(STRM, TERM), 
  get_prf(STRM, SUB).
  
get_prf(STRM, 'D', d(PID, SUB)) :- 
  get_num(STRM, PID), 
  get_prf(STRM, SUB).

get_prf(STRM, 'S', s(FORM, SUB_L, SUB_R)) :-
  get_form(STRM, FORM), 
  get_prf(STRM, SUB_L), 
  get_prf(STRM, SUB_R). 

get_prf(STRM, 'H', h(NAME, SUB)) :- 
  get_name(STRM, NAME), 
  get_prf(STRM, SUB). 

get_prf(STRM, 'N', n(PID, SUB)) :- 
  get_num(STRM, PID), 
  get_prf(STRM, SUB). 

get_prf(STRM, 'T', t(FORM, SUB)) :- 
  get_form(STRM, FORM), 
  get_prf(STRM, SUB). 
  
get_prf(STRM, 'X', x(PID, NID)) :- 
  get_num(STRM, PID), 
  get_num(STRM, NID).

repeat(_, 0, []) :- !.
repeat(ELEM, NUM, [ELEM | LIST]) :-
  num_pred(NUM, PRED),
  repeat(ELEM, PRED, LIST).

hyphens(NUM, STR) :- 
  repeat("-", NUM, STRS), 
  strings_concat(STRS, STR).

offset(0, "").
offset(NUM, STR) :- 
  TOT_LTH is NUM * 2,
  number_string(NUM, NUM_STR),
  string_length(NUM_STR, NUM_LTH),
  PAD_LTH is TOT_LTH - NUM_LTH,
  (
    PAD_LTH < 1 -> 
    hyphens(TOT_LTH, STR)
  ;
    hyphens(PAD_LTH, PAD_STR),
    string_concat(NUM_STR, PAD_STR, STR)
  ).


  





% offset(_, 0) :- !.

% offset(_, 0) :- !.
% offset(OFS, OFS_STR) :- 
%   num_pred(OFS, PRED),
%   write(STRM, ' '),
%   offset(STRM, PRED).

% write_offset(STRM, OFS, TERM) :- 
%   offset(OFS, OFS_STR),
%   write(STRM, TERM).
  
show_prf(STRM, OFS, a(PID, DIR, PRF)) :- 
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  atomic_list_concat(['A', PID, DIR], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF).  

show_prf(STRM, OFS, b(PID, PRF_A, PRF_B)) :- 
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  atomic_list_concat(['B', PID], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF_A),   
  show_prf(STRM, NEW, PRF_B).

show_prf(STRM, OFS, c(PID, TERM, PRF)) :- 
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  term_to_atom(TERM, TERM_ATOM),
  atomic_list_concat(['C', PID, TERM_ATOM], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF).   
  
show_prf(STRM, OFS, d(PID, PRF)) :- 
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  atomic_list_concat(['D', PID], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF).   

show_prf(STRM, OFS, s(FORM, PRF_A, PRF_B)) :-
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  term_to_atom(FORM, FORM_ATOM),
  atomic_list_concat(['S', FORM_ATOM], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF_A), 
  show_prf(STRM, NEW, PRF_B), !.   

show_prf(STRM, OFS, h(NAME, PRF)) :- 
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  atomic_list_concat(['H', NAME], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF), !. 

show_prf(STRM, 'N', n(PID, PRF)) :- 
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  atomic_list_concat(['N', PID], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF), !. 

show_prf(STRM, OFS, t(FORM, PRF)) :- 
  num_succ(OFS, NEW), 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  term_to_atom(FORM, FORM_ATOM),
  atomic_list_concat(['T', FORM_ATOM], ', ', STR),
  writeln(STRM, STR), 
  show_prf(STRM, NEW, PRF), !. 
  
show_prf(STRM, OFS, x(PID, NID)) :- 
  offset(OFS, OFS_STR), write(STRM, OFS_STR), 
  atomic_list_concat(['X', PID, NID], ', ', STR),
  writeln(STRM, STR). 

show_prf(PRF) :- 
  open('showprf.txt', write, STRM),
  show_prf(STRM, 0, PRF).
  

%%%%%%%%%%%%%%%% PROPOSITIONAL CONNECTION TABLEAUX %%%%%%%%%%%%%%%%

startable_hyp(MODE, (_, FORM)) :- 
  startable_form(MODE, FORM).

startable_form(_, FORM) :- falsehood(FORM), !.
startable_form(MODE, FORM) :- break_n(FORM, SUB), !, startable_form(MODE, SUB). 
startable_form(MODE, FORM) :- 
  break_a(l, FORM, FORM_A), !, 
  break_a(r, FORM, FORM_B), !, 
  (startable_form(MODE, FORM_A) ; startable_form(MODE, FORM_B)).
startable_form(MODE, FORM) :- 
  break_b(FORM, FORM_A, FORM_B), !, 
  startable_form(MODE, FORM_A), 
  startable_form(MODE, FORM_B). 
startable_form(q, FORM) :- break_c(_, FORM, SUB), !, startable_form(q, SUB).
startable_form(_, FORM) :- FORM \= $not(_).
  
exists_on_path(HYP, PATH) :- 
  hyp_form(HYP, LIT),
  orient_literal(LIT, LIT_A),
  member((_, LIT_B), PATH), 
  LIT_A == LIT_B.

pblx(PQ, HYPS, GOAL) :- 
  pluck(HYPS, HYP, REST), 
  pblx((start, PQ), REST, [], HYP, GOAL).

pblx(MODE, HYPS, PATH, HYP, GOAL) :- 
  apply_n(HYP, GOAL, HYP_N, GOAL_N), !, 
  pblx(MODE, HYPS, PATH, HYP_N, GOAL_N).
  
pblx((PHASE, q), HYPS, PATH, HYP, GOAL) :- 
  apply_c(HYP, _, GOAL, HYP_N, GOAL_N), !, 
  pblx((PHASE, q), HYPS, PATH, HYP_N, GOAL_N).

pblx(MODE, HYPS, PATH, HYP, GOAL) :- 
  apply_aa(HYP, GOAL, HYP_L, HYP_R, GOAL_N), !, 
  (
    pblx(MODE, [HYP_R | HYPS], PATH, HYP_L, GOAL_N) ;
    pblx(MODE, [HYP_L | HYPS], PATH, HYP_R, GOAL_N)
  ).

pblx((start, PQ), HYPS, PATH, HYP, GOAL) :- 
  apply_sb_lem(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  startable_hyp(PQ, HYP_R),
  pblx((start, PQ), HYPS, PATH, HYP_L, GOAL_L),
  pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R).

pblx((match, PQ), HYPS, PATH, HYP, GOAL) :- 
  apply_sb_lem(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  (
    pblx((match, PQ), HYPS, PATH, HYP_L, GOAL_L),
    pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R)
  ;
    pblx((match, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R),
    pblx((block, PQ), HYPS, PATH, HYP_L, GOAL_L)
  ).
  
pblx((block, PQ), HYPS, PATH, HYP, GOAL) :- 
  apply_sb_lem(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  pblx((block, PQ), HYPS, PATH, HYP_L, GOAL_L),
  pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R).

pblx((start, _), _, _, HYP, GOAL) :-
  use_contra(HYP, GOAL).

pblx((start, PQ), HYPS, PATH, HYP, GOAL) :-
  hyp_form(HYP, FORM), 
  FORM \= $not(_),
  pblx((block, PQ), HYPS, PATH, HYP, GOAL).

pblx((match, _), _, [CMP | _], HYP, GOAL) :- 
  mate(HYP, CMP, GOAL).
  
pblx((block, _), _, _, HYP, GOAL) :-
  use_contra(HYP, GOAL).

pblx((block, _), _, PATH, HYP, GOAL) :- 
  member(CMP, PATH),
  mate(HYP, CMP, GOAL).

pblx((block, PQ), HYPS, PATH, HYP, GOAL) :- 
  \+ exists_on_path(HYP, PATH),
  pluck(HYPS, HYP_N, REST), 
  pblx((match, PQ), REST, [HYP | PATH], HYP_N, GOAL). 

iff_conv_pos_aux(TRP) :- 
  para_ba_swap(TRP, TRP_A, TRP_B), 
  mate(TRP_B),
  para__n(TRP_A, TRP_C), 
  mate(TRP_C). 

iff_conv_neg_aux(TRP) :- 
  para__b(TRP, TRP_2, TRP_1),
  para_a_(l, TRP_1, TRP_1A), 

  (D1 = l, D2 = r ; D1 = r, D2 = l),

  para__a(D1, TRP_1A, TRP_1B), 
  mate(TRP_1B),
  para_a_(r, TRP_2, TRP_2A), 
  para__a(D2, TRP_2A, TRP_2B), 
  para__n(TRP_2B, TRP_2C), 
  mate(TRP_2C).

iff_conv(TRP_I, TRP_O) :- 
  trp_prem(TRP_I, PREM), 
  hyp_form(PREM, $not($iff(FORM_A, FORM_B))),
  (
    para_s_($and($or($not(FORM_A), $not(FORM_B)), $or(FORM_A, FORM_B)), TRP_I, TRP_T, TRP_O) ;
    para_s_($and($or($not(FORM_B), $not(FORM_A)), $or(FORM_B, FORM_A)), TRP_I, TRP_T, TRP_O)
  ), 
  para_b_(TRP_T, TRP_A, TRP_B),
  iff_conv_neg_aux(TRP_A),
  iff_conv_neg_aux(TRP_B).

iff_conv(TRP_I, TRP_O) :- 
  trp_prem(TRP_I, PREM), 
  hyp_form(PREM, $iff(FORM_A, FORM_B)),
  para_s_($and($or(FORM_A, $not(FORM_B)), $or(FORM_B, $not(FORM_A))), TRP_I, TRP_T, TRP_O), 
  para_ab_swap(TRP_T, TRP_A, TRP_B), 
  iff_conv_pos_aux(TRP_A), 
  iff_conv_pos_aux(TRP_B). 

e_iff_conv((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  hyp_form(HYP_A, $not($iff(FORM_A, FORM_B))),
  FORM = $and($or($not(FORM_A), $not(FORM_B)), $or(FORM_A, FORM_B)),
  apply_s(FORM, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N),
  pblx(p, [HYP_A, HYP_T], GOAL_T).



%%%%%%%%%%%%%%%% PARALLEL DECOMPOSITION PREDICATES %%%%%%%%%%%%%%%%
  
para_a_(DIR, (HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  apply_a(HYP_A, DIR, GOAL, HYP_AN, GOAL_N). 
  
para__a(DIR, (HYP_A, HYP_B, GOAL), (HYP_A, HYP_NB, GOAL_N)) :- 
  apply_a(HYP_B, DIR, GOAL, HYP_NB, GOAL_N). 

para_b_((HYP_A, HYP_B, GOAL), (HYP_L, HYP_B, GOAL_L), (HYP_R, HYP_B, GOAL_R)) :- 
  apply_b(HYP_A, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R). 

para__b((HYP_A, HYP_B, GOAL), (HYP_A, HYP_L, GOAL_L), (HYP_A, HYP_R, GOAL_R)) :- 
  apply_b(HYP_B, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R). 

para_c_(TERM, (HYP_A, HYP_B, GOAL_I), (HYP_NA, HYP_B, GOAL_O)) :- apply_c(HYP_A, TERM, GOAL_I, HYP_NA, GOAL_O).
para__c(TERM, (HYP_A, HYP_B, GOAL_I), (HYP_A, HYP_NB, GOAL_O)) :- apply_c(HYP_B, TERM, GOAL_I, HYP_NB, GOAL_O).

para_c_(TRP_I, TRP_O) :- para_c_(_, TRP_I, TRP_O).

para__c(TRP_I, TRP_O) :- para__c(_, TRP_I, TRP_O).

para__d((HYP_A, HYP_B, GOAL_I), (HYP_A, HYP_NB, GOAL_O)) :- 
  apply_d(HYP_B, GOAL_I, HYP_NB, GOAL_O).

para_d_((HYP_A, HYP_B, GOAL_I), (HYP_NA, HYP_B, GOAL_O)) :- 
  apply_d(HYP_A, GOAL_I, HYP_NA, GOAL_O).

parad(TRP_I, TRP_O) :- 
  para_d_(TRP_I, TRP_O) ;
  para__d(TRP_I, TRP_O).

mate((HYP_A, HYP_B, GOAL)) :- mate(HYP_A, HYP_B, GOAL).

para_mate((HYP_A, HYP_B, GOAL)) :- mate(HYP_A, HYP_B, GOAL).

para_n_((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  apply_n(HYP_A, GOAL, HYP_AN, GOAL_N). 
  
para__n((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  apply_n(HYP_B, GOAL, HYP_BN, GOAL_N). 

paran(X, Y) :- para_n_(X, Y) ; para__n(X, Y).

paracd(X, Y) :- para_cd(X, Y) ; para_dc(X, Y).

para_cd((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  apply_cd(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N).

para_dc((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  apply_cd(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).

paraab(X, Y, Z) :- para_ab(X, Y, Z) ; para_ba(X, Y, Z).

para_ab((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  apply_ab(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R).

para_ba((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  apply_ab(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

para(H2G) :-
  para_mate(H2G) -> true ;
  paran(H2G, H2G_N) -> para(H2G_N) ;
  paracd(H2G, H2G_N) -> para(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R) ->
  para(H2G_L), !, 
  para(H2G_R).

para_falsehood((HYP_A, HYP_B, GOAL)) :- 
  use_falsehood(HYP_A, GOAL) ; use_falsehood(HYP_B, GOAL).

para_mlc(X) :- para_mate(X) ; para_falsehood(X).



%%%%%%%%%%%%%%%% PARALLEL CHOICE DECOMPOSITION %%%%%%%%%%%%%%%%

para_s_(FORM, (PREM, CONC, GOAL), (PREM, HYP_N, GOAL_N), (HYP_P, CONC, GOAL_P)) :- 
  apply_s(FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P).

paraab_choice(TRP, TRP_B, TRP_A) :- 
  paraab(TRP, TRP_B, TRP_A) ;
  paraab_swap(TRP, TRP_B, TRP_A).

paraab_swap(TRP, TRP_B, TRP_A) :- 
  para_ab_swap(TRP, TRP_B, TRP_A) ;
  para_ba_swap(TRP, TRP_B, TRP_A).
  
para_ab_swap((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  apply_ab_rev(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R).

para_ba_swap((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  apply_ab_rev(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

para_choice(H2G) :- 
  para_mate(H2G) -> true ;
  paran(H2G, H2G_N) -> para_choice(H2G_N) ;
  paracd(H2G, H2G_N) -> para_choice(H2G_N) ;
  paraab_choice(H2G, H2G_L, H2G_R),
  para_choice(H2G_L),  
  para_choice(H2G_R).




%%%%%%%%%%%%%%%% PARALLEL SIMP DECOMPOSITION %%%%%%%%%%%%%%%%

para_simp_v((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  (
    apply_b(HYP_A, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N) ;
    apply_b(HYP_A, GOAL, HYP_N, HYP_T, GOAL_N, GOAL_T) 
  ),
  use_contra(HYP_T, GOAL_T).

para_simp_v((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  pluck([l, r], DIR, [FLP]), 
  hyp_form(HYP_A, FORM), 
  break_a(DIR, FORM, FORM_T), 
  tautology(FORM_T), 
  apply_a(HYP_A, FLP, GOAL, HYP_N, GOAL_N). 

para_simp(_, H2G) :- para_mate(H2G), !.
para_simp(_, TRP) :- para_falsehood(TRP), !.
para_simp(SLVR, H2G) :- para_n_(H2G, H2G_N), !, para_simp(SLVR, H2G_N).
para_simp(v, H2G) :- paracd(H2G, H2G_N), !, para_simp(v, H2G_N).
para_simp(v, H2G) :- para_simp_v(H2G, H2G_N), !, para_simp(v, H2G_N).
para_simp(v, H2G) :- 
  paraab_choice(H2G, H2G_L, H2G_R),
  para_simp(v, H2G_L),  
  para_simp(v, H2G_R).

para_simp(e, H2G) :- 
  H2G = (PREM, _, GOAL),
  hyp_form(PREM, FORM),
  break_a(l, FORM, FORM_A), !,
  break_a(r, FORM, FORM_B), 
  bool_simp(FORM_A, NORM_A),
  bool_simp(FORM_B, NORM_B),
  (
    (truth(NORM_A) ; NORM_A == NORM_B) -> 
    para_a_(r, H2G, H2G_N),
    para_simp(e, H2G_N)
  ;
    truth(NORM_B) -> 
    para_a_(l, H2G, H2G_N),
    para_simp(e, H2G_N)
  ;
    complements(NORM_A, NORM_B) -> 
    apply_aa(PREM, GOAL, HYP_A, HYP_B, GOAL_AA),
    apply_s(NORM_A, GOAL_AA, HYP_NA, HYP_PA, GOAL_NA, GOAL_PA), 
    para_simp(e, (HYP_A, HYP_NA, GOAL_NA)), 
    apply_s(NORM_B, GOAL_PA, HYP_NB, HYP_PB, GOAL_NB, GOAL_PB), 
    para_simp(e, (HYP_B, HYP_NB, GOAL_NB)), 
    mate(HYP_PA, HYP_PB, GOAL_PB), !
  ;
    para_ab(H2G, TRP_A, TRP_B),
    para_simp(e, TRP_A), !, 
    para_simp(e, TRP_B)
  ).

para_simp(e, TRP) :- 
  TRP = ((_, FORM), _, _),
  break_b(FORM, FORM_A, FORM_B), !,
  bool_simp(FORM_A, NORM_A),
  bool_simp(FORM_B, NORM_B),
  (
    falsehood(NORM_A) ->  
    para_b_(TRP, (PREM, _, GOAL), TRP_N),
    pblx(p, [PREM], GOAL),
    para_simp(e, TRP_N)
  ;
    falsehood(NORM_B) ->  
    para_b_(TRP, TRP_N, (PREM, _, GOAL)),
    pblx(p, [PREM], GOAL),
    para_simp(e, TRP_N)
  ;
    NORM_A == NORM_B -> 
    para_s_(NORM_A, TRP, TRP_N, TRP_P), 
    para_b_(TRP_N, TRP_A, TRP_B), 
    para_simp(e, TRP_A), !,
    para_simp(e, TRP_B), !,
    para_simp(e, TRP_P)
  ;
    para_ba(TRP, TRP_A, TRP_B),
    para_simp(e, TRP_A), !, 
    para_simp(e, TRP_B)
  ).

para_simp(e, TRP) :- 
  TRP = (PREM, _, GOAL),
  PREM = (_, FORM),
  break_c(_, FORM, SUB), !,
  bool_simp(SUB, NORM),
  (
    falsehood(NORM) -> 
    pblx(p, [PREM], GOAL)
  ;
    para_cd(TRP, TRP_N), 
    para_simp(e, TRP_N)
  ).

para_simp(e, TRP) :- 
  TRP = (PREM, _, GOAL),
  PREM = (_, FORM),
  GOAL = (_, CNT),
  break_d(CNT, FORM, SUB), !,
  bool_simp(SUB, NORM),
  (
    falsehood(NORM) -> 
    pblx(p, [PREM], GOAL)
  ;
    para_dc(TRP, TRP_N), 
    para_simp(e, TRP_N)
  ).

para_vac_cd((HYP_A, HYP_B, GOAL_I), (HYP_NA, HYP_B, GOAL_O)) :- 
  apply_c_vac(HYP_A, GOAL_I, HYP_NA, GOAL_O) ;
  dp_vac(HYP_A, GOAL_I, HYP_NA, GOAL_O).

para_vac_cd((HYP_A, HYP_B, GOAL_I), (HYP_A, HYP_NB, GOAL_O)) :- 
  apply_c_vac(HYP_B, GOAL_I, HYP_NB, GOAL_O) ;
  dp_vac(HYP_B, GOAL_I, HYP_NB, GOAL_O).

para_vac(H2G) :- 
  para_mate(H2G) *-> true ;
  paran(H2G, H2G_N) -> para_vac(H2G_N) ;
  para_vac_cd(H2G, H2G_N) -> para_vac(H2G_N) ;
  paracd(H2G, H2G_N) -> para_vac(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R), !,
  para_vac(H2G_L), !, 
  para_vac(H2G_R).

para_cd_lax((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  apply_cd_lax(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N) ;
  apply_cd_lax(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).

para_lax(H2G) :- 
  para_mate(H2G) *-> true ;
  paran(H2G, H2G_N) -> para_lax(H2G_N) ;
  para_cd_lax(H2G, H2G_N) -> para_lax(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R), !,
  para_lax(H2G_L), !, 
  para_lax(H2G_R).

ppr(H2G) :- 
  para_mate(H2G) -> true ;
  paran(H2G, H2G_N) -> ppr(H2G_N) ;
  paracd(H2G, H2G_N) -> ppr(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R), 
  ppr(H2G_L), 
  ppr(H2G_R)
;
  ppr_a(H2G, H2G_N),
  ppr(H2G_N).



%%%%%%%%%%%%%%%% NEGATION NORMALIZATION %%%%%%%%%%%%%%%%

a_para((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  apply_a(HYP_A, l, GOAL, HYP_AN, GOAL_N) ;
  apply_a(HYP_A, r, GOAL, HYP_AN, GOAL_N).
  
ppr_a((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  apply_a(HYP_A, l, GOAL, HYP_AN, GOAL_N) ;
  apply_a(HYP_A, r, GOAL, HYP_AN, GOAL_N).

ppr_a((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  apply_a(HYP_B, l, GOAL, HYP_BN, GOAL_N) ;
  apply_a(HYP_B, r, GOAL, HYP_BN, GOAL_N).

fnnf(H2G) :- 
  para_mate(H2G) -> true ;
  paran(H2G, H2G_N) -> fnnf(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R) -> fnnf(H2G_L), !, fnnf(H2G_R) ;
  paracd(H2G, H2G_N) -> fnnf(H2G_N) ;
  H2G = (PREM, CONC, GOAL), 
  (
    type_hyp(c, PREM),
    apply_b(CONC, GOAL, CONC_L, CONC_R, GOAL_L, GOAL_R), 
    fnnf((PREM, CONC_L, GOAL_L)),
    fnnf((PREM, CONC_R, GOAL_R))
  ;
    imp_hyp(PREM),
    ppr_a(H2G, H2G_N),
    fnnf(H2G_N)
  ;  
    e_iff_conv(H2G, H2G_N), 
    fnnf(H2G_N)
  ).

vnnf(H2G) :- 
  para_mate(H2G) -> true ;
  paran(H2G, H2G_N) -> vnnf(H2G_N) 
;
  paracd(H2G, H2G_N) -> vnnf(H2G_N) 
;
  iff_conv(H2G, H2G_N) *-> vnnf(H2G_N) 
;
  paraab(H2G, TRP_A, TRP_B), 
  vnnf(TRP_A), !,
  vnnf(TRP_B)
;
  ppr_a(H2G, H2G_N),
  vnnf(H2G_N). 



%%%%%%%%%%%%%%%% PARALLEL CLAUSAL DECOMPOSITION %%%%%%%%%%%%%%%%

imp_hyp(HYP) :- 
  hyp_form(HYP, FORM),
  member(FORM, [$imp(_, _), $iff(_, _)]).

ap_rop_aux(HYP, GOAL, HYP_L, HYP_R, NEW_GOAL) :- 
  \+ imp_hyp(HYP), 
  apply_a(HYP, l, GOAL, HYP_L, TEMP_GOAL),
  apply_a(HYP, r, TEMP_GOAL, HYP_R, NEW_GOAL).

ap_rop(HYP, GOAL, HYPS, GOAL_N) :- 
  ap_rop_aux(HYP, GOAL, HYP_L, HYP_R, GOAL0) -> 
  (
    ap_rop(HYP_L, GOAL0, HYPS_L, GOAL1),
    ap_rop(HYP_R, GOAL1, HYPS_R, GOAL_N), 
    append(HYPS_L, HYPS_R, HYPS)
  ) ;
  (HYPS = [HYP], GOAL_N = GOAL).

bp_rop(HYP, GOAL, HGS) :- 
  (
    \+ imp_hyp(HYP),
    apply_b(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R)
  ) -> 
  (
    bp_rop(HYP_L, GOAL_L, HGS_L),
    bp_rop(HYP_R, GOAL_R, HGS_R),
    append(HGS_L, HGS_R, HGS)
  ) ;
  HGS = [([HYP], GOAL)].

/*
cp_rop([], GOAL, [], GOAL).
cp_rop([HYP_I | HYPS_I], GOAL_I, [HYP_O | HYPS_O], GOAL_O) :- 
  many_nb([c], [HYP_I], GOAL_I, [HYP_O], GOAL_T),
  cp_rop(HYPS_I, GOAL_T, HYPS_O, GOAL_O).
*/

para_clausal_two((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  (imp_hyp(HYP_A) ; imp_hyp(HYP_B)),
  (
    apply_ab(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ;
    apply_ab(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R) 
  ).

para_clausal_many((HYP_A, HYP_B, GOAL), HYPS, HGS) :- 
  \+ imp_hyp(HYP_A),
  \+ imp_hyp(HYP_B),
  (
    type_hyp(a, HYP_A),
    ap_rop(HYP_A, GOAL, HYPS, GOAL_T), 
    bp_rop(HYP_B, GOAL_T, HGS)
  ;
    type_hyp(a, HYP_B),
    ap_rop(HYP_B, GOAL, HYPS, GOAL_T), 
    bp_rop(HYP_A, GOAL_T, HGS)
  ).

ppr(PREM, CONC, GOAL) :- 
  ap_rop(PREM, GOAL, PREMS, TEMP), 
  bp_rop(CONC, TEMP, HGS), 
  ppr(PREMS, HGS).

ppr(_, []) :- !. 

ppr([PREM | PREMS], [([CONC], GOAL) | HGS]) :- 
  mate(PREM, CONC, GOAL) -> 
  ppr(PREMS, HGS) 
;
  ppr(PREMS, [([CONC], GOAL) | HGS]).
  
para_clausal(H2G) :- 
  para_falsehood(H2G) -> true ;
  para_mate(H2G) 
;
  paran(H2G, H2G_N)  -> para_clausal(H2G_N) ;
  paracd(H2G, H2G_N) -> para_clausal(H2G_N) ;
  para_clausal_two(H2G, H2G_L, H2G_R) -> 
  para_clausal(H2G_L), 
  para_clausal(H2G_R)
;
  para_clausal_many(H2G, HS, HGS) -> 
  para_clausal_aux(HS, HGS).

para_clausal_aux(_, []).
para_clausal_aux(HYPS, [([HYP], GOAL) | HGS]) :- 
  member(CMP, HYPS), 
  para_clausal((HYP, CMP, GOAL)),
  para_clausal_aux(HYPS, HGS).

path_filenames(Dir, Entries) :- 
  directory_files(Dir, TempA), 
  delete(TempA, '.', TempB),
  delete(TempB, '..', Entries).

rec_path_files(Path, [Path]) :- 
  exists_file(Path). 

rec_path_files(Path, Files) :- 
  exists_directory(Path), 
  rec_path_filenames(Path, Files).

rec_path_filenames(Dir, Files) :- 
  path_filenames(Dir, Entries), 
  maplist(directory_file_path(Dir), Entries, Paths),
  maplist(rec_path_files, Paths, Filess),
  append(Filess, Files).

cla_lits($false, []) :- !.
cla_lits(CLA, LITS) :- cla_lits(CLA, LITS, []).

cla_lits($or(FORM_L, FORM_R), LITS, TAIL) :- !, 
  cla_lits(FORM_L, LITS, TEMP), 
  cla_lits(FORM_R, TEMP, TAIL).

cla_lits(LIT, [LIT | TAIL], TAIL) :- literal(LIT).

trace_if_debug(OPTS) :-
  member('-debug', OPTS) ->
  write("Begin tracing.\n\n"),
  guitracer,
  trace 
;
  true.

get_context(PROB, IDS, CTX) :- 
  maplist(prob_id_hyp(PROB), IDS, CTX).

redirect_id(NI, OLD, NEW) :- 
  get_assoc(OLD, NI, NEW).

map_form(_, _, FORM, FORM) :- log_const(FORM), !.

map_form(GOAL, DTH, $not(FORM_I), $not(FORM_O)) :- !,
  map_form(GOAL, DTH, FORM_I, FORM_O).
  
map_form(GOAL, DTH, FORM_I, FORM_O) :- 
  decom_qtf(FORM_I, QTF, SUB_I), !,
  num_succ(DTH, SUCC),
  map_form(GOAL, SUCC, SUB_I, SUB_O), 
  apply_uop(QTF, SUB_O, FORM_O). 

map_form(GOAL, DTH, FORM_I, FORM_O) :- 
  decom_bct(FORM_I, BCT, SUB_AI, SUB_BI), !, 
  map_form(GOAL, DTH, SUB_AI, SUB_AO), 
  map_form(GOAL, DTH, SUB_BI, SUB_BO), 
  apply_bop(BCT, SUB_AO, SUB_BO, FORM_O). 

map_form(GOAL, DTH, $rel(REL, TERMS_I), $rel(REL, TERMS_O)) :- 
  maplist_cut(call(GOAL, DTH), TERMS_I, TERMS_O).

para_e1(H2G) :- 
  para_mate(H2G) -> true ;
  paran(H2G, H2G_N) -> para_e1(H2G_N) ;
  parad(H2G, H2G_N) -> para_e1(H2G_N) ;
  para_clausal_two(H2G, H2G_L, H2G_R) -> para_e1(H2G_L), !, para_e1(H2G_R) ;
  % para_clausal_many(H2G, TRPS) -> maplist_cut(para_e1, TRPS) ;
  para_c_(H2G, H2G_N) -> para_e1(H2G_N) ;
  member(DIR, [l, r]),
  clause_ab(para_e1, DIR, H2G).
  % -> true ; 

clause_ab(PARA, l, (HYP_A, HYP_B, GOAL)) :- clause_ab(PARA, l, HYP_A, HYP_B, GOAL). 
clause_ab(PARA, r, (HYP_A, HYP_B, GOAL)) :- clause_ab(PARA, l, HYP_B, HYP_A, GOAL). 

clause_ab(PARA, DIR, HYP_A, HYP_B, GOAL) :- 
  type_hyp(a, HYP_A),
  ap_rop(HYP_A, GOAL, HYPS, TEMP), 
  clause_ab_aux(PARA, DIR, HYPS, HYP_B, TEMP, []).
  
clause_ab_aux(PARA, DIR, HYPS, HYP, GOAL, REM) :-
  apply_c(HYP, _, GOAL, HYP_N, GOAL_N), !, 
  clause_ab_aux(PARA, DIR, HYPS, HYP_N, GOAL_N, REM).

clause_ab_aux(PARA, l, [HYP_A | HYPS], HYP_B, GOAL, HYPS) :-
  call(PARA, (HYP_A, HYP_B, GOAL)), !. 
  
clause_ab_aux(PARA, r, [HYP_A | HYPS], HYP_B, GOAL, HYPS) :-
  call(PARA, (HYP_B, HYP_A, GOAL)), !. 

clause_ab_aux(PARA, DIR, HYPS, HYP_B, GOAL, REM) :-
  apply_b(HYP_B, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  clause_ab_aux(PARA, DIR, HYPS, HYP_L, GOAL_L, TEMP), !, 
  clause_ab_aux(PARA, DIR, TEMP, HYP_R, GOAL_R, REM).

pick_mate(HYPS_A, (HYPS_B, GOAL)) :- 
  member(HYP_A, HYPS_A), 
  member(HYP_B, HYPS_B), 
  mate(HYP_A, HYP_B, GOAL).

map_signed_atoms(_, []).

map_signed_atoms(HYPS, [([HYP], GOAL) | HGS]) :- 
  use_falsehood(HYP, GOAL) ->
  map_signed_atoms(HYPS, HGS) ;
  ground(HYP) -> 
  (pick_mate(HYPS, ([HYP], GOAL)), !, map_signed_atoms(HYPS, HGS)) ;
  (pick_mate(HYPS, ([HYP], GOAL)),  map_signed_atoms(HYPS, HGS)). 

sbsm(PREM, CONC, GOAL) :-
  rp([a, d, n], [CONC], GOAL, HYPS, TEMP), 
  (
    (member(HYP, HYPS), use_falsehood(HYP, TEMP)) -> 
    true
  ;
    rp([b, c, n], [PREM], TEMP, HGS), 
    map_signed_atoms(HYPS, HGS)
  ).

relabel(SOL_I, SOL_O) :- 
  empty_assoc(EMP),  
  relabel_sol((EMP, EMP), EMP, 0, SOL_I, SOL_O).

relabel_inst(DICT, NI, CNT, add(NAME, FORM), DICT, NI_N, add(NORM)) :-    
  resymb_form(DICT, FORM, NORM),
  put_assoc(NAME, NI, CNT, NI_N).

relabel_inst((RDICT, FDICT), NI, CNT, add([isni, REL, ARI], NAME, FORM), (RDICT_N, FDICT), NI_N, add(NORM)) :-    
  put_assoc(NAME, NI, CNT, NI_N), 
  put_assoc((REL, ARI), RDICT, CNT, RDICT_N),
  resymb_form((RDICT_N, FDICT), FORM, NORM).
  
relabel_inst((RDICT, FDICT), NI, CNT, add([def, REL, ARI], NAME, FORM), (RDICT_N, FDICT), NI_N, add(NORM)) :-    
  put_assoc(NAME, NI, CNT, NI_N), 
  put_assoc((REL, ARI), RDICT, CNT, RDICT_N),
  resymb_form((RDICT_N, FDICT), FORM, NORM).

relabel_inst((RDICT, FDICT), NI, CNT, skm(FUN, ARI, NAME, FORM), (RDICT, FDICT_N), NI_N, add(NORM)) :-    
  put_assoc(NAME, NI, CNT, NI_N), 
  put_assoc((FUN, ARI), FDICT, CNT, FDICT_N),
  resymb_form((RDICT, FDICT_N), FORM, NORM).

relabel_inst(DICT, NI, CNT, inf(HINT, NAMES, NAME, FORM), DICT, NI_N, inf(HINT, IDS, NORM)) :-    
  maplist_cut(redirect_id(NI), NAMES, IDS),
  put_assoc(NAME, NI, CNT, NI_N),
  resymb_form(DICT, FORM, NORM).

relabel_inst(DICT, NI, CNT, orig(NAME, VID, FORM), DICT, NI_N, orig(NAME, NORM)) :-    
  put_assoc(VID, NI, CNT, NI_N),
  resymb_form(DICT, FORM, NORM).

relabel_sol(DICT, NI, CNT, [INST | SOL], [INST_N | SOL_N]) :- 
  relabel_inst(DICT, NI, CNT, INST, DICT_N, NI_N, INST_N),   
  num_succ(CNT, SCNT),
  relabel_sol(DICT_N, NI_N, SCNT, SOL, SOL_N). 

relabel_sol(_, _, _, [], []).

eqr_aux(_, ([HYP], GOAL)) :- use_falsehood(HYP, GOAL), !.
eqr_aux(_, ([HYP], GOAL)) :- 
  HYP = (_, $not($rel('=', [_, _]))),
  eq_refl(HYP, GOAL).
eqr_aux(HYPS, HG) :- pick_mate(HYPS, HG).

eqr(PREM, CONC, GOAL) :- 
  rp([a, d, n], [CONC], GOAL, HYPS, GOAL_T), 
  rp([b, c, n], [PREM], GOAL_T, HGS), !,
  maplist(eqr_aux(HYPS), HGS).

/*
bool_not($false, $true) :- !.
bool_not($true, $false) :- !.
bool_not($not(FORM), FORM) :- !.
bool_not(FORM, $not(FORM)).

bool_or($true, _, $true) :- !.
bool_or(_, $true, $true) :- !.
bool_or($false, FORM, FORM) :- !.
bool_or(FORM, $false, FORM) :- !.
bool_or(FORM_L, FORM_R, $or(FORM_L, FORM_R)).

bool_and($false, _, $false) :- !.
bool_and(_, $false, $false) :- !.
bool_and($true, FORM, FORM) :- !.
bool_and(FORM, $true, FORM) :- !.
bool_and(FORM_L, FORM_R, $and(FORM_L, FORM_R)).

bool_imp($false, _, $true) :- !.
bool_imp(_, $true, $true) :- !.
bool_imp($true, FORM, FORM) :- !.
bool_imp(FORM, $false, $not(FORM)) :- !.
bool_imp(FORM_L, FORM_R, $true) :- FORM_L == FORM_R, !.
bool_imp(FORM_L, FORM_R, $imp(FORM_L, FORM_R)).

bool_norm($not(FORM), NORM) :- !, 
  bool_norm(FORM, TEMP), 
  bool_not(TEMP, NORM). 
 
bool_norm($or(FORM_L, FORM_R), NORM) :- !, 
  bool_norm(FORM_L, NORM_L), 
  bool_norm(FORM_R, NORM_R),
  bool_or(NORM_L, NORM_R, NORM).

bool_norm($and(FORM_L, FORM_R), NORM) :- !, 
  bool_norm(FORM_L, NORM_L), 
  bool_norm(FORM_R, NORM_R),
  bool_and(NORM_L, NORM_R, NORM).

bool_norm($imp(FORM_L, FORM_R), NORM) :- !, 
  bool_norm(FORM_L, NORM_L), 
  bool_norm(FORM_R, NORM_R),
  bool_imp(NORM_L, NORM_R, NORM).

bool_norm(FORM, FORM).
*/

tautology(FORM) :- bool_simp(FORM, $true).
contradiction(FORM) :- bool_simp(FORM, $false).

bool_simp_not($false, $true) :- !.
bool_simp_not($true, $false) :- !.
bool_simp_not($not(FORM), FORM) :- !.
bool_simp_not(FORM, $not(FORM)).

bool_simp_qtf(_, $true, $true) :- !.
bool_simp_qtf(_, $false, $false) :- !.
bool_simp_qtf(QTF, FORM_I, FORM_O) :-
  no_fv_form(0, FORM_I) -> 
  FORM_O = FORM_I 
;
  apply_uop(QTF, FORM_I, FORM_O).

bool_simp_bct(iff, FORM, $true, FORM) :- !.
bool_simp_bct(iff, FORM, $false, $not(FORM)) :- !.
bool_simp_bct(iff, $true, FORM, FORM) :- !.
bool_simp_bct(iff, $false, FORM, $not(FORM)) :- !.
bool_simp_bct(iff, FORM_A, FORM_B, $true) :- FORM_A == FORM_B, !.
bool_simp_bct(iff, FORM_A, FORM_B, $false) :- complements(FORM_A, FORM_B), !.
bool_simp_bct(iff, FORM_A, FORM_B, $iff(FORM_A, FORM_B)). 

bool_simp_bct(imp, $false, _, $true) :- !.
bool_simp_bct(imp, $true, FORM, FORM) :- !.
bool_simp_bct(imp, _, $true, $true) :- !.
bool_simp_bct(imp, FORM, $false, $not(FORM)) :- !.
bool_simp_bct(imp, FORM_A, FORM_B, $true) :- FORM_A == FORM_B, !.
bool_simp_bct(imp, FORM_A, FORM_B, FORM_B) :- complements(FORM_A, FORM_B), !.
bool_simp_bct(imp, FORM_A, FORM_B, $imp(FORM_A, FORM_B)) :- !.

bool_simp_bct(and, $false, _, $false) :- !.
bool_simp_bct(and, _, $false, $false) :- !.
bool_simp_bct(and, $true, FORM, FORM) :- !.
bool_simp_bct(and, FORM, $true, FORM) :- !.
bool_simp_bct(and, FORM_L, FORM_R, FORM_L) :- FORM_L == FORM_R, !.
bool_simp_bct(and, FORM_L, FORM_R, $false) :- complements(FORM_L, FORM_R), !.
bool_simp_bct(and, FORM_L, FORM_R, $and(FORM_L, FORM_R)) :- !.

bool_simp_bct(or, $true, _, $true) :- !.
bool_simp_bct(or, _, $true, $true) :- !.
bool_simp_bct(or, $false, FORM, FORM) :- !.
bool_simp_bct(or, FORM, $false, FORM) :- !.
bool_simp_bct(or, FORM_L, FORM_R, FORM_L) :- FORM_L == FORM_R, !.
bool_simp_bct(or, FORM_L, FORM_R, $true) :- complements(FORM_L, FORM_R), !.
bool_simp_bct(or, FORM_L, FORM_R, $or(FORM_L, FORM_R)) :- !.
 
bool_simp($not(FORM), NORM) :- !, 
  bool_simp(FORM, TEMP), 
  bool_simp_not(TEMP, NORM). 
 
bool_simp(FORM, NORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !,
  bool_simp(FORM_A, NORM_A), 
  bool_simp(FORM_B, NORM_B),
  bool_simp_bct(BCT, NORM_A, NORM_B, NORM).

bool_simp(FORM, NORM) :- 
  decom_qtf(FORM, QTF, BODY), !, 
  bool_simp(BODY, TEMP),
  bool_simp_qtf(QTF, TEMP, NORM).

bool_simp(FORM, FORM).

map_var(GOAL, $var(NUM), TERM) :- !, call(GOAL, NUM, TERM).
map_var(_, $dst(STR), $dst(STR)) :- !.
map_var(GOAL, $fun(FUN, TERMS_I), $fun(FUN, TERMS_O)) :- !, 
  maplist_cut(map_var(GOAL), TERMS_I, TERMS_O).
  
decr_vdx_form(FORM, NORM) :- 
  map_form(decr_vdx_term, 0, FORM, NORM).
decr_vdx_term(DEP, TERM_I, TERM_O) :- 
  map_var(decr_vdx(DEP), TERM_I, TERM_O).

decr_vdx(DTH, NUM, $var(NUM)) :- NUM < DTH.
decr_vdx(DTH, NUM, $var(PRED)) :- 
  DTH < NUM, num_pred(NUM, PRED). 

dist_qtf_bct(fa, and).
dist_qtf_bct(ex, or).

dist_qtf(_, FORM, NORM) :- decr_vdx_form(FORM, NORM), !.

dist_qtf(QTF, FORM, NORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), 
  (
    dist_qtf_bct(QTF, BCT) ; 
    decr_vdx_form(FORM_A, _) ;
    decr_vdx_form(FORM_B, _) 
  ), !, 
  dist_qtf(QTF, FORM_A, NORM_A), 
  dist_qtf(QTF, FORM_B, NORM_B), 
  apply_bop(BCT, NORM_A, NORM_B, NORM).

dist_qtf(QTF, FORM, NORM) :- 
  apply_uop(QTF, FORM, NORM).

push_qtf(FORM, NORM) :- 
  decom_qtf(FORM, QTF, BODY), !,
  push_qtf(BODY, TEMP),
  dist_qtf(QTF, TEMP, NORM).

push_qtf(FORM, NORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !,
  push_qtf(FORM_A, NORM_A),
  push_qtf(FORM_B, NORM_B),
  apply_bop(BCT, NORM_A, NORM_B, NORM).

push_qtf(FORM, FORM).


distribute($fa(FORM), $fa(NORM)) :- !, 
  distribute(FORM, NORM).

distribute($and(FORM_A, FORM_B), $and(NORM_A, NORM_B)) :- !, 
  distribute(FORM_A, NORM_A),
  distribute(FORM_B, NORM_B).

distribute($or(FORM_A, FORM_B), NORM) :- !, 
  distribute(FORM_A, TEMP_A),  
  distribute(FORM_B, TEMP_B),
  (
    TEMP_A = $and(FORM_L, FORM_R) -> 
    distribute($or(FORM_L, TEMP_B), CONJ_L), 
    distribute($or(FORM_R, TEMP_B), CONJ_R), 
    NORM = $and(CONJ_L, CONJ_R)
  ;
    TEMP_B = $and(FORM_L, FORM_R) -> 
    distribute($or(FORM_L, TEMP_A), CONJ_L), 
    distribute($or(FORM_R, TEMP_A), CONJ_R), 
    NORM = $and(CONJ_L, CONJ_R) 
  ;
    NORM = $or(TEMP_A, TEMP_B)
  ).  

distribute(FORM, FORM).

trp_prem((PREM, _, _), PREM).

atom_firstchar(ATOM, CH) :-
  atom_codes(ATOM, [CODE | _]), 
  char_code(CH, CODE).

get_prob(STRM, PROB_I, PROB_O) :- 
  get_char(STRM, CH), 
  get_prob(STRM, CH, PROB_I, PROB_O).
get_prob(STRM, ',', PROB_I, PROB_O) :- 
  get_af(STRM, (NAME, _, FORM, _)), !,
  (
    get_assoc(NAME, PROB_I, _) ->
    throw(duplicate_hypothesis_found)
  ;
    put_assoc(NAME, PROB_I, FORM, PROB_T), !,
    get_prob(STRM, PROB_T, PROB_O), !
  ).
get_prob(_, '.', PROB, PROB). 

get_sol(STRM, SOL) :- get_list(STRM, get_af, SOL).

tptp_prob(TPTP, PROB) :-
  process_create(
    './ttp/target/release/ttp', 
    [TPTP], 
    [stdout(pipe(STRM))]
  ), !,
  (
    set_stream(STRM, encoding(octet)),
    empty_assoc(EMP),
    get_prob(STRM, EMP, PROB)
  ),
  close(STRM).

tptp_sol(TPTP, SOL) :-
  process_create(
    './ttp/target/release/ttp', 
    [TPTP], 
    [stdout(pipe(STRM))]
  ), !,
  (
    set_stream(STRM, encoding(octet)),
    get_sol(STRM, SOL)
  ),
  close(STRM).

any_line_strm(STRM, GOAL) :- 
  read_line_to_string(STRM, LINE), 
  (
    call(GOAL, LINE) 
  ;
    LINE \= end_of_file, 
    any_line_strm(STRM, GOAL)
  ).

any_line_path(PATH, GOAL) :- 
  setup_call_cleanup(
    open(PATH, read, STRM),
    any_line_strm(STRM, GOAL), 
    close(STRM) 
  ).

concat_shell(LIST, EXST) :- 
  atomic_list_concat(LIST, CMD),
  shell(CMD, EXST).

call_prover(e, TPTP, TSTP, RST) :- 
  concat_shell(["eprover --cpu-limit=60 -p ", TPTP, " > temp.tstp"], _), 
  (
    any_line_path('temp.tstp', =("# Proof found!")) -> 
    concat_shell(["cat temp.tstp | sed '/\\(^#\\|^\\$\\)/d' > ", TSTP], _), RST = true ;
    RST = false
  ),
  delete_file('temp.tstp').

call_prover(v, TPTP, TSTP, RST) :- 
  concat_shell(["vampire --output_axiom_names on --proof tptp --include /home/sk/projects/TPTP/ ", TPTP, " > temp.tstp"], _),  
  (
    any_line_path('temp.tstp', =("% Refutation found. Thanks to Tanya!")) -> 
    concat_shell(["cat temp.tstp | sed '/\\(^%\\|^\\$\\)/d' > ", TSTP], _), RST = true ;
    RST = false
  ),
  delete_file('temp.tstp').

