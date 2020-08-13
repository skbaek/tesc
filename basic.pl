:- [paths].
% % :- module(basic, 
%   [
%     sbsm/3,
%     eqr/3,
%     para/1,
%     para_e1/1,
%     para_e2/1,
%     mate/1,
%     axiomatic/1,
%     write_list/1,
%     unsigned_atom/1,
%     paral/1,
%     no_fv_form/2,
%     num_succ/2,
%     num_pred/2,
%     lit_atom/2,
%     body_lits/2,
%     ground_all/2,
%     para__s/2,
%     first_char/2,
%     erient_form/2,
%     inst_with_lvs/2,
%     explicate_form/2,
%     implicate_form/2,
%     relabel/2,
%     fnnf/2,
%     decom_uct/3,
%     decom_qtf/3,
%     mate/3,
%     many/3,
%     range/3,
%     pluck/3,
%     mk_par/3,
%     apply_uop/3,
%     timed_call/4,
%     maplist_cut/3, 
%     redirect_id/3, 
%     resymb_form/3, 
%     tt_term/3,
%     add_fas/3,
%     strip_fas/3,
%     mk_vars/3,
%     mk/3,
%     pluck/4,
%     substitute_form/4,
%     decom_bct/4,
%     apply_bop/4,
%     map_form/4,
%     maplist_cut/4,
%     sp/4,
%     many_nb/5,
%     ap/5,
%     cp/5,
%     bp/6
%   ]
% ).

% :- meta_predicate maplist_cut(2, ?, ?), maplist_cut(3, ?, ?, ?), timed_call(+, 0, 0).

%%%%%%%%%%%%%%%% GENERIC %%%%%%%%%%%%%%%% 



random_pluck(LIST, ELEM, REST) :- 
  random_member(ELEM, LIST), 
  delete(LIST, ELEM, REST).

random_n(0, _, []).
random_n(NUM, LIST, [ELEM | SEL]) :-
  num_pred(NUM, PRED), 
  random_pluck(LIST, ELEM, REST),
  random_n(PRED, REST, SEL).

  
timed_call(TIME, GOAL, EARLY, LATE) :- 
  catch(
    call_with_time_limit(
      TIME, 
      (
        call(GOAL) -> 
        true 
      ;
        throw(premature_failure)
      )
    ),
    ERROR, 
    (
      ERROR = premature_failure ->
      call(EARLY) 
    ;
      call(LATE) 
    )
  ).  

% timed_call(TIME, GOAL, ALT_GOAL) :- 
%   catch(
%     call_with_time_limit(
%       TIME, 
%       (
%         call(GOAL) -> 
%         true 
%       ;
%         write("Premature failure in timed call.\n"),
%         throw(time_limit_exceeded)
%       )
%     ),
%     time_limit_exceeded, 
%     call(ALT_GOAL)
%   ).  

ground_all(TERM, EXP) :- 
  term_variables(EXP, VARS),
  maplist_cut('='(TERM), VARS).


%%%%%%%%%%%%%%%% SYNTACTIC %%%%%%%%%%%%%%%% 

type_sf(a, $pos($and(_, _))). 
type_sf(a, $neg($or(_, _))). 
type_sf(a, $neg($imp(_, _))). 
type_sf(a, $pos($iff(_, _))). 
type_sf(b, $neg( $and(_, _))). 
type_sf(b, $pos($or(_, _))). 
type_sf(b, $pos($imp(_, _))). 
type_sf(b, $neg($iff(_, _))). 
type_sf(c, $pos($fa(_))). 
type_sf(c, $neg($ex(_))). 
type_sf(d, $neg($fa(_))). 
type_sf(d, $pos($ex(_))). 
type_sf(s, $pos($not(_))).
type_sf(s, $neg($not(_))).
type_hyp(TYP, (_, SF)) :- type_sf(TYP, SF).

sf_form($pos(FORM), FORM).
sf_form($neg(FORM), FORM).
hyp_form((_, SF), FORM) :- 
  sf_form(SF, FORM).

unsigned_atom(ATOM) :- \+ molecular(ATOM).
literal(LIT) :- unsigned_atom(LIT).
literal($not(ATOM)) :- unsigned_atom(ATOM).

complements($pos(FORM), $neg(FORM)).
complements($neg(FORM), $pos(FORM)).

hyp_sf((_, SF), SF).

incr_idx_term(VAR, _) :- var(VAR), !, false.
incr_idx_term(#(NUM), #(SUCC)) :- !,
  num_succ(NUM, SUCC).
incr_idx_term(^(FUN, TERMS_I), ^(FUN, TERMS_O)) :- 
  maplist_cut(incr_idx_term, TERMS_I, TERMS_O).
incr_idx_term(TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(incr_idx_term, TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O]. 

substitute_term(fast, _, _, VAR, VAR) :- var(VAR), !.
substitute_term(safe, _, _, VAR, _) :- var(VAR), !, false.
substitute_term(_, CNT, TERM_S, #(NUM), TERM_O) :- !, 
  CNT = NUM -> TERM_O = TERM_S 
; 
  CNT < NUM -> 
  num_pred(NUM, PRED), 
  TERM_O = #(PRED) 
; 
  TERM_O = #(NUM).
substitute_term(MODE, NUM, TERM, ^(FUN, TERMS_I), ^(FUN, TERMS_O)) :- !, 
  maplist_cut(substitute_term(MODE, NUM, TERM), TERMS_I, TERMS_O).
substitute_term(MODE, NUM, TERM_S, TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(substitute_term(MODE, NUM, TERM_S), TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O]. 

resymb_term(_, VAR, VAR) :- var(VAR), !.
resymb_term(_, #(NUM), #(NUM)) :- !.
resymb_term(DICT, ^(FUN, TERMS_I), ^(FUN, TERMS_O)) :- !,
  maplist_cut(resymb_term(DICT), TERMS_I, TERMS_O).
resymb_term(DICT, TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I], 
  length(TERMS_I, ARI),
  maplist_cut(resymb_term(DICT), TERMS_I, TERMS_O), !, 
  (
    get_assoc((FUN, ARI), DICT, IDX) -> 
    mk_par(IDX, TERMS_O, TERM_O)
  ;    
    TERM_O =.. [FUN | TERMS_O] 
  ).


% qtf('!').
% qtf('?').
% 
% uct('~').
% uct('!').
% uct('?').
% 
% bct('|').
% bct('&').
% bct('=>').
% bct('<=>').

log_const(($ true)).
log_const(($ false)).

substitute_form(_, _, _, FORM, FORM) :- log_const(FORM), !.

substitute_form(MODE, NUM, TERM, $not(FORM), $not(FORM_N)) :- !,
  substitute_form(MODE, NUM, TERM, FORM, FORM_N).

substitute_form(MODE, NUM, TERM, FORM_I, FORM_O) :-
  decom_qtf(FORM_I, QTF, SUB_I), !, 
  num_succ(NUM, SUCC),
  ( 
    MODE = safe -> 
    incr_idx_term(TERM, TERM_N) ; 
    TERM_N = TERM
  ),
  substitute_form(MODE, SUCC, TERM_N, SUB_I, SUB_O), 
  apply_uop(QTF, SUB_O, FORM_O). 

substitute_form(MODE, NUM, TERM, FORM, FORM_N) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !, 
  substitute_form(MODE, NUM, TERM, FORM_A, FORM_AN),
  substitute_form(MODE, NUM, TERM, FORM_B, FORM_BN),
  apply_bop(BCT, FORM_AN, FORM_BN, FORM_N). 

substitute_form(MODE, NUM, TERM, FORM, FORM_N) :- 
  FORM =.. [REL | TERMS], 
  maplist_cut(substitute_term(MODE, NUM, TERM), TERMS, TERMS_N), 
  FORM_N =.. [REL | TERMS_N]. 

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

resymb_form((RDICT, FDICT), FORM, FORM_N) :- 
  FORM =.. [REL | TERMS], 
  maplist_cut(resymb_term(FDICT), TERMS, TERMS_N), !,  
  length(TERMS, ARI),
  (
    get_assoc((REL, ARI), RDICT, IDX) -> 
    mk_par(IDX, TERMS_N, FORM_N)
  ;
    FORM_N =.. [REL | TERMS_N]
  ).

explicate_form(FORM, FORM) :- log_const(FORM), !.
explicate_form(FORM, FORM_N) :-
  decom_uct(FORM, UCT, SUB), !, 
  explicate_form(SUB, SUB_N),
  apply_uop(UCT, SUB_N, FORM_N). 
explicate_form(FORM, FORM_N) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !,  
  explicate_form(FORM_A, FORM_AN),
  explicate_form(FORM_B, FORM_BN),
  apply_bop(BCT, FORM_AN, FORM_BN, FORM_N). 
explicate_form(FORM, FORM_N) :- 
  FORM =.. [REL | TERMS], 
  maplist_cut(explicate_term, TERMS, TERMS_N), !,  
  FORM_N =.. [REL | TERMS_N].

implicate_form(FORM, FORM) :- log_const(FORM), !.
implicate_form(FORM, FORM_N) :-
  decom_uct(FORM, UCT, SUB), !, 
  implicate_form(SUB, SUB_N),
  apply_uop(UCT, SUB_N, FORM_N). 
implicate_form(FORM, FORM_N) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !,  
  implicate_form(FORM_A, FORM_AN),
  implicate_form(FORM_B, FORM_BN),
  apply_bop(BCT, FORM_AN, FORM_BN, FORM_N). 
implicate_form(FORM, FORM_N) :- 
  FORM =.. [REL | TERMS], 
  maplist_cut(implicate_term, TERMS, TERMS_N), !,  
  FORM_N =.. [REL | TERMS_N].

explicate_term(VAR, VAR) :- var(VAR), !.
explicate_term(#(NUM), #(NUM)) :- !.
explicate_term(TERM_I, ^(FUN, TERMS_O)) :- 
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(explicate_term, TERMS_I, TERMS_O), !.

implicate_term(VAR, VAR) :- var(VAR), !.
implicate_term(#(NUM), #(NUM)) :- !.
implicate_term(^(FUN, TERMS_I), TERM) :- 
  maplist_cut(implicate_term, TERMS_I, TERMS_O), !,
  TERM =.. [FUN | TERMS_O].

ab(l, $pos($and(FORM, _)), $pos(FORM)).
ab(r, $pos($and(_, FORM)), $pos(FORM)).
ab(l, $neg($or(FORM, _)), $neg(FORM)).
ab(r, $neg($or(_, FORM)), $neg(FORM)).
ab(l, $neg($imp(FORM, _)), $pos(FORM)).
ab(r, $neg($imp(_, FORM)), $neg(FORM)).
ab(l, $pos($iff(FORM_A, FORM_B)), $pos($imp(FORM_A, FORM_B))).
ab(r, $pos($iff(FORM_A, FORM_B)), $pos($imp(FORM_B, FORM_A))).

aab(SF, SF0, SF1) :-
  ab(l, SF, SF0), 
  ab(r, SF, SF1).

bb($neg($and(FORM_A, FORM_B)), $neg(FORM_A), $neg(FORM_B)).
bb($pos($or(FORM_A, FORM_B)), $pos(FORM_A), $pos(FORM_B)).
bb($pos($imp(FORM_A, FORM_B)), $neg(FORM_A), $pos(FORM_B)).
bb($neg($iff(FORM_A, FORM_B)), $neg($imp(FORM_A, FORM_B)), $neg($imp(FORM_B, FORM_A))).

cb(TERM, $pos($fa(FORM_I)), $pos(FORM_O)) :- substitute_form(fast, TERM, FORM_I, FORM_O).
cb(TERM, $neg($ex(FORM_I)), $neg(FORM_O)) :- substitute_form(fast, TERM, FORM_I, FORM_O).

db(NUM, $neg($fa(FORM_I)),  $neg(FORM_O)) :- 
  mk_par(NUM, [], TERM),
  substitute_form(fast, TERM, FORM_I, FORM_O).
db(NUM, $pos($ex(FORM_I)),  $pos(FORM_O)) :- 
  mk_par(NUM, [], TERM),
  substitute_form(fast, TERM, FORM_I, FORM_O).

sb($pos($not(FORM)), $neg(FORM)).
sb($neg($not(FORM)), $pos(FORM)).



%%%%%%%%%%%%%%%% BASIC RULES %%%%%%%%%%%%%%%% 

ap(
  (PID, SF),
  DIR, 
  (a(PID, DIR, PRF), C), 
  (CID, SF_N), 
  (PRF, SC)
) :- 
  mk_par(C, [], CID),
  num_succ(C, SC), 
  ab(DIR, SF, SF_N), !.

bp(
  (PID, SF), 
  (b(PID, PRF_A, PRF_B), C), 
  (CID, SF_L),
  (CID, SF_R),
  (PRF_A, SC),
  (PRF_B, SC)
) :- 
  mk_par(C, [], CID),
  num_succ(C, SC), 
  bb(SF, SF_L, SF_R), !.

cp(
  (PID, SF), 
  TERM, 
  (c(PID, TERM, PRF), C), 
  (CID, SF_N),
  (PRF, SC)
) :- 
  mk_par(C, [], CID),
  num_succ(C, SC),
  cb(TERM, SF, SF_N), !.

dp(
  (PID, SF),
  (d(PID, PRF), C), 
  (CID, SF_N),
  (PRF, SC)
) :-
  mk_par(C, [], CID),
  num_succ(C, SC),
  db(C, SF, SF_N), !.

fp(
  FORM,
  (f(FORM, PRF_A, PRF_B), C), 
  (CID, $neg(FORM)),
  (CID, $pos(FORM)),
  (PRF_A, SC), 
  (PRF_B, SC)
) :-
  mk_par(C, [], CID),
  num_succ(C, SC), !.

tp(
  SF,
  (t(SF, PRF), C),
  (CID, SF),
  (PRF, SC)
) :- 
  mk_par(C, [], CID),
  num_succ(C, SC), !.

sp(
  (PID, SF),
  (s(PID, PRF), C), 
  (CID, SF_N),
  (PRF, SC)
) :- 
  mk_par(C, [], CID),
  num_succ(C, SC),
  sb(SF, SF_N), !.

wp(
  (PID, _),
  (w(PID, PRF), C), 
  (PRF, SC)
) :-
  num_succ(C, SC).

xp(
  (PID, $pos(FORM_P)), 
  (NID, $neg(FORM_N)), 
  (x(PID, NID), _)
) :-
  unify_with_occurs_check(FORM_P, FORM_N), !.

justified(_, $neg($false)). 
justified(_, $pos($true)). 

justified(_, $pos($fa(#(0) = #(0)))).
justified(_, $pos($fa($fa($imp(#(1) = #(0), #(0) = #(1)))))).
justified(_, $pos($fa($fa($fa($imp(#(2) = #(1), $imp(#(1) = #(0), #(2) = #(0)))))))).

justified(_, $pos(FORM)) :- 
  is_mono_rel(0, FORM) ; 
  is_mono_fun(0, FORM). 

% justified(_, + ((FUNA ^ []) = (FUNB ^ [])), [ne_eval]) :- 
%   atom_number(FUNA, NUMA),
%   atom_number(FUNB, NUMB),
%   NUMA \= NUMB.
% 
% justified(_, - ((FUNA ^ []) = (FUNB ^ [])), [ne_eval]) :- 
%   atom_number(FUNA, NUMA),
%   atom_number(FUNB, NUMB),
%   NUMA \= NUMB.

justified(C, $pos(FORM)) :- 
  strip_fas(FORM, ARI, $imp($ex(ANTE), CONS)), 
  counter_safe(C, ANTE),
  mk_vars(ARI, VARS), 
  mk_par(C, VARS, TERM),
  substitute_form(safe, TERM, ANTE, TEMP),
  TEMP == CONS.

justified(C, $pos(FORM)) :- 
  strip_fas(FORM, ARI, $iff(ATOM, BODY)), 
  counter_safe(C, BODY),
  mk_vars(ARI, VARS),
  mk_par(C, VARS, ATOM).

is_mono_rel(N, $fa($fa($imp(#(1) = #(0), F)))) :- !,
  num_succ(N, SN), 
  is_mono_rel(SN, F). 
   
is_mono_rel(N, $imp(A0, A1)) :- 
  A0 =.. [R | TS0],
  A1 =.. [R | TS1],
  mk_mono_args(N, TS0, TS1).

is_mono_fun(N, $fa($fa($imp(#(1) = #(0), F)))) :- !,
  num_succ(N, SN), 
  is_mono_fun(SN, F). 
   
is_mono_fun(N, (T0 = T1)) :- 
  T0 =.. [F | TS0],
  T1 =.. [F | TS1],
  mk_mono_args(N, TS0, TS1).

%%%%%%%%%%%%%%%% DERIVED RULES %%%%%%%%%%%%%%%% 

many(RULS, (HYPS, GOAL), HGS) :-
  member(s, RULS), 
  pluck(HYPS, HYP, REST), 
  sp(HYP, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(a, RULS), 
  pluck(HYPS, HYP, REST), 
  aap(HYP, GOAL, HYP_L, HYP_R, GOAL_T), 
  many(RULS, ([HYP_R, HYP_L | REST], GOAL_T), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(d, RULS), 
  pluck(HYPS, HYP, REST), 
  dp(HYP, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(c, RULS), 
  pluck(HYPS, HYP, REST), 
  cp(HYP, _, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(b, RULS), 
  pluck(HYPS, HYP, REST), 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), !, 
  many(RULS, ([HYP_L | REST], GOAL_L), HGSL), !,
  many(RULS, ([HYP_R | REST], GOAL_R), HGSR),
  append(HGSL, HGSR, HGS). 

many(_, HG, [HG]).

many_nb(RULS, HYPS, GOAL, HYP_NS, GOAL_N) :-
  many(RULS, (HYPS, GOAL), [(HYP_NS, GOAL_N)]).

aap(HYP, GOAL, HYP_L, HYP_R, GOAL_N) :- 
  ap(HYP, l, GOAL, HYP_L, GOAL_T), 
  ap(HYP, r, GOAL_T, HYP_R, GOAL_N). 

abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) :- 
  bp(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_TL, GOAL_TR), 
  ap(HYP_A, l, GOAL_TL, HYP_AL, GOAL_L),
  ap(HYP_A, r, GOAL_TR, HYP_AR, GOAL_R).

abpr(HYP_A, HYP_B, GOAL, HYP_AR, HYP_BL, GOAL_L, HYP_AL, HYP_BR, GOAL_R) :- 
  bp(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_TL, GOAL_TR), 
  ap(HYP_A, r, GOAL_TL, HYP_AR, GOAL_L),
  ap(HYP_A, l, GOAL_TR, HYP_AL, GOAL_R).

fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R) :- 
  hyp_sf(HYP, SF), 
  bb(SF, SF_L, _),
  fps(SF_L, GOAL, HYP_LN, HYP_L, GOAL_LN, GOAL_L), 
  bp(HYP, GOAL_LN, HYP_LP, HYP_R, GOAL_LPN, GOAL_R), 
  mate(HYP_LP, HYP_LN, GOAL_LPN).

fps($pos(FORM), GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P) :- 
  fp(FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P).

fps($neg(FORM), GOAL, HYP_P, HYP_N, GOAL_P, GOAL_N) :- 
  fp(FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P).

cdp(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  GOAL = (_, CNT), 
  dp(HYP_D, GOAL, HYP_N_D, GOAL_T), 
  mk_par(CNT, [], PAR),
  cp(HYP_C, PAR, GOAL_T, HYP_N_C, GOAL_N). 

dp_lax(CNT_I, HYP_I, GOAL_I, CNT_O, HYP_O, GOAL_O) :-  
  dp(HYP_I, GOAL_I, HYP_T, GOAL_T) -> 
  ( 
    vac_qtf(HYP_I) -> CNT_T = CNT_I ;
    num_succ(CNT_I, CNT_T)
  ),
  dp_lax(CNT_T, HYP_T, GOAL_T, CNT_O, HYP_O, GOAL_O) 
;
  CNT_O = CNT_I, 
  HYP_O = HYP_I, 
  GOAL_O = GOAL_I. 
  
cp_vac(HYP_I, GOAL_I, HYP_O, GOAL_O) :-  
  vac_qtf(HYP_I),
  cp(HYP_I, _, GOAL_I, HYP_O, GOAL_O).

dp_vac(HYP_I, GOAL_I, HYP_O, GOAL_O) :-  
  vac_qtf(HYP_I),
  dp(HYP_I, GOAL_I, HYP_O, GOAL_O).

cp_lax(CNT, HYP_I, GOAL_I, HYP_O, GOAL_O) :-  
  vac_qtf(HYP_I) ->  
  (
    cp(HYP_I, _, GOAL_I, HYP_T, GOAL_T) -> 
    cp_lax(CNT, HYP_T, GOAL_T, HYP_O, GOAL_O)  
  ;
    HYP_O = HYP_I, 
    GOAL_O = GOAL_I
  )
;
  (
    num_pred(CNT, PRED) -> 
    cp(HYP_I, _, GOAL_I, HYP_T, GOAL_T),
    cp_lax(PRED, HYP_T, GOAL_T, HYP_O, GOAL_O)  
  ;
    HYP_O = HYP_I, 
    GOAL_O = GOAL_I
  ).

cdp_lax(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  type_hyp(d, HYP_D),
  type_hyp(c, HYP_C),
  dp_lax(0, HYP_D, GOAL, CNT, HYP_N_D, GOAL_T), 
  cp_lax(CNT, HYP_C, GOAL_T, HYP_N_C, GOAL_N). 
  
union([], []).

union([List | Lists], Set) :- 
  union(Lists, TempSet),
  union(List, TempSet, Set).

write_list(_, []).
write_list(STRM, [ELEM]) :- format(STRM, '~w', ELEM).
write_list(STRM, [ELEM | List]) :- 
  format(STRM, '~w\n', ELEM),
  write_list(STRM, List).

write_list([]).
write_list([Elem | List]) :- 
  format('~w\n', Elem),
  write_list(List).

strings_concat([], "").

strings_concat([Str | Strs], NewStr) :- 
  strings_concat(Strs, TempStr), 
  string_concat(Str, TempStr, NewStr). 

strings_concat_with(_, [], "").

strings_concat_with(_, [Str], Str).

strings_concat_with(Div, [Str | Strs], Result) :-
  strings_concat_with(Div, Strs, TempStr),
  strings_concat([Str, Div, TempStr], Result).
 
% Similar to nth0/2, but avoids instantion.
where(ElemA, [ElemB | _], 0) :- 
  ElemA == ElemB.

where(Elem, [_ | List], NUM) :- 
  where(Elem, List, Pred),
  num_succ(Pred, NUM).

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

molecular(Exp) :- 
  member(Exp, 
    [ $fa(_), $ex(_), $not(_), 
      $or(_, _), $and(_, _), $imp(_, _), $iff(_, _) ]).

lit_atom(LIT, ATOM) :- 
  LIT = $not(ATOM) -> true ;
  LIT = ATOM.

decom_uct(FORM, not, SUB) :-
  \+ var(FORM),
  FORM = $not(SUB). 

decom_uct(FORM, QTF, SUB) :- 
  decom_qtf(FORM, QTF, SUB).

decom_qtf(FORM, ex, SUB) :- 
  \+ var(FORM), FORM = $ex(SUB).

decom_qtf(FORM, fa, SUB) :- 
  \+ var(FORM), FORM = $fa(SUB).

decom_bct(FORM, BCT, FORM_A, FORM_B) :- 
  \+ var(FORM),
  FORM = $TEMP, 
  TEMP =.. [BCT, FORM_A, FORM_B].

apply_uop(UCT, FORM, $SUB) :- 
  SUB =.. [UCT, FORM].

apply_bop(BCT, FORM_A, FORM_B, $SUB) :- 
  SUB =.. [BCT, FORM_A, FORM_B].

drop(0, LIST, LIST). 
drop(NUM, [_ | LIST], REM) :- 
  num_pred(NUM, PRED),
  drop(PRED, LIST, REM).

take(0, _, []). 
take(NUM, [ELEM | LIST], [ELEM | REM]) :- 
  num_pred(NUM, PRED),
  take(PRED, LIST, REM).

slice(DROP, TAKE, LIST, SLICE) :- 
  drop(DROP, LIST, TEMP), 
  take(TAKE, TEMP, SLICE). 

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

mk(SYM, ARG, TERM) :- 
  TERM =.. [SYM, ARG].

mk_par(CNT, TERMS, PAR) :- 
  atomic_concat('@', CNT, FUN), 
  PAR =.. [FUN | TERMS].
  
mk_vars(NUM, VARS) :- 
  mk_vars(asc, NUM, VARS) ;
  mk_vars(desc, NUM, VARS).

mk_vars(DIR, NUM, VARS) :- 
  range(DIR, NUM, NUMS), 
  maplist(mk('#'), NUMS, VARS).



/* MONOtonicity */

mk_mono_args(0, [], []).

mk_mono_args(NUM, [#(NUMA) | VARSA], [#(NUMB) | VARSB]) :-
  NUMA is (NUM * 2) - 1, 
  NUMB is (NUM * 2) - 2, 
  Pred is NUM - 1,
  mk_mono_args(Pred, VARSA, VARSB).

mk_mono_eq(NUM, FUN, TERM_A = TERM_B) :- 
  mk_mono_args(NUM, VARS_A, VARS_B),
  TERM_A =.. [FUN | VARS_A],
  TERM_B =.. [FUN | VARS_B].

mk_mono_imp(NUM, REL, $imp(ATOM_A, ATOM_B)) :- 
  mk_mono_args(NUM, VarsA, VarsB),
  ATOM_A =.. [REL | VarsA],
  ATOM_B =.. [REL | VarsB], !.

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

mk_mono(NUM, Cons, $fa($fa($imp(#(1) = #(0), MONO)))) :-
  num_pred(NUM, Pred), 
  mk_mono(Pred, Cons, MONO), !.

orient_dir(OPF, ONF, l, OPF, ONF).
orient_dir(ONF, OPF, r, OPF, ONF).

orient_sign(OPF, ONF, OPF, ONF) :- 
  OPF = (_, $pos(_)),
  ONF = (_, $neg(_)).

orient_sign(ONF, OPF, OPF, ONF) :- 
  OPF = (_, $pos(_)),
  ONF = (_, $neg(_)).

strip_fas($fa(FORM), NUM, BODY) :- !,
  strip_fas(FORM, PRED, BODY), 
  num_succ(PRED, NUM).

strip_fas(Form, 0, Form).

inst_with_lvs($fa(FORM), BODY) :- !,
  substitute_form(fast, _, FORM, TEMP), 
  inst_with_lvs(TEMP, BODY).

inst_with_lvs(FORM, FORM).

% inst_fas(FORM, FORM) :- FORM \= $fa(_).
% inst_fas($fa(FORM), BODY) :-
%   substitute_form(fast, _, FORM, TEMP),
%   inst_fas(TEMP, BODY).


inst_with_pars(NUM, $fa(FORM), CNT, BODY) :- !,
  mk_par(NUM, [], PAR),
  substitute_form(fast, PAR, FORM, TEMP), 
  num_succ(NUM, SUCC), 
  inst_with_pars(SUCC, TEMP, CNT, BODY).

inst_with_pars(NUM, FORM, NUM, FORM).

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

tt_term(VARS, Var, #(NUM)) :- 
  var(Var),
  where(Var, VARS, NUM), !.

tt_term(VARS, TT, TERM) :- 
  TT =.. [FUN | TTS], 
  maplist_cut(tt_term(VARS), TTS, TERMS), !,
  TERM =.. [FUN | TERMS].

first_char(STR, CHAR) :- 
  string_codes(STR, [CODE | _]), 
  char_code(CHAR, CODE).

no_bv_term(_, VAR) :- var(VAR), !.
no_bv_term(CNT, #(NUM)) :- !, NUM \= CNT.
no_bv_term(CNT, TERM) :- 
  TERM =.. [_ | TERMS],
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
no_bv_form(NUM, FORM) :- 
  FORM =.. [_ | TERMS],
  maplist_cut(no_bv_term(NUM), TERMS).

vac_qtf(HYP) :- 
  hyp_form(HYP, FORM),
  decom_qtf(FORM, _, SUB), 
  no_bv_form(0, SUB).

no_fv_term(_, VAR) :- var(VAR), !, false.
no_fv_term(CNT, #(NUM)) :- !, NUM < CNT.
no_fv_term(CNT, TERM) :- 
  TERM =.. [_ | TERMS],
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
no_fv_form(NUM, FORM) :- 
  FORM =.. [_ | TERMS],
  maplist_cut(no_fv_term(NUM), TERMS).

no_fv_sf(CNT, SF) :- 
  sf_form(SF, FORM),
  no_fv_form(CNT, FORM).

has_idx_ge(C, X) :- 
  sub_term(T, X), 
  T =.. [F | _], 
  atom_concat('@', ATOM, F), 
  atom_number(ATOM, NUM),
  C =< NUM.

counter_safe(C, X) :- 
  ground(X), 
  \+ has_idx_ge(C, X).

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
  put_char(STRM, ';'),
  call(PTR, STRM, ELEM),
  put_list(STRM, PTR, LIST), !.

put_dot(STRM) :-
  put_char(STRM, '$').

put_bytes(_, []).

put_bytes(STRM, [BYTE | BYTES]) :- 
  put_byte(STRM, BYTE),
  put_bytes(STRM, BYTES).

put_bytes_dot(STRM, BYTES) :- 
  put_bytes(STRM, BYTES), 
  put_dot(STRM). 

put_functor(STRM, FUN) :- 
  put_atom(STRM, FUN) ;
  put_string(STRM, FUN).

put_string(STRM, STR) :- 
  string(STR), 
  put_byte(STRM, 34), 
  string_codes(STR, BYTES), 
  put_bytes_dot(STRM, BYTES).

put_atom(STRM, ATOM) :- 
  atom(ATOM), 
  atom_codes(ATOM, BYTES),
  put_bytes_dot(STRM, BYTES).

put_dir(STRM, l) :- 
  put_char(STRM, "<").

put_dir(STRM, r) :- 
  put_char(STRM, ">").

put_num(STRM, NUM) :- 
  number(NUM),
  number_codes(NUM, BYTES),
  put_bytes_dot(STRM, BYTES).
 
put_id(STRM, ID) :- !,
  put_atom(STRM, ID).
  
put_term(STRM, #(NUM)) :- !, put_char(STRM, '#'), put_num(STRM, NUM).
put_term(STRM, TERM) :- 
  TERM =.. [FUN | TERMS],
  put_char(STRM, '^'), 
  put_functor(STRM, FUN), 
  put_terms(STRM, TERMS). 

put_terms(STRM, TERMS) :- 
  put_list(STRM, put_term, TERMS).

put_form(STRM, $true) :- !,
  put_char(STRM, 'T').

put_form(STRM, $false) :- !, 
  put_char(STRM, 'F').

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

put_form(STRM, FORM) :- 
  FORM =.. [REL | TERMS],
  put_char(STRM, '^'), 
  put_atom(STRM, REL), 
  put_terms(STRM, TERMS).

put_sf(STRM, $pos(FORM)) :- 
  put_char(STRM, '+'),
  put_form(STRM, FORM).
put_sf(STRM, $neg(FORM)) :- 
  put_char(STRM, '-'),
  put_form(STRM, FORM).

put_prf(STRM, a(ID, DIR, PRF)) :- 
  put_char(STRM, 'A'), 
  put_id(STRM, ID), 
  put_dir(STRM, DIR),
  put_prf(STRM, PRF).
  
put_prf(STRM, b(ID, PRF_L, PRF_R)) :- 
  put_char(STRM, 'B'), 
  put_id(STRM, ID), 
  put_prf(STRM, PRF_L),
  put_prf(STRM, PRF_R).

put_prf(STRM, c(ID, TERM, PRF)) :- 
  put_char(STRM, 'C'), 
  put_id(STRM, ID), 
  put_term(STRM, TERM),
  put_prf(STRM, PRF).

put_prf(STRM, d(ID, PRF)) :- 
  put_char(STRM, 'D'), 
  put_id(STRM, ID), 
  put_prf(STRM, PRF).

put_prf(STRM, f(FORM, PRF_L, PRF_R)) :- 
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  put_prf(STRM, PRF_L),
  put_prf(STRM, PRF_R).

put_prf(STRM, s(ID, PRF)) :- 
  put_char(STRM, 'S'), 
  put_id(STRM, ID), 
  put_prf(STRM, PRF).

put_prf(STRM, t(SF, PRF)) :- 
  put_char(STRM, 'T'), 
  put_sf(STRM, SF), 
  put_prf(STRM, PRF).

put_prf(STRM, w(ID, PRF)) :- 
  put_char(STRM, 'W'), 
  put_id(STRM, ID), 
  put_prf(STRM, PRF).

put_prf(STRM, x(PID, NID)) :- 
  put_char(STRM, 'X'), 
  put_id(STRM, PID), 
  put_id(STRM, NID).


%%%%%%%%%%%%%%%% TACTICS  %%%%%%%%%%%%%%%%


% eq_refl(CONC, GOAL)
% --- 
% GOAL := ... |- CONC : TERM = TERM, ...
eq_refl(CONC, GOAL) :- 
  tp($pos($fa(#(0) = #(0))), GOAL, HYP0, GOAL_T), 
  cp(HYP0, _, GOAL_T, HYP1, GOAL_N), 
  xp(HYP1, CONC, GOAL_N).

% eq_symm(TERMA, TERMB, GOAL)
% --- 
% GOAL ::= PID : TERMA = TERMB, ... |- NID : TERMB = TERMA, ...
% IPF = PID + TERMA = TERMB
% INF = NID - TERMB = TERMA
eq_symm(OPF, ONF, GOAL) :- 
  OPF = (_, $pos(TERM_A = TERM_B)), 
  ONF = (_, $neg(TERM_B = TERM_A)),
  tp($pos($fa($fa($imp(#(1) = #(0), #(0) = #(1))))), GOAL, HYP0, GOAL0), 
  cp(HYP0, TERM_A, GOAL0, HYP1, GOAL1), 
  cp(HYP1, TERM_B, GOAL1, HYP2, GOAL2), 
  bp(HYP2, GOAL2, HYP3, HYP4, GOAL3, GOAL4), 
  mate_pn(OPF, HYP3, GOAL3), 
  mate_pn(HYP4, ONF, GOAL4). 

eq_symm(OPF, GOAL, NewOPF, GOAL_N) :- 
  OPF = (_, $pos(TERM_A = TERM_B)), 
  fp(TERM_B = TERM_A, GOAL, ONF, NewOPF, GOAL_T, GOAL_N), 
  eq_symm(OPF, ONF, GOAL_T).

% eq_trans(TERM_A, TERM_B, TERM_C, GOAL)
% --- 
% GOAL := PID0 : TERM_A = TERM_B, PID1 : TERM_B = TERM_C, ... |- CID : TERM_A = TERM_C, ...
% IPF0 = PID0 + TERM_A = TERM_B
% IPF1 = PID1 + TERM_B = TERM_C
% INF = NID - TERM_A = TERM_C
eq_trans(IPF0, IPF1, INF, GOAL) :- 
  IPF0 = (_, $pos(TERM_A = TERM_B)), !,
  IPF1 = (_, $pos(TERM_B = TERM_C)), !,
  INF = (_, $neg(TERM_A = TERM_C)), !,
  tp($pos($fa($fa($fa($imp(#(2) = #(1), $imp(#(1) = #(0), #(2) = #(0))))))), GOAL, MONO0, GOAL0),  !,
  cp(MONO0, TERM_A, GOAL0, MONO1, GOAL1), !,
  cp(MONO1, TERM_B, GOAL1, MONO2, GOAL2), !,
  cp(MONO2, TERM_C, GOAL2, MONO3, GOAL3), !,
  bp(MONO3, GOAL3, MONO4, MONO5, GOAL4, GOAL5), !,
  mate(IPF0, MONO4, GOAL4), !,
  bp(MONO5, GOAL5, MONO6, MONO7, GOAL6, GOAL7), !,
  mate(IPF1, MONO6, GOAL6), !,
  mate(INF, MONO7, GOAL7), !.

terms_size([], 0).
terms_size([TERM | TERMS], SIZE) :- 
  term_size(TERM, SIZE_A), 
  terms_size(TERMS, SIZE_B), 
  SIZE is SIZE_A + SIZE_B.

term_size(VAR, 1) :- var(VAR), !.
term_size(^(_, TERMS), SIZE) :- !,
  terms_size(TERMS, TEMP), 
  num_succ(TEMP, SIZE).
term_size(_, 1).

orient_equation(TERM_A = TERM_B, TERM_L = TERM_R) :- 
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

erient_form(FORM, FORM).
erient_form(TERM_A = TERM_B, TERM_B = TERM_A).

erient_stom(SA, SA).
erient_stom($pos(TERM_A = TERM_B), $pos(TERM_B = TERM_A)).
erient_stom($neg(TERM_A = TERM_B), $neg(TERM_B = TERM_A)).

erient_hyp(HYP, GOAL, HYP, GOAL).
erient_hyp(HYP_I, GOAL_I, HYP_O, GOAL_O) :- 
  HYP_I = (_, $pos(LHS = RHS)), 
  fp(RHS = LHS, GOAL_I, HYP_T, HYP_O, GOAL_T, GOAL_O), 
  eq_symm(HYP_I, HYP_T, GOAL_T), !. 

use_pf(HYP, GOAL) :- 
  HYP = (_, $pos($false)),
  tp($neg($false), GOAL, CMP, GOAL_N),
  xp(HYP, CMP, GOAL_N).

use_nt(HYP, GOAL) :- 
  HYP = (_, $neg($true)),
  tp($pos($true), GOAL, CMP, GOAL_N),
  xp(CMP, HYP, GOAL_N).

use_lc(HYP, GOAL) :- 
  use_pf(HYP, GOAL) ; 
  use_nt(HYP, GOAL).

use_contra(HYP, GOAL) :- 
  use_lc(HYP, GOAL) ;
  (
    sp(HYP, GOAL, HYP_N, GOAL_N) ;
    ap(HYP, l, GOAL, HYP_N, GOAL_N) ; 
    ap(HYP, r, GOAL, HYP_N, GOAL_N) 
  ),
  use_contra(HYP_N, GOAL_N) ;
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  use_contra(HYP_L, GOAL_L),
  use_contra(HYP_R, GOAL_R).

falsity($pos($false)).
falsity($neg($true)).

mate(HYP0, HYP1, GOAL) :- 
  orient_sign(HYP0, HYP1, OPF, ONF),
  mate_pn(OPF, ONF, GOAL).
 
mate_pn(PYP, NYP, GOAL) :- 
  erient_hyp(PYP, GOAL, PYP_N, GOAL_N), 
  xp(PYP_N, NYP, GOAL_N).



%%%%%%%% GET %%%%%%%%

get_list(STRM, GTR, LIST) :- 
  get_char(STRM, CH), 
  (
    CH = ';' -> 
    call(GTR, STRM, ELEM), 
    get_list(STRM, GTR, TAIL),
    LIST = [ELEM | TAIL] ;
    CH = '.', 
    LIST = []
  ).

get_until_dot(STRM, BYTES) :- 
  get_byte(STRM, BYTE), 
  (
    BYTE = 36 -> BYTES = [] ;
    get_until_dot(STRM, TAIL),
    BYTES = [BYTE | TAIL] 
  ).
  
get_string(STRM, STR) :- 
  get_until_dot(STRM, BYTES), 
  string_codes(STR, BYTES).
  
get_functor(STRM, FUN) :- 
  get_until_dot(STRM, [BYTE | BYTES]), 
  (
    BYTE = 34 -> 
    string_codes(FUN, BYTES) 
  ;
    atom_codes(FUN, [BYTE | BYTES])
  ).

get_atom(STRM, ATOM) :- 
  get_string(STRM, STR),
  atom_string(ATOM, STR).
  
get_sign(STRM, SIGN) :- 
  get_char(STRM, CH),
  (
    CH = '+', SIGN = pos ;
    CH = '-', SIGN = neg
  ).

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

get_term(STRM, '#', #(NUM)) :- get_num(STRM, NUM).
get_term(STRM, '^', TERM) :- 
  get_functor(STRM, FUN), 
  get_terms(STRM, TERMS),
  TERM =.. [FUN | TERMS].

get_terms(STRM, TERMS) :- 
  get_list(STRM, get_term, TERMS).

get_form(STRM, FORM) :-
  get_char(STRM, CH), 
  get_form_aux(STRM, CH, FORM).

get_form_aux(_, 'T', $true).
get_form_aux(_, 'F', $false).

get_form_aux(STRM, '^', FORM) :- 
  get_atom(STRM, REL), 
  get_terms(STRM, TERMS), 
  FORM =.. [REL | TERMS].

get_form_aux(STRM, CH, FORM) :- 
  char_uct(CH, UCT), 
  get_form(STRM, SUB), 
  apply_uop(UCT, SUB, FORM).

get_form_aux(STRM, CH, FORM) :- 
  char_bct(CH, BCT), 
  get_form(STRM, SUB_A), 
  get_form(STRM, SUB_B), 
  apply_bop(BCT, SUB_A, SUB_B, FORM).

get_sf(STRM, SF) :- 
  get_sign(STRM, SIGN),
  get_form(STRM, FORM),
  apply_uop(SIGN, FORM, SF).

get_id(STRM, ID) :- 
  get_atom(STRM, ID).

get_prf(STRM, PRF) :- 
  get_char(STRM, CH), !, 
  get_prf(STRM, CH, PRF).

get_prf(STRM, 'A', a(PID, DIR, SUB)) :- 
  get_id(STRM, PID),  
  get_dir(STRM, DIR),
  get_prf(STRM, SUB).  
  
get_prf(STRM, 'B', b(PID, SUB_L, SUB_R)) :- 
  get_id(STRM, PID), 
  get_prf(STRM, SUB_L), 
  get_prf(STRM, SUB_R).

get_prf(STRM, 'C', c(PID, TERM, SUB)) :- 
  get_id(STRM, PID), 
  get_term(STRM, TERM), 
  get_prf(STRM, SUB).
  
get_prf(STRM, 'D', d(PID, SUB)) :- 
  get_id(STRM, PID), 
  get_prf(STRM, SUB).

get_prf(STRM, 'F', f(FORM, SUB_L, SUB_R)) :-
  get_form(STRM, FORM), 
  get_prf(STRM, SUB_L), 
  get_prf(STRM, SUB_R). 

get_prf(STRM, 'S', s(PID, SUB)) :- 
  get_id(STRM, PID), 
  get_prf(STRM, SUB). 

get_prf(STRM, 'T', t(SF, SUB)) :- 
  get_sf(STRM, SF), 
  get_prf(STRM, SUB). 

get_prf(STRM, 'W', w(PID, SUB)) :-
  get_id(STRM, PID), 
  get_prf(STRM, SUB). 
  
get_prf(STRM, 'X', x(PID, NID)) :- 
  get_id(STRM, PID), 
  get_id(STRM, NID).


%%%%%%%%%%%%%%%% PROPOSITIONAL CONNECTION TABLEAUX %%%%%%%%%%%%%%%%

startable_hyp((_, SF)) :- 
  startable_sf(SF).

startable_sf(SF) :- 
  sb(SF, SF_N) -> startable_sf(SF_N) 
;
  aab(SF, SF_L, SF_R) -> 
  (startable_sf(SF_L) ; startable_sf(SF_R)) 
;
  bb(SF, SF_L, SF_R) -> 
  startable_sf(SF_L),
  startable_sf(SF_R)
; 
  falsity(SF) 
; 
  SF = $pos(_). 
  
path_redundant(HYP, PATH) :- 
  hyp_sf(HYP, SF),
  erient_stom(SF, SF_A),
  member((_, SF_B), PATH), 
  SF_A == SF_B.

pblx(PQ, HYPS, GOAL) :- 
  pluck(HYPS, HYP, REST), 
  pblx((start, PQ), REST, [], HYP, GOAL).

pblx(MODE, HYPS, PATH, HYP, GOAL) :- 
  sp(HYP, GOAL, HYP_N, GOAL_N), !, 
  pblx(MODE, HYPS, PATH, HYP_N, GOAL_N).
  
pblx((PHASE, q), HYPS, PATH, HYP, GOAL) :- 
  cp(HYP, _, GOAL, HYP_N, GOAL_N), !, 
  pblx((PHASE, q), HYPS, PATH, HYP_N, GOAL_N).

pblx(MODE, HYPS, PATH, HYP, GOAL) :- 
  aap(HYP, GOAL, HYP_L, HYP_R, GOAL_N), !, 
  (
    pblx(MODE, [HYP_R | HYPS], PATH, HYP_L, GOAL_N) ;
    pblx(MODE, [HYP_L | HYPS], PATH, HYP_R, GOAL_N)
  ).

pblx((start, PQ), HYPS, PATH, HYP, GOAL) :- 
  fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  startable_hyp(HYP_R),
  pblx((start, PQ), HYPS, PATH, HYP_L, GOAL_L),
  pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R).

pblx((match, PQ), HYPS, PATH, HYP, GOAL) :- 
  fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  (
    pblx((match, PQ), HYPS, PATH, HYP_L, GOAL_L),
    pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R)
  ;
    pblx((match, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R),
    pblx((block, PQ), HYPS, PATH, HYP_L, GOAL_L)
  ).
  
pblx((block, PQ), HYPS, PATH, HYP, GOAL) :- 
  fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  pblx((block, PQ), HYPS, PATH, HYP_L, GOAL_L),
  pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R).

pblx((start, _), _, _, HYP, GOAL) :-
  use_contra(HYP, GOAL).

pblx((start, PQ), HYPS, PATH, HYP, GOAL) :-
  hyp_sf(HYP, $pos(_)), 
  pblx((block, PQ), HYPS, PATH, HYP, GOAL).

pblx((match, _), _, [CMP | _], HYP, GOAL) :- 
  mate(HYP, CMP, GOAL).
  
pblx((block, _), _, _, HYP, GOAL) :-
  use_contra(HYP, GOAL).

pblx((block, _), _, PATH, HYP, GOAL) :- 
  member(CMP, PATH),
  mate(HYP, CMP, GOAL).

pblx((block, PQ), HYPS, PATH, HYP, GOAL) :- 
  \+ path_redundant(HYP, PATH),
  pluck(HYPS, HYP_N, REST), 
  pblx((match, PQ), REST, [HYP | PATH], HYP_N, GOAL). 

% iff_sf_conv($pos($iff(FORM_A, FORM_B)), $neg($and($or(FORM_A, FORM_B), $or($not(FORM_A), $not(FORM_B))))).
% iff_sf_conv($neg($iff(FORM_A, FORM_B)), $pos($and($or(FORM_A, FORM_B), $or($not(FORM_A), $not(FORM_B))))).

iff_conv_pos_aux(TRP) :- 
  para_ba_swap(TRP, TRP_A, TRP_B), 
  mate(TRP_B),
  para__s(TRP_A, TRP_C), 
  mate(TRP_C). 

iff_conv_neg_aux(TRP) :- 
  para__b(TRP, TRP_2, TRP_1),
  para_a_(l, TRP_1, TRP_1A), 

  (D1 = l, D2 = r ; D1 = r, D2 = l),

  para__a(D1, TRP_1A, TRP_1B), 
  mate(TRP_1B),
  para_a_(r, TRP_2, TRP_2A), 
  para__a(D2, TRP_2A, TRP_2B), 
  para__s(TRP_2B, TRP_2C), 
  mate(TRP_2C).

iff_conv(TRP_I, TRP_O) :- 
  trp_prem(TRP_I, PREM), 
  hyp_sf(PREM, $neg($iff(FORM_A, FORM_B))),
  para_f_($and($or($not(FORM_B), $not(FORM_A)), $or(FORM_B, FORM_A)), TRP_I, TRP_T, TRP_O), 
% TRP_T : - (FORM_A <=> FORM_B), - ((~ FORM_B \/ ~ FORM_A) & (FORM_B \/ FORM_A))
  para_b_(TRP_T, TRP_A, TRP_B),

% TRP_A : - (FORM_A => FORM_B), - ((~ FORM_B \/ ~ FORM_A) & (FORM_B \/ FORM_A))
% TRP_B : - (FORM_B => FORM_A), - ((~ FORM_B \/ ~ FORM_A) & (FORM_B \/ FORM_A))

  iff_conv_neg_aux(TRP_A),
  iff_conv_neg_aux(TRP_B).

iff_conv(TRP_I, TRP_O) :- 
  trp_prem(TRP_I, PREM), 
  hyp_sf(PREM, $pos($iff(FORM_A, FORM_B))),
  % fp($and($or(FORM_A, $not(FORM_B)), $or(FORM_B, $not(FORM_A))), GOAL, CONC_N, PREM_N, GOAL_T, GOAL_N),
  para_f_($and($or(FORM_A, $not(FORM_B)), $or(FORM_B, $not(FORM_A))), TRP_I, TRP_T, TRP_O), 
  para_ab_swap(TRP_T, TRP_A, TRP_B), 
  iff_conv_pos_aux(TRP_A), 
  iff_conv_pos_aux(TRP_B). 


% iff_conv((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
%   hyp_sf(HYP_A, SF_A),
%   iff_sf_conv(SF_A, SF_N), 
%   fps(SF_N, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N),
%   %pblx(p, [HYP_A, HYP_T], GOAL_T).
%   true.

e_iff_conv((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  hyp_sf(HYP_A, $neg($iff(FORM_A, FORM_B))),
  FORM = $and($or($not(FORM_A), $not(FORM_B)), $or(FORM_A, FORM_B)),
  fp(FORM, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N),
  pblx(p, [HYP_A, HYP_T], GOAL_T).

%%%%%%%%%%%%%%%% PARALLEL DECOMPOSITION PREDICATES %%%%%%%%%%%%%%%%
  
para_a_(DIR, (HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  ap(HYP_A, DIR, GOAL, HYP_AN, GOAL_N). 
  
para__a(DIR, (HYP_A, HYP_B, GOAL), (HYP_A, HYP_NB, GOAL_N)) :- 
  ap(HYP_B, DIR, GOAL, HYP_NB, GOAL_N). 

para_b_((HYP_A, HYP_B, GOAL), (HYP_L, HYP_B, GOAL_L), (HYP_R, HYP_B, GOAL_R)) :- 
  bp(HYP_A, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R). 

para__b((HYP_A, HYP_B, GOAL), (HYP_A, HYP_L, GOAL_L), (HYP_A, HYP_R, GOAL_R)) :- 
  bp(HYP_B, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R). 

para_c_(TERM, (HYP_A, HYP_B, GOAL_I), (HYP_NA, HYP_B, GOAL_O)) :- cp(HYP_A, TERM, GOAL_I, HYP_NA, GOAL_O).
para__c(TERM, (HYP_A, HYP_B, GOAL_I), (HYP_A, HYP_NB, GOAL_O)) :- cp(HYP_B, TERM, GOAL_I, HYP_NB, GOAL_O).

para_c_(TRP_I, TRP_O) :- para_c_(_, TRP_I, TRP_O).

para__c(TRP_I, TRP_O) :- para__c(_, TRP_I, TRP_O).

para__d((HYP_A, HYP_B, GOAL_I), (HYP_A, HYP_NB, GOAL_O)) :- 
  dp(HYP_B, GOAL_I, HYP_NB, GOAL_O).

para_d_((HYP_A, HYP_B, GOAL_I), (HYP_NA, HYP_B, GOAL_O)) :- 
  dp(HYP_A, GOAL_I, HYP_NA, GOAL_O).

parad(TRP_I, TRP_O) :- 
  para_d_(TRP_I, TRP_O) ;
  para__d(TRP_I, TRP_O).

mate((HYP_A, HYP_B, GOAL)) :- mate(HYP_A, HYP_B, GOAL).

para_m((HYP_A, HYP_B, GOAL)) :- mate(HYP_A, HYP_B, GOAL).

para_s_((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  sp(HYP_A, GOAL, HYP_AN, GOAL_N). 
  
para__s((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  sp(HYP_B, GOAL, HYP_BN, GOAL_N). 

paras(X, Y) :- para_s_(X, Y) ; para__s(X, Y).

%para_c_((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_B, GOAL_N)) :- 
%  cp(HYP_A, _, GOAL, HYP_NA, GOAL_N).
%
%para__c((HYP_A, HYP_B, GOAL), (HYP_A, HYP_NB, GOAL_N)) :- 
%  cp(HYP_B, _, GOAL, HYP_NB, GOAL_N).

paracd(X, Y) :- para_cd(X, Y) ; para_dc(X, Y).

para_cd((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  cdp(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N).

para_dc((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  cdp(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).

paraab(X, Y, Z) :- para_ab(X, Y, Z) ; para_ba(X, Y, Z).

para_ab((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R).

para_ba((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  abpl(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

para(H2G) :- 
  % para_lc(H2G) -> true ;
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> para(H2G_N) ;
  paracd(H2G, H2G_N) -> para(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R) ->
  para(H2G_L), !, 
  para(H2G_R).

para_lc((HYP_A, HYP_B, GOAL)) :- 
  use_lc(HYP_A, GOAL) ;
  use_lc(HYP_B, GOAL).

para_mlc(X) :- para_m(X) ; para_lc(X). 

%%%%%%%%%%%%%%%% PARALLEL SWITCH DECOMPOSITION %%%%%%%%%%%%%%%%

para_f_(FORM, (PREM, CONC, GOAL), (PREM, HYP_N, GOAL_N), (HYP_P, CONC, GOAL_P)) :- 
  fp(FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P).

para__f(FORM, (PREM, CONC, GOAL), (PREM, HYP_P, GOAL_P), (HYP_N, CONC, GOAL_N)) :- 
  fp(FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P).

paraab_choose(TRP, TRP_B, TRP_A) :- 
  paraab(TRP, TRP_B, TRP_A) ;
  paraab_swap(TRP, TRP_B, TRP_A).

paraab_swap(TRP, TRP_B, TRP_A) :- 
  para_ab_swap(TRP, TRP_B, TRP_A) ;
  para_ba_swap(TRP, TRP_B, TRP_A).
  
para_ab_swap((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  abpr(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R).

para_ba_swap((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  abpr(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

% paraab_choose((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
%   abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ; 
%   abpr(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ; 
%   abpl(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R) ;
%   abpr(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

para_switch(H2G) :- 
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> para_switch(H2G_N) ;
  paracd(H2G, H2G_N) -> para_switch(H2G_N) ;
  paraab_choose(H2G, H2G_L, H2G_R),
  para_switch(H2G_L),  
  para_switch(H2G_R).




%%%%%%%%%%%%%%%% PARALLEL TF DECOMPOSITION %%%%%%%%%%%%%%%%

paratf_zero((HYP, _, GOAL)) :- 
  use_contra(HYP, GOAL).

paratf_one((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  (
    bp(HYP_A, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N) ;
    bp(HYP_A, GOAL, HYP_N, HYP_T, GOAL_N, GOAL_T) 
  ),
  use_contra(HYP_T, GOAL_T).

paratf_one((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  pluck([l, r], DIR, [FLP]), 
  hyp_sf(HYP_A, SF), 
  ab(DIR, SF, SF_T), 
  tauto(SF_T), 
  ap(HYP_A, FLP, GOAL, HYP_N, GOAL_N). 

paratf(H2G) :- 
  para_m(H2G) -> true ;
  paratf_zero(H2G) -> true ;
  paras(H2G, H2G_N) -> paratf(H2G_N) ;
  paracd(H2G, H2G_N) -> paratf(H2G_N) ;
  paratf_one(H2G, H2G_N) -> paratf(H2G_N) ;
  paraab_choose(H2G, H2G_L, H2G_R),
  paratf(H2G_L),  
  paratf(H2G_R).

parav_cd((HYP_A, HYP_B, GOAL_I), (HYP_NA, HYP_B, GOAL_O)) :- 
  cp_vac(HYP_A, GOAL_I, HYP_NA, GOAL_O) ;
  dp_vac(HYP_A, GOAL_I, HYP_NA, GOAL_O).

parav_cd((HYP_A, HYP_B, GOAL_I), (HYP_A, HYP_NB, GOAL_O)) :- 
  cp_vac(HYP_B, GOAL_I, HYP_NB, GOAL_O) ;
  dp_vac(HYP_B, GOAL_I, HYP_NB, GOAL_O).

parav(H2G) :- 
  para_m(H2G) *-> true ;
  paras(H2G, H2G_N) -> parav(H2G_N) ;
  parav_cd(H2G, H2G_N) -> parav(H2G_N) ;
  paracd(H2G, H2G_N) -> parav(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R), !,
  parav(H2G_L), !, 
  parav(H2G_R).

paral_cd((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  cdp_lax(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N) ;
  cdp_lax(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).

paral(H2G) :- 
  para_m(H2G) *-> true ;
  paras(H2G, H2G_N) -> paral(H2G_N) ;
  paral_cd(H2G, H2G_N) -> paral(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R), !,
  paral(H2G_L), !, 
  paral(H2G_R).

ppr(H2G) :- 
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> ppr(H2G_N) ;
  paracd(H2G, H2G_N) -> ppr(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R), 
  ppr(H2G_L), 
  ppr(H2G_R)
;
  ppr_a(H2G, H2G_N),
  ppr(H2G_N).



%%%%%%%%%%%%%%%% NEGATION NORMALIZATION %%%%%%%%%%%%%%%%

a_para((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  ap(HYP_A, l, GOAL, HYP_AN, GOAL_N) ;
  ap(HYP_A, r, GOAL, HYP_AN, GOAL_N).
  
ppr_a((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  ap(HYP_A, l, GOAL, HYP_AN, GOAL_N) ;
  ap(HYP_A, r, GOAL, HYP_AN, GOAL_N).

ppr_a((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  ap(HYP_B, l, GOAL, HYP_BN, GOAL_N) ;
  ap(HYP_B, r, GOAL, HYP_BN, GOAL_N).

fnnf(H2G) :- 
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> fnnf(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R) -> fnnf(H2G_L), !, fnnf(H2G_R) ;
  paracd(H2G, H2G_N) -> fnnf(H2G_N) ;
  H2G = (PREM, CONC, GOAL), 
  (
    type_hyp(c, PREM),
    bp(CONC, GOAL, CONC_L, CONC_R, GOAL_L, GOAL_R), 
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
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> vnnf(H2G_N) ;
  paracd(H2G, H2G_N) -> vnnf(H2G_N) ;
  iff_conv(H2G, H2G_N) -> vnnf(H2G_N) ;
  paraab(H2G, TRP_A, TRP_B), 
  vnnf(TRP_A), !,
  vnnf(TRP_B)
;
  ppr_a(H2G, H2G_N),
  vnnf(H2G_N). 


% vnnf(H2G) :- 
%   para_m(H2G) -> true ;
%   paras(H2G, H2G_N) -> vnnf(H2G_N) ;
%   paracd(H2G, H2G_N) -> vnnf(H2G_N) ;
%   ppr_a(H2G, H2G_N),
%   vnnf(H2G_N) 
% ;
%   paraab_choose(H2G, H2G_L, H2G_R),
%   vnnf(H2G_L),  
%   vnnf(H2G_R)
% ;
%   iff_conv(H2G, H2G_N), 
%   vnnf(H2G_N).



%%%%%%%%%%%%%%%% PARALLEL CLAUSAL DECOMPOSITION %%%%%%%%%%%%%%%%

prem_is_imp((PREM, _, _)) :- imp_hyp(PREM).

imp_hyp(HYP) :- 
  hyp_form(HYP, FORM),
  member(FORM, [$imp(_, _), $iff(_, _)]).

ap_repeat_aux(HYP, GOAL, HYP_L, HYP_R, NEW_GOAL) :- 
  \+ imp_hyp(HYP), 
  ap(HYP, l, GOAL, HYP_L, TEMP_GOAL),
  ap(HYP, r, TEMP_GOAL, HYP_R, NEW_GOAL).

ap_repeat(HYP, GOAL, HYPS, GOAL_N) :- 
  ap_repeat_aux(HYP, GOAL, HYP_L, HYP_R, GOAL0) -> 
  (
    ap_repeat(HYP_L, GOAL0, HYPS_L, GOAL1),
    ap_repeat(HYP_R, GOAL1, HYPS_R, GOAL_N), 
    append(HYPS_L, HYPS_R, HYPS)
  ) ;
  (HYPS = [HYP], GOAL_N = GOAL).

parac_b(HYP, GOAL, HGS) :- 
  (
    \+ imp_hyp(HYP),
    bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R)
  ) -> 
  (
    parac_b(HYP_L, GOAL_L, HGS_L),
    parac_b(HYP_R, GOAL_R, HGS_R),
    append(HGS_L, HGS_R, HGS)
  ) ;
  HGS = [([HYP], GOAL)].

para_clausal_two((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  (imp_hyp(HYP_A) ; imp_hyp(HYP_B)),
  (
    abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ;
    abpl(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R) 
  ).

% para_clausal_many_aux(HYP_A, ([HYP_B], GOAL), (HYP_A, HYP_B, GOAL)).

% para_clausal_many(TRP, TRPS) :- 
  % para_clausal_many(TRP, HYPS, HGS), 
  % maplist_cut(para_clausal_many_aux, HYPS, HGS, TRPS). 

para_clausal_many((HYP_A, HYP_B, GOAL), HYPS, HGS) :- 
  \+ imp_hyp(HYP_A),
  \+ imp_hyp(HYP_B),
  (
    type_hyp(a, HYP_A),
    ap_repeat(HYP_A, GOAL, HYPS, GOAL_T), 
    parac_b(HYP_B, GOAL_T, HGS)
  ;
    type_hyp(a, HYP_B),
    ap_repeat(HYP_B, GOAL, HYPS, GOAL_T), 
    parac_b(HYP_A, GOAL_T, HGS)
  ).

ppr(PREM, CONC, GOAL) :- 
  ap_repeat(PREM, GOAL, PREMS, TEMP), 
  parac_b(CONC, TEMP, HGS), 
  ppr(PREMS, HGS).

ppr(_, []) :- !. 

ppr([PREM | PREMS], [([CONC], GOAL) | HGS]) :- 
  mate(PREM, CONC, GOAL) -> 
  ppr(PREMS, HGS) 
;
  ppr(PREMS, [([CONC], GOAL) | HGS]).
  



% bfe_aux(_, []).
% bfe_aux(HYPS, [([HYP], GOAL) | HGS]) :- 
%   member(CMP, HYPS), 
%   bfe((HYP, CMP, GOAL)), !,
%   bfe_aux(HYPS, HGS).

para_clausal(PRVR, H2G) :- 
  para_lc(H2G) -> true ;
  para_m(H2G) 
;
  paras(H2G, H2G_N) -> para_clausal(PRVR, H2G_N) ;
  paracd(H2G, H2G_N) -> para_clausal(PRVR, H2G_N) ;
  para_clausal_two(H2G, H2G_L, H2G_R) -> 
  para_clausal(PRVR, H2G_L), 
  para_clausal(PRVR, H2G_R)
;
  para_clausal_many(H2G, HS, HGS) -> 
  para_clausal_aux(PRVR, HS, HGS).

para_clausal_aux(_, _, []).

para_clausal_aux(PRVR, HYPS, [([HYP], GOAL) | HGS]) :- 
  member(CMP, HYPS), 
  para_clausal(PRVR, (HYP, CMP, GOAL)),
  para_clausal_aux(PRVR, HYPS, HGS).

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

maplist_count(_, CNT, TTL, [], CNT, TTL).
maplist_count(GOAL, CNT_I, TTL_I, [ELEM | LIST], CNT_O, TTL_O) :- 
  atomics_to_string(["PASSED/TOTAL = ", CNT_I, "/", TTL_I, "\n"], STRING),
  write(STRING),
  (call(GOAL, ELEM) -> num_succ(CNT_I, CNT_T) ; CNT_I = CNT_T),
  num_succ(TTL_I, TTL_T), 
  maplist_count(GOAL, CNT_T, TTL_T, LIST, CNT_O, TTL_O).

% tstp_name(PRVR, TSTP, NAME) :- 
%   atom_concat(PRVR, TEMP0, TSTP), 
%   atom_concat('s/', TEMP1, TEMP0), 
%   atom_concat(NAME, '.tstp', TEMP1).
% 
% tesc_name(PRVR, TESC, NAME) :- 
%   atom_concat(PRVR, TEMP0, TESC), 
%   atom_concat('e/', TEMP1, TEMP0), 
%   atom_concat(NAME, '.tesc', TEMP1).

% names_failed(PRVR, NAMES) :- 
%   atom_concat(PRVR, f, PATH),
%   file_strings(PATH, STRS),
%   maplist_cut(string_to_atom, STRS, NAMES).
% 
% names_archived(PRVR, NAMES) :- 
%   atom_concat(PRVR, a, PATH),
%   rec_path_filenames(PATH, PATHS),
%   maplist_cut(path_name, PATHS, NAMES).

get_solution_names(PRVR, NAMES) :- 
  atom_concat(PRVR, sol, PATH),
  rec_path_filenames(PATH, PATHS),
  maplist_cut(path_name, PATHS, NAMES).

names_proven(PRVR, NAMES) :- 
  atom_concat(PRVR, prf, PATH),
  rec_path_filenames(PATH, PATHS),
  maplist_cut(path_name, PATHS, NAMES).

name_tptp(NAME, TPTP) :- 
  tptp_directory(PATH),
  atom_codes(NAME, [C0, C1, C2 | _]),
  atom_codes(CAT, [C0, C1, C2]),  
  atomic_list_concat([PATH, 'Problems/', CAT, "/", NAME, ".p"], TPTP).
  
path_cat_id(Path, Cat, ID) :- 
  atom_codes(Path, Codes0), 
  append(_, [47 | Codes1], Codes0),
  \+ member(47, Codes1), 
  append([C0, C1, C2 | Rest], [46, 112], Codes1),
  string_codes(Cat, [C0, C1, C2]),
  string_codes(ID, Rest).

path_name(PATH, NAME) :- 
  atom_codes(PATH, TEMP0), 
  append(_, [47 | TEMP1], TEMP0),
  \+ member(47, TEMP1), !, 
  append(TEMP2, [46 | TEMP3], TEMP1),
  \+ member(46, TEMP3), !, 
  atom_codes(NAME, TEMP2).

body_lits($or(FORM_L, FORM_R), LITS, TAIL) :- !, 
  body_lits(FORM_L, LITS, TEMP), 
  body_lits(FORM_R, TEMP, TAIL).

body_lits(LIT, [LIT | TAIL], TAIL) :- literal(LIT).

print_size(PATH) :- 
  atomic_concat("wc -c ", PATH, CMD),
  shell(CMD, _).

trace_if_debug(OPTS) :-
  member('-debug', OPTS) ->
  guitracer,
  trace 
;
  true.

try(PRED, [ELEM | LIST], RST) :- 
  call(PRED, ELEM, RST) -> 
  true ;
  try(PRED, LIST, RST).
  
path_cat(PATH, CAT) :- 
  atom_codes(PATH, [C0, C1, C2 | _]), 
  string_codes(CAT, [C0, C1, C2]).

get_context(PROB, IDS, CTX) :- 
  maplist(prob_id_hyp(PROB), IDS, CTX).

redirect_id(ON, OLD, NEW) :- 
  get_assoc(OLD, ON, NUM) -> 
  mk_par(NUM, [], NEW)
;
  NEW = OLD.

axiomatic(TYPE) :- member(TYPE, [lemma, axiom, hypothesis, conjecture, negated_conjecture]).

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

map_form(GOAL, DTH, FORM_I, FORM_O) :- 
  FORM_I =.. [REL | TERMS_I], 
  maplist_cut(call(GOAL, DTH), TERMS_I, TERMS_O),
  FORM_O =.. [REL | TERMS_O]. 

para_e1(H2G) :- 
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> para_e1(H2G_N) ;
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
  ap_repeat(HYP_A, GOAL, HYPS, TEMP), 
  clause_ab_aux(PARA, DIR, HYPS, HYP_B, TEMP, []).
  
clause_ab_aux(PARA, DIR, HYPS, HYP, GOAL, REM) :-
  cp(HYP, _, GOAL, HYP_N, GOAL_N), !, 
  clause_ab_aux(PARA, DIR, HYPS, HYP_N, GOAL_N, REM).

clause_ab_aux(PARA, l, [HYP_A | HYPS], HYP_B, GOAL, HYPS) :-
  call(PARA, (HYP_A, HYP_B, GOAL)), !. 
  
clause_ab_aux(PARA, r, [HYP_A | HYPS], HYP_B, GOAL, HYPS) :-
  call(PARA, (HYP_B, HYP_A, GOAL)), !. 

clause_ab_aux(PARA, DIR, HYPS, HYP_B, GOAL, REM) :-
  bp(HYP_B, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  clause_ab_aux(PARA, DIR, HYPS, HYP_L, GOAL_L, TEMP), !, 
  clause_ab_aux(PARA, DIR, TEMP, HYP_R, GOAL_R, REM).
   
   % (HYP_A, HYP_B, GOAL)).




para_e2(H2G) :- 
  para_m(H2G) -> true ;
  paras(H2G, H2G_N) -> para_e2(H2G_N) ;
  parad(H2G, H2G_N) -> para_e2(H2G_N) ;
  para_c_(H2G, H2G_N) -> para_e2(H2G_N) ;
  paraab(H2G, H2G_L, H2G_R) ->
  para_e2(H2G_L), !, 
  para_e2(H2G_R).

pick_mate(HYPS_A, (HYPS_B, GOAL)) :- 
  member(HYP_A, HYPS_A), 
  member(HYP_B, HYPS_B), 
  mate(HYP_A, HYP_B, GOAL).

map_signed_atoms(_, []).

map_signed_atoms(HYPS, [([HYP], GOAL) | HGS]) :- 
  use_lc(HYP, GOAL) ->
  map_signed_atoms(HYPS, HGS) ;
  ground(HYP) -> 
  (pick_mate(HYPS, ([HYP], GOAL)), !, map_signed_atoms(HYPS, HGS)) ;
  (pick_mate(HYPS, ([HYP], GOAL)),  map_signed_atoms(HYPS, HGS)). 

sbsm(PREM, CONC, GOAL) :-
  many_nb([a, d, s], [CONC], GOAL, HYPS, TEMP), 
  (
    (member(HYP, HYPS), use_lc(HYP, TEMP)) -> 
    true
  ;
    many([b, c, s], ([PREM], TEMP), HGS), 
    map_signed_atoms(HYPS, HGS)
  ).

relabel(SOL_I, SOL_O) :- 
  empty_assoc(EMP),  
  relabel_sol((EMP, EMP), EMP, 0, SOL_I, SOL_O).

try_del_assoc(KEY, ASC_I, ASC_O) :- 
  del_assoc(KEY, ASC_I, _, ASC_O) ->
  true   
;
  ASC_O = ASC_I.

relabel_inst(DICT, NI, _, del(NAME), DICT, NI_N, del(ID)) :-    
  redirect_id(NI, NAME, ID), 
  try_del_assoc(NAME, NI, NI_N).

relabel_inst(DICT, NI, CNT, add(NAME, FORM), DICT, NI_N, add(NORM)) :-    
  resymb_form(DICT, FORM, NORM),
  put_assoc(NAME, NI, CNT, NI_N).

relabel_inst((RDICT, FDICT), NI, CNT, add([def, REL, ARI], NAME, FORM), (RDICT_N, FDICT), NI_N, add(NORM)) :-    
  put_assoc(NAME, NI, CNT, NI_N), 
  put_assoc((REL, ARI), RDICT, CNT, RDICT_N),
  resymb_form((RDICT_N, FDICT), FORM, NORM).

relabel_inst((RDICT, FDICT), NI, CNT, skm(FUN, ARI, NAME, FORM), (RDICT, FDICT_N), NI_N, add(NORM)) :-    
  put_assoc(NAME, NI, CNT, NI_N), 
  put_assoc((FUN, ARI), FDICT, CNT, FDICT_N),
  resymb_form((RDICT, FDICT_N), FORM, NORM).

relabel_inst(DICT, NI, CNT, inf(HINT, NAMES, NAME, FORM), DICT, NI_N, inf(HINT, IDS, NORM)) :-    
  (
    NAMES = $orig -> 
    IDS = $orig 
  ;
    maplist_cut(redirect_id(NI), NAMES, IDS)
  ),
  put_assoc(NAME, NI, CNT, NI_N),
  resymb_form(DICT, FORM, NORM).

relabel_sol(DICT, NI, CNT, [INST | SOL], [INST_N | SOL_N]) :- 
  relabel_inst(DICT, NI, CNT, INST, DICT_N, NI_N, INST_N),   
  num_succ(CNT, SCNT),
  relabel_sol(DICT_N, NI_N, SCNT, SOL, SOL_N). 

relabel_sol(_, _, _, [], []).

eqr_aux(_, ([HYP], GOAL)) :- use_lc(HYP, GOAL), !.
eqr_aux(_, ([HYP], GOAL)) :- 
  HYP = (_, $neg(_ = _)),
  eq_refl(HYP, GOAL).
eqr_aux(HYPS, HG) :- pick_mate(HYPS, HG).

eqr(PREM, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T), 
  many([b, c, s], ([PREM], GOAL_T), HGS), !,
  maplist(eqr_aux(HYPS), HGS).

cf_lits_core($or(CLA_L, CLA_R), LITS) :- !, 
  cf_lits_core(CLA_L, LITS_L), 
  cf_lits_core(CLA_R, LITS_R), 
  append(LITS_L, LITS_R, LITS).
  
cf_lits_core(LIT, [LIT]). 

cf_lits($false, []) :- !. 
cf_lits(FORM, LITS) :-  
  cf_lits_core(FORM, LITS).


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

tauto($pos(FORM)) :- bool_norm(FORM, $true).
tauto($neg(FORM)) :- bool_norm(FORM, $false).

esimp_not($false, $true) :- !.
esimp_not($true, $false) :- !.
esimp_not($not(FORM), FORM) :- !.
esimp_not(FORM, $not(FORM)).

esimp_qtf(_, $true, $true) :- !.
esimp_qtf(_, $false, $false) :- !.
esimp_qtf(QTF, FORM_I, FORM_O) :-
  no_fv_form(0, FORM_I) -> 
  FORM_O = FORM_I 
;
  apply_uop(QTF, FORM_I, FORM_O).

esimp_bct(iff, FORM, $true, FORM) :- !.
esimp_bct(iff, FORM, $false, $not(FORM)) :- !.
esimp_bct(iff, $true, FORM, FORM) :- !.
esimp_bct(iff, $false, FORM, $not(FORM)) :- !.
esimp_bct(iff, FORM_A, FORM_B, FORM) :- !, 
(
  FORM_A == FORM_B -> 
  FORM = $true
;
  FORM = $iff(FORM_A, FORM_B) 
).

esimp_bct(imp, $false, _, $true) :- !.
esimp_bct(imp, $true, FORM, FORM) :- !.
esimp_bct(imp, _, $true, $true) :- !.
esimp_bct(imp, FORM, $false, $not(FORM)) :- !.
esimp_bct(imp, FORM_A, FORM_B, $true) :- FORM_A == FORM_B, !.
esimp_bct(imp, FORM_A, FORM_B, $imp(FORM_A, FORM_B)) :- !.

esimp_bct(and, $false, _, $false) :- !.
esimp_bct(and, _, $false, $false) :- !.
esimp_bct(and, $true, FORM, FORM) :- !.
esimp_bct(and, FORM, $true, FORM) :- !.
esimp_bct(and, FORM_L, FORM_R, FORM_L) :- FORM_L == FORM_R, !.
esimp_bct(and, FORM_L, FORM_R, $and(FORM_L, FORM_R)) :- !.

esimp_bct(or, $true, _, $true) :- !.
esimp_bct(or, _, $true, $true) :- !.
esimp_bct(or, $false, FORM, FORM) :- !.
esimp_bct(or, FORM, $false, FORM) :- !.
esimp_bct(or, FORM_L, FORM_R, FORM_L) :- FORM_L == FORM_R, !.
esimp_bct(or, FORM_L, FORM_R, $or(FORM_L, FORM_R)) :- !.

% esimp_bct(BCT, FORM_A, FORM_B, FORM) :- 
%   apply_bop(BCT, FORM_A, FORM_B, FORM).
  
esimp($not(FORM), NORM) :- !, 
  esimp(FORM, TEMP), 
  esimp_not(TEMP, NORM). 
 
esimp(FORM, NORM) :- 
  decom_bct(FORM, BCT, FORM_A, FORM_B), !,
  esimp(FORM_A, NORM_A), 
  esimp(FORM_B, NORM_B),
  esimp_bct(BCT, NORM_A, NORM_B, NORM).

esimp(FORM, NORM) :- 
  decom_qtf(FORM, QTF, BODY), !, 
  esimp(BODY, TEMP),
  esimp_qtf(QTF, TEMP, NORM).

esimp(FORM, FORM).

quote_par_aux(IN, OUT) :- 
  re_replace("([^'])@([0-9]+)([^'])"/g, "$1'@$2'$3", IN, TEMP),
  (
    IN = TEMP -> 
    OUT = TEMP   
  ;
    quote_par_aux(TEMP, OUT)
  ).

quote_par(SRC, TGT) :- 
  read_line_to_string(SRC, LINE), 
  (
    LINE = end_of_file -> true 
  ; 
    quote_par_aux(LINE, NORM),
    write(TGT, NORM), 
    write(TGT, "\n"), 
    quote_par(SRC, TGT)
  ).

map_var(GOAL, #(NUM), TERM) :- !, 
  call(GOAL, NUM, TERM).
map_var(GOAL, ^(FUN, TERMS_I), ^(FUN, TERMS_O)) :- !, 
  maplist_cut(map_var(GOAL), TERMS_I, TERMS_O).
map_var(GOAL, TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(map_var(GOAL), TERMS_I, TERMS_O),
  TERM_O =.. [FUN | TERMS_O]. 
  
decr_vdx_form(FORM, NORM) :- 
  map_form(decr_vdx_term, 0, FORM, NORM).
decr_vdx_term(DEP, TERM_I, TERM_O) :- 
  map_var(decr_vdx(DEP), TERM_I, TERM_O).

decr_vdx(DTH, NUM, #(NUM)) :- NUM < DTH.
decr_vdx(DTH, NUM, #(PRED)) :- 
  DTH < NUM, num_pred(NUM, PRED). 

dist_qtf_bct(fa, and).
dist_qtf_bct(ex, or).

dist_qtf(_, FORM, NORM) :-
  decr_vdx_form(FORM, NORM), !.

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

msg(PTRN, ARGS) :-
  % write(" ────────────────────────────────────────────────────────────────── "), 
  write("                                                                      > "), 
  format(PTRN, ARGS),
  write("\n\n").

msg(STR) :-
  % write(" ────────────────────────────────────────────────────────────────── "), 
  write("                                                                      > "), 
  write(STR),
  write("\n\n").

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

path_atoms(PATH, ATOMS) :- 
  open(PATH, read, STRM), 
  stream_strings(STRM, STRS),
  maplist_cut(string_to_atom, STRS, ATOMS).

record_list(PATH, LIST) :- 
  open(PATH, write, STRM), 
  write_list(STRM, LIST),
  close(STRM).

record_paths(PATH, PATHS) :- 
  maplist_cut(path_name, PATHS, NAMES), 
  record_list(PATH, NAMES).

atom_firstchar(ATOM, CH) :-
  atom_codes(ATOM, [CODE | _]), 
  char_code(CH, CODE).

write_term_punct(STRM, TERM) :-
  write_term(STRM, TERM, [fullstop(true), nl(true), quoted(true)]).

countall(TMP, GOAL, CNT) :- 
  findall(TMP, GOAL, BAG),
  length(BAG, CNT).