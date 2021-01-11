:- [basic].

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

write_offset(STRM, OFS) :-
  offset(OFS, STR),
  write(STRM, STR).

get_from_bch(BCH, ID, FORM) :- 
  length(BCH, LTH), 
  num_pred(LTH, PRED), 
  NUM is PRED - ID, 
  get_from_bch_aux(BCH, NUM, FORM).
  
get_from_bch_aux([FORM | _], 0, FORM) :- !.
get_from_bch_aux([_ | BCH], NUM, FORM) :-
  num_pred(NUM, PRED), 
  get_from_bch_aux(BCH, PRED, FORM).
  
bch_form([], none).
bch_form([FORM | _], FORM).

annot_prf(PROB, BCH, a(PID, DIR, PRF), a(LAST, PID, DIR, ANT)) :- 
  bch_form(BCH, LAST), 
  get_from_bch(BCH, PID, PREM), 
  break_a(DIR, PREM, CONC), 
  annot_prf(PROB, [CONC | BCH], PRF, ANT).
  
annot_prf(PROB, BCH, b(PID, PRF_A, PRF_B), b(FORM, PID, ANT_A, ANT_B)) :- 
  bch_form(BCH, FORM), 
  get_from_bch(BCH, PID, PREM), 
  break_b(PREM, CONC_A, CONC_B), 
  annot_prf(PROB, [CONC_A | BCH], PRF_A, ANT_A),
  annot_prf(PROB, [CONC_B | BCH], PRF_B, ANT_B).

annot_prf(PROB, BCH, c(PID, TERM, PRF), c(FORM, PID, TERM, ANT)) :- 
  bch_form(BCH, FORM), 
  get_from_bch(BCH, PID, PREM), 
  break_c(TERM, PREM, CONC), 
  annot_prf(PROB, [CONC | BCH], PRF, ANT).

annot_prf(PROB, BCH, d(PID, PRF), d(FORM, PID, ANT)) :- 
  bch_form(BCH, FORM), 
  get_from_bch(BCH, PID, PREM), 
  length(BCH, CNT),
  break_d(CNT, PREM, CONC), 
  annot_prf(PROB, [CONC | BCH], PRF, ANT).

annot_prf(PROB, BCH, n(PID, PRF), n(FORM, PID, ANT)) :- 
  bch_form(BCH, FORM), 
  get_from_bch(BCH, PID, PREM), 
  break_n(PREM, CONC), 
  annot_prf(PROB, [CONC | BCH], PRF, ANT).

annot_prf(PROB, BCH, s(FORM, PRF_A, PRF_B), s(LAST, FORM, ANT_A, ANT_B)) :- 
  bch_form(BCH, LAST), 
  annot_prf(PROB, [~ FORM | BCH], PRF_A, ANT_A),
  annot_prf(PROB, [FORM | BCH], PRF_B, ANT_B).

annot_prf(PROB, BCH, p(NAME, PRF), p(LAST, NAME, ANT)) :- 
  bch_form(BCH, LAST), 
  get_assoc(NAME, PROB, FORM),
  annot_prf(PROB, [FORM | BCH], PRF, ANT).

annot_prf(PROB, BCH, t(FORM, PRF), t(LAST, FORM, ANT)) :- 
  bch_form(BCH, LAST), 
  annot_prf(PROB, [FORM | BCH], PRF, ANT).

annot_prf(_, BCH, x(PID, NID), x(LAST, PID, NID)) :- 
  bch_form(BCH, LAST). 

formatnl(STRM, PAT, ARGS) :- format(STRM, PAT, ARGS), nl(STRM).
  
printnl(true, PAT, ARGS) :- format(PAT, ARGS), nl.
printnl(false, _, _).

write_ant(STRM, OFS, a(LAST, PID, DIR, ANT)) :- 
  num_succ(OFS, SUCC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ A ~w ~w ]]", [OFS_STR, LAST, PID, DIR]), 
  write_ant(STRM, SUCC, ANT), !.  

write_ant(STRM, OFS, b(LAST, PID, ANT_A, ANT_B)) :- 
  num_succ(OFS, SUCC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ B ~w ]]", [OFS_STR, LAST, PID]), 
  write_ant(STRM, SUCC, ANT_A), !,
  write_ant(STRM, SUCC, ANT_B), !.

write_ant(STRM, OFS, c(LAST, PID, TERM, ANT)) :- 
  num_succ(OFS, SUC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ C ~w ~w ]]", [OFS_STR, LAST, PID, TERM]), 
  write_ant(STRM, SUC, ANT), !.   
  
write_ant(STRM, OFS, d(LAST, PID, ANT)) :- 
  num_succ(OFS, SUC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ D ~w ]]", [OFS_STR, LAST, PID]), 
  write_ant(STRM, SUC, ANT), !.   

write_ant(STRM, OFS, n(LAST, PID, ANT)) :- 
  num_succ(OFS, SUC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ N ~w ]]", [OFS_STR, LAST, PID]), 
  write_ant(STRM, SUC, ANT), !.   

write_ant(STRM, OFS, s(LAST, FORM, ANT_A, ANT_B)) :-
  num_succ(OFS, SUC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ S ~w ]]", [OFS_STR, LAST, FORM]), 
  write_ant(STRM, SUC, ANT_A), 
  write_ant(STRM, SUC, ANT_B), !.   

write_ant(STRM, OFS, p(LAST, NAME, ANT)) :- 
  num_succ(OFS, SUC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ P ~w ]]", [OFS_STR, LAST, NAME]), 
  write_ant(STRM, SUC, ANT), !.   

write_ant(STRM, OFS, t(LAST, FORM, ANT)) :- 
  num_succ(OFS, SUC), 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ T ~w ]]", [OFS_STR, LAST, FORM]), 
  write_ant(STRM, SUC, ANT), !.   
  
write_ant(STRM, OFS, x(LAST, PID, NID)) :- 
  offset(OFS, OFS_STR),
  formatnl(STRM, "~w ~w [[ X ~w ~w ]]", [OFS_STR, LAST, PID, NID]).

term_pp(#NUM, PP) :- !, 
  number_string(NUM, STR),
  string_concat("#", STR, PP).
term_pp((FUN $ TERMS), PP) :- 
  functor_pp(FUN, FUN_PP), 
  terms_pp(TERMS, TERMS_PP),
  string_concat(FUN_PP, TERMS_PP, PP).

form_pp((REL $ TERMS), PP) :-
  functor_pp(REL, REL_PP), 
  terms_pp(TERMS, TERMS_PP),
  string_concat(REL_PP, TERMS_PP, PP).
form_pp(tt, "⊤").
form_pp(ff, "⊥").
form_pp(~ FORM, PP) :-
  form_pp(FORM, SUB_PP), 
  string_concat("¬ ", SUB_PP, PP).
form_pp(! FORM, PP) :-
  form_pp(FORM, SUB_PP), 
  string_concat("∀ ", SUB_PP, PP).
form_pp(? FORM, PP) :-
  form_pp(FORM, SUB_PP), 
  string_concat("∃ ", SUB_PP, PP).
form_pp((FORM_A \/ FORM_B), PP) :-
  form_pp(FORM_A, PP_A), 
  form_pp(FORM_B, PP_B), 
  atomics_to_string(["(", PP_A, " ∨ ", PP_B, ")"], PP).
form_pp((FORM_A /\ FORM_B), PP) :-
  form_pp(FORM_A, PP_A), 
  form_pp(FORM_B, PP_B), 
  atomics_to_string(["(", PP_A, " ∧ ", PP_B, ")"], PP).
form_pp((FORM_A => FORM_B), PP) :-
  form_pp(FORM_A, PP_A), 
  form_pp(FORM_B, PP_B), 
  atomics_to_string(["(", PP_A, " → ", PP_B, ")"], PP).
form_pp((FORM_A <> FORM_B), PP) :-
  form_pp(FORM_A, PP_A), 
  form_pp(FORM_B, PP_B), 
  atomics_to_string(["(", PP_A, " ↔ ", PP_B, ")"], PP).

terms_pp(TERMS, PP) :-
  cmap(term_pp, TERMS, PPS), 
  atomics_to_string(PPS, ',', BODY_PP),
  atomics_to_string(["(", BODY_PP, ")"], PP).
  
functor_pp(#NUM, PP) :- !, 
  number_string(NUM, STR), 
  atomics_to_string(["#", STR], PP).
functor_pp(STR, STR) :- string(STR).
  
dir_pp(lft, "<").
dir_pp(rgt, ">").

check(BCH, CNT, SUC, 'A', PRINT, PAD, STRM) :- 
  get_num(STRM, ID),  
  get_dir(STRM, DIR),
  dir_pp(DIR, DIR_PP),
  printnl(PRINT, "~w~w : A / ~w / ~w", [PAD, CNT, ID, DIR_PP]), 
  get_assoc(ID, BCH, PREM),
  break_a(DIR, PREM, CONC), 
  form_pp(CONC, PP),
  printnl(PRINT, "~w└─ ~w ", [PAD, PP]), 
  string_concat(PAD, "   ", PAD_N),
  put_assoc(CNT, BCH, CONC, BCH_N), !,
  check(BCH_N, SUC, PRINT, PAD_N, STRM), !.

check(BCH, CNT, SUC, 'B', PRINT, PAD, STRM) :- 
  get_num(STRM, ID), 
  printnl(PRINT, "~w~w : B / ~w", [PAD, CNT, ID]), 
  get_assoc(ID, BCH, PREM),
  break_b(PREM, CONC_A, CONC_B),
  string_concat(PAD, "│  ", PAD_A),
  string_concat(PAD, "   ", PAD_B),
  
  put_assoc(CNT, BCH, CONC_A, BCH_A), 
  put_assoc(CNT, BCH, CONC_B, BCH_B), 

  form_pp(CONC_A, PP_A),
  printnl(PRINT, "~w├─ ~w ", [PAD, PP_A]), !,
  check(BCH_A, SUC, PRINT, PAD_A, STRM), !,

  form_pp(CONC_B, PP_B),
  printnl(PRINT, "~w└─ ~w ", [PAD, PP_B]), !,
  check(BCH_B, SUC, PRINT, PAD_B, STRM), !.
  
check(BCH, CNT, SUC, 'C', PRINT, PAD, STRM) :- 
  get_num(STRM, ID), 
  get_term(STRM, TERM), 
  term_pp(TERM, TERM_PP),
  printnl(PRINT, "~w~w : C / ~w / ~w", [PAD, CNT, ID, TERM_PP]), 

  get_assoc(ID, BCH, PREM),
  break_c(TERM, PREM, CONC),
  string_concat(PAD, "   ", PAD_N),
  put_assoc(CNT, BCH, CONC, BCH_N), 

  form_pp(CONC, CONC_PP),
  printnl(PRINT, "~w└─ ~w ", [PAD, CONC_PP]), !,
  check(BCH_N, SUC, PRINT, PAD_N, STRM), !.

check(BCH, CNT, SUC, 'D', PRINT, PAD, STRM) :- 
  get_num(STRM, ID), 
  printnl(PRINT, "~w~w : D / ~w", [PAD, CNT, ID]), 

  get_assoc(ID, BCH, PREM),
  break_d(CNT, PREM, CONC),
  string_concat(PAD, "   ", PAD_N),
  put_assoc(CNT, BCH, CONC, BCH_N), 

  form_pp(CONC, CONC_PP),
  printnl(PRINT, "~w└─ ~w", [PAD, CONC_PP]), !,
  check(BCH_N, SUC, PRINT, PAD_N, STRM), !.

check(BCH, CNT, SUC, 'N', PRINT, PAD, STRM) :- 
  get_num(STRM, ID), 
  printnl(PRINT, "~w~w : N / ~w", [PAD, CNT, ID]), 

  get_assoc(ID, BCH, PREM),
  break_n(PREM, CONC),
  string_concat(PAD, "   ", PAD_N),
  put_assoc(CNT, BCH, CONC, BCH_N), 

  form_pp(CONC, CONC_PP),
  printnl(PRINT, "~w└─ ~w ", [PAD, CONC_PP]), !,
  check(BCH_N, SUC, PRINT, PAD_N, STRM), !.
  
check(BCH, CNT, SUC, 'S', PRINT, PAD, STRM) :- 
  get_form(STRM, FORM), 
  form_pp(FORM, PP),
  printnl(PRINT, "~w~w : S / ~w", [PAD, CNT, PP]), 

  string_concat(PAD, "│  ", PAD_A),
  string_concat(PAD, "   ", PAD_B),
  put_assoc(CNT, BCH, ~ FORM, BCH_A), 
  put_assoc(CNT, BCH, FORM, BCH_B), 

  printnl(PRINT, "~w├─ ¬ ~w", [PAD, PP]), !,
  check(BCH_A, SUC, PRINT, PAD_A, STRM), !,

  printnl(PRINT, "~w└─ ~w", [PAD, PP]), !,
  check(BCH_B, SUC, PRINT, PAD_B, STRM), !.
  
check(BCH, CNT, SUC, 'T', PRINT, PAD, STRM) :- 
  get_form(STRM, FORM), 
  form_pp(FORM, PP),
  printnl(PRINT, "~w~w : T / ~w", [PAD, CNT, PP]), 

  string_concat(PAD, "   ", PAD_N),
  put_assoc(CNT, BCH, FORM, BCH_N), 

  printnl(PRINT, "~w└ ~w", [PAD, PP]), !,
  check(BCH_N, SUC, PRINT, PAD_N, STRM), !.
  
check(BCH, CNT, _, 'X', PRINT, PAD, STRM) :- 
  get_num(STRM, NID), 
  get_num(STRM, PID),
  get_assoc(NID, BCH, ~ FORM_N),
  get_assoc(PID, BCH, FORM_P),
  (
    FORM_P == FORM_N ->
    true 
  ;  
    format("~w != ~w", [FORM_N, FORM_P]),
    false
  ), !,
  printnl(PRINT, "~w~w : X / ~w / ~w", [PAD, CNT, NID, PID]), !.

check(BCH, CNT, PRINT, PAD, STM) :- 
  num_succ(CNT, SUC),
  get_char(STM, CH), !,
  check(BCH, CNT, SUC, CH, PRINT, PAD, STM), !.

main([PROB, PRF]) :- 
  tptp_bch(PROB, BCH, _, SIZE), !,
  open(PRF, read, STM, [encoding(octet)]), !,
  check(BCH, SIZE, false, "", STM), !,
  close(STM), !,
  writeln("Proof verified (kernel = PTTV)."), !,
  true.