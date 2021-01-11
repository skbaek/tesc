:- [basic].

print_on(NUM, INP, STR) :- 
  NUM = INP -> write(STR) ; true.

format_on(NUM, INP, PAT, ARGS) :- 
  NUM = INP -> format(PAT, ARGS) ; true.

update_fi_ftr(OFF, TAB, #NUM_I, #NUM_O) :- !, update_fi(OFF, TAB, NUM_I, NUM_O). 
update_fi_ftr(_, _, FTR, FTR).

update_fi_form(_, _, FORM, FORM) :- log_const(FORM), !.
update_fi_form(OFF, TAB, ~ FORM, ~ FORM_N) :- !,
  update_fi_form(OFF, TAB, FORM, FORM_N).
update_fi_form(OFF, TAB, FORM_I, FORM_O) :-
  break_qtf(FORM_I, QTF, SUB_I), !, 
  update_fi_form(OFF, TAB, SUB_I, SUB_O), 
  apply_uct(QTF, SUB_O, FORM_O). 
update_fi_form(OFF, TAB, FORM, FORM_N) :- 
  break_bct(FORM, BCT, FORM_A, FORM_B), !, 
  update_fi_form(OFF, TAB, FORM_A, FORM_AN),
  update_fi_form(OFF, TAB, FORM_B, FORM_BN),
  apply_bct(BCT, FORM_AN, FORM_BN, FORM_N). 
update_fi_form(OFF, LOG, (REL_I $ TERMS_I), (REL_O $ TERMS_O)) :- 
  update_fi_ftr(OFF, LOG, REL_I, REL_O), !,
  cmap(update_fi_term(OFF, LOG), TERMS_I, TERMS_O).

update_fi_term(_, _, #NUM, #NUM).
update_fi_term(OFF, LOG, (FUN_I $ TERMS_I), (FUN_O $ TERMS_O)) :- !, 
  update_fi_ftr(OFF, LOG, FUN_I, FUN_O), !,
  cmap(update_fi_term(OFF, LOG), TERMS_I, TERMS_O).

update_fi(OFF, [], OLD_FI, NEW_FI) :- NEW_FI is OFF + OLD_FI. 
update_fi(_, [(OLD, _) | _], OLD, _) :- !, throw(p_and_d_rule_superposed).
update_fi(OFF, [(OLD, _) | LOG], OLD_FI, NEW_FI) :- 
  OLD < OLD_FI, !, 
  length(LOG, LEN), 
  NEW_FI is (OFF + OLD_FI) - (LEN + 1).
update_fi(OFF, [(OLD, _) | LOG], OLD_FI, NEW_FI) :- 
  OLD > OLD_FI, 
  update_fi(OFF, LOG, OLD_FI, NEW_FI).

update_id(_, [(OLD, NEW) | _], OLD, NEW) :- !.
update_id(OFF, [(OLD, _) | LOG], IN, OUT) :- 
  OLD < IN, !, 
  length(LOG, LEN), 
  OUT is (OFF + IN) - (LEN + 1).
update_id(OFF, [(OLD, _) | LOG], IN, OUT) :- 
  OLD > IN, 
  update_id(OFF, LOG, IN, OUT).
update_id(OFF, [], IN, OUT) :- OUT is OFF + IN. 

pass_id(OFF, LOG, IN, OUT) :- 
  get_num(IN, OLD),  
  update_id(OFF, LOG, OLD, NEW),
  put_num(OUT, NEW).

bch_ch('A', TAB, OFF, LOG, _, SUC, IN, OUT) :- 
  pass_id(OFF, LOG, IN, OUT),  
  get_dir(IN, DIR),
  put_dir(OUT, DIR), !,
  bch(TAB, OFF, LOG, SUC, IN, OUT).

bch_ch('B', TAB, OFF, LOG, _, SUC, IN, OUT) :- 
  pass_id(OFF, LOG, IN, OUT), !,
  bch(TAB, OFF, LOG, SUC, IN, OUT), !,
  bch(TAB, OFF, LOG, SUC, IN, OUT).

bch_ch('C', TAB, OFF, LOG, _, SUC, IN, OUT) :- 
  pass_id(OFF, LOG, IN, OUT), 
  get_term(IN, TERM), 
  update_fi_term(OFF, LOG, TERM, NEW_TERM),
  put_term(OUT, NEW_TERM), !,
  bch(TAB, OFF, LOG, SUC, IN, OUT).

bch_ch('D', TAB, OFF, LOG, _, SUC, IN, OUT) :- 
  pass_id(OFF, LOG, IN, OUT), !,
  bch(TAB, OFF, LOG, SUC, IN, OUT).

bch_ch('N', TAB, OFF, LOG, _, SUC, IN, OUT) :- 
  pass_id(OFF, LOG, IN, OUT), !,
  bch(TAB, OFF, LOG, SUC, IN, OUT).

bch_ch('P', TAB, OFF, LOG, NUM, SUC, IN, OUT) :- 
  get_string(IN, NAME), 
  get_assoc(NAME, TAB, ID), !, 
  bch(TAB, OFF, [(NUM, ID) | LOG], SUC, IN, OUT).

bch_ch('S', TAB, OFF, LOG, _, SUC, IN, OUT) :- 
  get_form(IN, FORM), 
  update_fi_form(OFF, LOG, FORM, NEW_FORM),
  put_form(OUT, NEW_FORM), !,  
  bch(TAB, OFF, LOG, SUC, IN, OUT), !,
  bch(TAB, OFF, LOG, SUC, IN, OUT).

bch_ch('T', TAB, OFF, LOG, _, SUC, IN, OUT) :- 
  get_form(IN, FORM), 
  update_fi_form(OFF, LOG, FORM, NEW_FORM),
  put_form(OUT, NEW_FORM), !,  
  bch(TAB, OFF, LOG, SUC, IN, OUT).

bch_ch('X', _, OFF, LOG, _, _, IN, OUT) :- 
  pass_id(OFF, LOG, IN, OUT), !,
  pass_id(OFF, LOG, IN, OUT).

bch(TAB, OFF, LOG, NUM, IN, OUT) :- 
  get_char(IN, CH), 
  put_if_not_p(OUT, CH),
  num_succ(NUM, SUC), !,
  bch_ch(CH, TAB, OFF, LOG, NUM, SUC, IN, OUT), !.

put_if_not_p(_, 'P') :- !.
put_if_not_p(OUT, CH) :- put_char(OUT, CH). 

merge(TPTP, TEMP, TESC) :- 
  tptp_bch(TPTP, _, TAB, OFF), !,
  open(TEMP, read, IN, [encoding(octet)]), !,
  open(TESC, write, OUT, [encoding(octet)]), !,
  bch(TAB, OFF, [], 0, IN, OUT),
  close(IN),
  close(OUT).