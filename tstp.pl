:- [op].

term_scla(TERM, (ID, TYPE, FORM)) :- 
  TERM =.. [LNG, ID, TYPE, TF], 
  tf_form(LNG, TF, FORM).

term_scla(TERM, (ID, TYPE, FORM, ANT)) :- 
  TERM =.. [LNG, ID, TYPE, TF, ANT], 
  tf_form(LNG, TF, FORM).

tstp_sclas(TSTP, SCLAS) :- 
  style_check(-singleton),
  declare_TPTP_operators,
  tptp_terms(TSTP, TERMS), !,
  maplist_cut(term_scla, TERMS, SCLAS).