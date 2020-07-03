:- [op].

term_scla(TERM, (ID, TYPE, FORM)) :- 
  TERM =.. [LNG, ID, TYPE, TF], 
  tf_form(LNG, TF, FORM).

term_scla(TERM, (ID, TYPE, FORM, ANT)) :- 
  TERM =.. [LNG, ID, TYPE, TF, ANT], 
  tf_form(LNG, TF, FORM).

tstp_sclas(TSTP, SCLAS) :- 
  style_check(-singleton),
  % retract_all_tptp_clauses,
  declare_TPTP_operators,
  % tptp_directory(TPTP_DIR), 
  % current_directory(CURR_DIR), 
  % cd(TPTP_DIR),
  % name_cat(NAME, CAT),
  % atomic_list_concat(["Problems/", CAT, "/", NAME, ".p"], PATH),
  tptp_terms(TSTP, TERMS), !,
  maplist_cut(term_scla, TERMS, SCLAS).