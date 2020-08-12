:- [tptp].

check_term(PROB, _, SUCC, CID, a(PID, DIR, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_term(PROB_N, SUCC, PRF).

check_term(PROB, _, SUCC, CID, b(PID, PRF_L, PRF_R)) :- 
  get_assoc(PID, PROB, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc(CID, PROB, CONC_L, PROB_L),
  put_assoc(CID, PROB, CONC_R, PROB_R), !, 
  check_term(PROB_L, SUCC, PRF_L), !,
  check_term(PROB_R, SUCC, PRF_R).

check_term(PROB, CNT, SUCC, CID, c(PID, TERM, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  ground(TERM),
  no_fv_term(0, TERM),
  counter_safe(CNT, TERM),
  cb(TERM, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_term(PROB_N, SUCC, PRF).

check_term(PROB, CNT, SUCC, CID, d(PID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  db(CNT, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_term(PROB_N, SUCC, PRF).

check_term(PROB, CNT, SUCC, CID, f(FORM, PRF_L, PRF_R)) :- 
  ground(FORM), % No logic variables in Form
  no_fv_form(0, FORM), % No free object variables in Form
  counter_safe(CNT, FORM), % No new parameters in Form
  put_assoc(CID, PROB, $neg(FORM), PROB_N), !,
  check_term(PROB_N, SUCC, PRF_L),
  put_assoc(CID, PROB, $pos(FORM), PROB_P), !,
  check_term(PROB_P, SUCC, PRF_R).

check_term(PROB, _, SUCC, CID, s(PID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  sb(PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_term(PROB_N, SUCC, PRF).

check_term(PROB, CNT, SUCC, CID, t(SF, PRF)) :- 
  no_fv_sf(0, SF),  
  justified(CNT, SF),
  put_assoc(CID, PROB, SF, PROB_N), !,
  check_term(PROB_N, SUCC, PRF).

check_term(PROB, _, SUCC, _, w(PID, PRF)) :- 
  del_assoc(PID, PROB, _, PROB_N), !,
  check_term(PROB_N, SUCC, PRF).

check_term(PROB, _, _, _, x(PID, NID)) :- 
  get_assoc(PID, PROB, $pos(FORM_P)),
  get_assoc(NID, PROB, $neg(FORM_N)),
  FORM_P == FORM_N.

check_term(PROB, CNT, PRF) :- 
  mk_par(CNT, [], CID),
  num_succ(CNT, SUCC),
  check_term(PROB, CNT, SUCC, CID, PRF).
  
check_term(TPTP, TESC) :- 
  style_check(-singleton),
  pose(none, TPTP, _, _, PROB),
  open(TESC, read, STRM, [encoding(octet)]), !, 
  get_prf(STRM, PRF),
  close(STRM), 
  check_term(PROB, 0, PRF).

check_strm(TPTP, TESC) :- 
  style_check(-singleton),
  pose(none, TPTP, _, _, PROB),
  open(TESC, read, STRM, [encoding(octet)]), !, 
  check_strm(STRM, PROB, 0),  
  close(STRM).

check_strm(STRM, PROB, CNT) :- 
  mk_par(CNT, [], CID),
  num_succ(CNT, SUCC),
  get_char(STRM, CH), !,
  check_strm(STRM, PROB, CNT, SUCC, CID, CH), !.

check_strm(STRM, PROB, _, SUCC, CID, 'A') :- 
  get_id(STRM, ID),  
  get_dir(STRM, DIR),
  get_assoc(ID, PROB, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_strm(STRM, PROB_N, SUCC), !. 
    
check_strm(STRM, PROB, _, SUCC, CID, 'B') :- 
  get_id(STRM, ID), 
  get_assoc(ID, PROB, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc(CID, PROB, CONC_L, PROB_L), !,
  put_assoc(CID, PROB, CONC_R, PROB_R), !, 
  check_strm(STRM, PROB_L, SUCC), !,
  check_strm(STRM, PROB_R, SUCC), !.

check_strm(STRM, PROB, CNT, SUCC, CID, 'C') :- 
  get_id(STRM, ID), 
  get_term(STRM, TERM), 
  get_assoc(ID, PROB, PREM),
  ground(TERM),
  no_fv_term(0, TERM),
  counter_safe(CNT, TERM),
  cb(TERM, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_strm(STRM, PROB_N, SUCC), !.

check_strm(STRM, PROB, CNT, SUCC, CID, 'D') :- 
  get_id(STRM, ID), 
  get_assoc(ID, PROB, PREM),
  db(CNT, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_strm(STRM, PROB_N, SUCC), !.

check_strm(STRM, PROB, CNT, SUCC, CID, 'F') :- 
  get_form(STRM, FORM), 
  ground(FORM), % No logic variables in Form
  no_fv_form(0, FORM), % No free object variables in Form
  counter_safe(CNT, FORM), % No new parameters in Form
  put_assoc(CID, PROB, $neg(FORM), PROB_N), !,
  check_strm(STRM, PROB_N, SUCC), !,
  put_assoc(CID, PROB, $pos(FORM), PROB_P), !,
  check_strm(STRM, PROB_P, SUCC), !.

check_strm(STRM, PROB, _, SUCC, CID, 'S') :- 
  get_id(STRM, ID), 
  get_assoc(ID, PROB, PREM),
  sb(PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check_strm(STRM, PROB_N, SUCC), !.
    
check_strm(STRM, PROB, CNT, SUCC, CID, 'T') :-
  get_sf(STRM, SF),
  no_fv_sf(0, SF),  
  justified(CNT, SF),
  put_assoc(CID, PROB, SF, PROB_N), !,
  check_strm(STRM, PROB_N, SUCC), !.

check_strm(STRM, PROB, _, SUCC, _, 'W') :- 
  get_id(STRM, ID), 
  del_assoc(ID, PROB, _, PROB_N), !,
  check_strm(STRM, PROB_N, SUCC), !.

check_strm(STRM, PROB, _, _, _, 'X') :- 
  get_id(STRM, PID), 
  get_id(STRM, NID), 
  get_assoc(PID, PROB, $pos(FORM_P)),
  get_assoc(NID, PROB, $neg(FORM_N)),
  FORM_P == FORM_N, !.