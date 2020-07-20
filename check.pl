:- use_module(tptp).

/*
check_debug(PROB, CNT, a(PID, DIR, PRF)) :- 
  num_succ(CNT, SCNT),
  get_assoc(PID, PROB, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(n(CNT), PROB, CONC, PROB_N), !,
  check_debug(PROB_N, SCNT, PRF).

check_debug(PROB, CNT, b(PID, PRF_L, PRF_R)) :- 
  num_succ(CNT, SCNT),
  get_assoc(PID, PROB, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc(n(CNT), PROB, CONC_L, PROB_L),
  put_assoc(n(CNT), PROB, CONC_R, PROB_R), !,
  check_debug(PROB_L, SCNT, PRF_L), !,
  check_debug(PROB_R, SCNT, PRF_R).

check_debug(PROB, CNT, c(PID, TERM, PRF)) :- 
  num_succ(CNT, SCNT),
  ground(TERM),
  no_fv_term(0, TERM),
  counter_safe(CNT, TERM),
  get_assoc(PID, PROB, PREM),
  cb(TERM, PREM, CONC), 
  put_assoc(n(CNT), PROB, CONC, PROB_N), !,
  check_debug(PROB_N, SCNT, PRF).

check_debug(PROB, CNT, d(PID, PRF)) :- 
  num_succ(CNT, SCNT),
  num_succ(SCNT, SSCNT),
  get_assoc(PID, PROB, PREM),
  db(SCNT, PREM, CONC), 
  put_assoc(n(CNT), PROB, CONC, PROB_N), !,
  check_debug(PROB_N, SSCNT, PRF).

check_debug(PROB, CNT, f(FORM, PRF_L, PRF_R)) :- 
  num_succ(CNT, SCNT),
  ground(FORM), % No logic variables in Form
  no_fv_form(0, FORM), % No free object variables in Form
  counter_safe(CNT, FORM), % No new parameters in Form
  put_assoc(n(CNT), PROB, $neg(FORM), PROB_L), !,
  check_debug(PROB_L, SCNT, PRF_L),
  put_assoc(n(CNT), PROB, $pos(FORM), PROB_R), !,
  check_debug(PROB_R, SCNT, PRF_R).

check_debug(PROB, CNT, s(PID, PRF)) :- 
  num_succ(CNT, SCNT),
  get_assoc(PID, PROB, PREM),
  sb(PREM, CONC), 
  put_assoc(n(CNT), PROB, CONC, PROB_N), !,
  check_debug(PROB_N, SCNT, PRF).

check_debug(PROB, CNT, t(SF, PRF)) :- 
  num_succ(CNT, SCNT),
  no_fv_sf(0, SF),  
  justified(SCNT, SF, CNT_N),
  put_assoc(n(CNT), PROB, SF, PROB_N), !,
  check_debug(PROB_N, CNT_N, PRF).
    
check_debug(PROB, CNT, w(PID, PRF)) :- 
  del_assoc(PID, PROB, _, PROB_N), !,
  check_debug(PROB_N, CNT, PRF).

check_debug(PROB, _, x(PID, NID)) :- 
  get_assoc(PID, PROB, $pos(FORM_P)),
  get_assoc(NID, PROB, $neg(FORM_N)),
  FORM_P == FORM_N.

check_debug(TPTP, TESC) :- 
  style_check(-singleton),
  pose(none, TPTP, _, _, PROB),
  open(TESC, read, STRM, [encoding(octet)]), 
  get_prf(STRM, PRF),
  check_debug(PROB, 0, PRF),
  write("Proof verified.\n"),
  close(STRM).
*/


/*
check(PROB, FP, a(PID, DIR, CID, PRF)) :- 
  write("A-fail\n"),
  throw(check_failure).
  % get_assoc(PID, PROB, PREM),
  % ab(DIR, PREM, CONC), 
  % put_assoc(CID, PROB, CONC, PROB_N), !,
  % check(PROB_N, FP, PRF).

check(PROB, FP, b(PID, CID, PRF_L, PRF_R)) :- 
  write("B-fail\n"),
  throw(check_failure).
  % get_assoc(PID, PROB, PREM),
  % bb(PREM, CONC_L, CONC_R),
  % put_assoc(CID, PROB, CONC_L, PROB_L),
  % put_assoc(CID, PROB, CONC_R, PROB_R), !,
  % check(PROB_L, FP, PRF_L), !,
  % check(PROB_R, FP, PRF_R).

check(PROB, FP, c(PID, TERM, CID, PRF)) :- 
  write("C-fail :\n"),
  format("FP = ~w\n", FP),
  format("PID = ~w\n", PID),
  format("CID = ~w\n", CID),
  format("TERM = ~w\n", TERM),
  % ground(TERM),
  % no_fv_term(0, TERM),
  % no_fp_term(FP, TERM),
  get_assoc(PID, PROB, PREM),
  format("PREM = ~w\n", PREM),
  % cb(TERM, PREM, CONC), 
  % put_assoc(CID, PROB, CONC, PROB_N), !,
  % check(PROB_N, FP, PRF).
  throw(check_failure).

check(PROB, FP, d(PID, CID, PRF)) :- 
  write("D-fail\n"),
  throw(check_failure).
  % get_assoc(PID, PROB, PREM),
  % db(FP, PREM, CONC), 
  % put_assoc(CID, PROB, CONC, PROB_N),
  % num_succ(FP, FP_N), !,
  % check(PROB_N, FP_N, PRF).

check(PROB, FP, f(FORM, CID, PRF_L, PRF_R)) :- 
  write("F-fail\n"),
  throw(check_failure).
  % ground(FORM), % No logic variables in Form
  % no_fv_form(0, FORM), % No free object variables in Form
  % no_fp_form(FP, FORM), % No new parameters in Form
  % put_assoc(CID, PROB, $neg(FORM), PROB_L), !,
  % check(PROB_L, FP, PRF_L),
  % put_assoc(CID, PROB, $pos(FORM), PROB_R), !,
  % check(PROB_R, FP, PRF_R).

check(PROB, FP, s(PID, CID, PRF)) :- 
  write("S-fail\n"),
  throw(check_failure).
  % get_assoc(PID, PROB, PREM),
  % sb(PREM, CONC), 
  % put_assoc(CID, PROB, CONC, PROB_N), !,
  % check(PROB_N, FP, PRF).

check(PROB, FP, t(SF, JST, CID, PRF)) :- 
  write("T-fail\n"),
  throw(check_failure).
  % no_fv_sf(0, SF),  
  % no_fp_sf(FP, SF), 
  % justified(PROB, SF, JST),
  % put_assoc(CID, PROB, SF, PROB_N), !,
  % check(PROB_N, FP, PRF).
    
check(PROB, FP, w(PID, PRF)) :- 
  write("W-fail\n"),
  throw(check_failure).
  % del_assoc(PID, PROB, _, PROB_N), !,
  % check(PROB_N, FP, PRF).

check(PROB, _, x(PID, NID)) :- 
  write("X-fail\n"),
  throw(check_failure).
  % get_assoc(PID, PROB, $pos(FORM_P)),
  % get_assoc(NID, PROB, $neg(FORM_N)),
  % FORM_P == FORM_N.
  */

put_assoc_write(CID, PROB, CONC, PROB_N) :- 
  %   ( 
  %     CID = x(_) -> 
  %     true ; 
  %     format("Adding ID : ~w\n\n", CID)
  %   ),
  put_assoc(CID, PROB, CONC, PROB_N).

check(TPTP, TESC) :- 
  style_check(-singleton),
  pose(none, TPTP, _, _, PROB),
  open(TESC, read, STRM, [encoding(octet)]), !, 
  check(STRM, PROB, 0), 
  write("Proof verified.\n\n"),
  close(STRM).

check(STRM, PROB, C) :- 
  mk_par(C, [], CID),
  num_succ(C, SC),
  get_char(STRM, CH), !,
  check(STRM, PROB, CID, SC, CH).
  
check(STRM, PROB, CID, SC, 'A') :- 
  get_id(STRM, ID),  
  get_dir(STRM, DIR),
  get_assoc(ID, PROB, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc_write(CID, PROB, CONC, PROB_N), !,
  check(STRM, PROB_N, SC). 
    
check(STRM, PROB, CID, SC, 'B') :- 
  get_id(STRM, ID), 
  get_assoc(ID, PROB, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc_write(CID, PROB, CONC_L, PROB_L),
  put_assoc_write(CID, PROB, CONC_R, PROB_R), !, 
  check(STRM, PROB_L, SC), !,
  check(STRM, PROB_R, SC).

check(STRM, PROB, CID, SC, 'C') :- 
  get_id(STRM, ID), 
  get_term(STRM, TERM), 
  get_assoc(ID, PROB, PREM),
  ground(TERM),
  no_fv_term(0, TERM),
  counter_safe(SC, TERM),
  cb(TERM, PREM, CONC), 
  put_assoc_write(CID, PROB, CONC, PROB_N), !,
  check(STRM, PROB_N, SC).

check(STRM, PROB, CID, SC, 'D') :- 
  num_succ(SC, SSC),
  get_id(STRM, ID), 
  get_assoc(ID, PROB, PREM),
  db(SC, PREM, CONC), 
  put_assoc_write(CID, PROB, CONC, PROB_N), !,
  check(STRM, PROB_N, SSC).

check(STRM, PROB, CID, SC, 'F') :- 
  get_form(STRM, FORM), 
  ground(FORM), % No logic variables in Form
  no_fv_form(0, FORM), % No free object variables in Form
  counter_safe(SC, FORM), % No new parameters in Form
  put_assoc_write(CID, PROB, $neg(FORM), PROB_N), !,
  check(STRM, PROB_N, SC),
  put_assoc_write(CID, PROB, $pos(FORM), PROB_P), !,
  check(STRM, PROB_P, SC).

check(STRM, PROB, CID, SC, 'S') :- 
  get_id(STRM, ID), 
  get_assoc(ID, PROB, PREM),
  sb(PREM, CONC), 
  put_assoc_write(CID, PROB, CONC, PROB_N), !,
  check(STRM, PROB_N, SC).
    
check(STRM, PROB, CID, SC, 'T') :- 
  get_sf(STRM, SF),
  no_fv_sf(0, SF),  
  justified(SC, SF, C_N),
  put_assoc(CID, PROB, SF, PROB_N), !,
  check(STRM, PROB_N, C_N).

check(STRM, PROB, CID, _, 'W') :- 
  atom_concat('@', ATOM, CID),
  atom_number(ATOM, C),
  get_id(STRM, ID), 
  del_assoc(ID, PROB, _, PROB_N), !,
  check(STRM, PROB_N, C).

check(STRM, PROB, _, _, 'X') :- 
  get_id(STRM, PID), 
  get_id(STRM, NID), 
  get_assoc(PID, PROB, $pos(FORM_P)),
  get_assoc(NID, PROB, $neg(FORM_N)),
  FORM_P == FORM_N.