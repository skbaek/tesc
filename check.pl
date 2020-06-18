:- [tptp].

/*
check(PROB, FP, a(PID, DIR, CID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check(PROB_N, FP, PRF).

check(PROB, FP, b(PID, CID, PRF_L, PRF_R)) :- 
  get_assoc(PID, PROB, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc(CID, PROB, CONC_L, PROB_L),
  put_assoc(CID, PROB, CONC_R, PROB_R), !,
  check(PROB_L, FP, PRF_L), !,
  check(PROB_R, FP, PRF_R).

check(PROB, FP, c(PID, TERM, CID, PRF)) :- 
  ground(TERM),
  no_fv_term(0, TERM),
  no_fp_term(FP, TERM),
  get_assoc(PID, PROB, PREM),
  cb(TERM, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check(PROB_N, FP, PRF).

check(PROB, FP, d(PID, CID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  db(FP, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N),
  num_succ(FP, FP_N), !,
  check(PROB_N, FP_N, PRF).

check(PROB, FP, f(FORM, CID, PRF_L, PRF_R)) :- 
  ground(FORM), % No logic variables in Form
  no_fv_form(0, FORM), % No free object variables in Form
  no_fp_form(FP, FORM), % No new parameters in Form
  put_assoc(CID, PROB, $neg(FORM), PROB_L), !,
  check(PROB_L, FP, PRF_L),
  put_assoc(CID, PROB, $pos(FORM), PROB_R), !,
  check(PROB_R, FP, PRF_R).

check(PROB, FP, s(PID, CID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  sb(PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N), !,
  check(PROB_N, FP, PRF).

check(PROB, FP, t(SF, JST, CID, PRF)) :- 
  no_fv_sf(0, SF),  
  no_fp_sf(FP, SF), 
  justified(PROB, SF, JST),
  put_assoc(CID, PROB, SF, PROB_N), !,
  check(PROB_N, FP, PRF).
    
check(PROB, FP, w(PID, PRF)) :- 
  del_assoc(PID, PROB, _, PROB_N), !,
  check(PROB_N, FP, PRF).

check(PROB, _, x(PID, NID)) :- 
  get_assoc(PID, PROB, $pos(FORM_P)),
  get_assoc(NID, PROB, $neg(FORM_N)),
  FORM_P == FORM_N.

check(TPTP, TESC) :- 
  style_check(-singleton),
  pose(TPTP, _, PROB),
  open(TESC, read, STRM, [encoding(octet)]), 
  get_prf(STRM, PRF),
  check(PROB, 0, PRF),
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




% ---------------------------------------------------

check(TPTP, TESC) :- 
  style_check(-singleton),
  pose(TPTP, _, PROB),
  open(TESC, read, STRM, [encoding(octet)]), 
  check(STRM, PROB, 0), 
  write("Proof verified.\n"),
  close(STRM).

check(STRM, PROB, FP) :- 
  get_char(STRM, CH), 
  (
    CH = 'A' -> 
    get_id(STRM, PID),  
    get_dir(STRM, DIR),
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    ab(DIR, PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N), !,
    check(STRM, PROB_N, FP) ;

    CH = 'B' -> 
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    bb(PREM, CONC_L, CONC_R),
    put_assoc(CID, PROB, CONC_L, PROB_L),
    put_assoc(CID, PROB, CONC_R, PROB_R), !, 
    check(STRM, PROB_L, FP), !,
    check(STRM, PROB_R, FP) ;

    CH = 'C' -> 
    get_id(STRM, PID), 
    get_term(STRM, TERM), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    ground(TERM),
    no_fv_term(0, TERM),
    no_fp_term(FP, TERM),
    cb(TERM, PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N), !,
    check(STRM, PROB_N, FP) ;

    CH = 'D' -> 
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    db(FP, PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N),
    num_succ(FP, FP_N), !,
    check(STRM, PROB_N, FP_N) ;

    CH = 'F' -> 
    get_form(STRM, FORM), 
    get_id(STRM, CID), 
    ground(FORM), % No logic variables in Form
    no_fv_form(0, FORM), % No free object variables in Form
    no_fp_form(FP, FORM), % No new parameters in Form
    put_assoc(CID, PROB, $neg(FORM), PROB_N), !,
    check(STRM, PROB_N, FP),
    put_assoc(CID, PROB, $pos(FORM), PROB_P), !,
    check(STRM, PROB_P, FP) ;

    CH = 'S' -> 
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    sb(PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N), !,
    check(STRM, PROB_N, FP) ;

    CH = 'T' -> 
    get_sf(STRM, SF), 
    get_atoms(STRM, JST), 
    get_id(STRM, CID), 
    no_fv_sf(0, SF),  
    no_fp_sf(FP, SF), 
    justified(PROB, SF, JST),
    put_assoc(CID, PROB, SF, PROB_N), !,
    check(STRM, PROB_N, FP) ;
    
    CH = 'W' -> 
    get_id(STRM, PID), 
    del_assoc(PID, PROB, _, PROB_N), !,
    check(STRM, PROB_N, FP) ;

    CH = 'X' -> 
    get_id(STRM, PID), 
    get_id(STRM, NID), 
    get_assoc(PID, PROB, $pos(FORM_P)),
    get_assoc(NID, PROB, $neg(FORM_N)),
    FORM_P == FORM_N
  ).
  