:- [tptp].

check_term(PROB, CTX, CNT, a(PID, DIR, PRF)) :- 
  get_assoc(PID, CTX, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  num_succ(CNT, SUCC),
  check_term(PROB, CTX_N, SUCC, PRF).

check_term(PROB, CTX, CNT, b(PID, PRF_L, PRF_R)) :- 
  get_assoc(PID, CTX, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc(CNT, CTX, CONC_L, CTX_L),
  put_assoc(CNT, CTX, CONC_R, CTX_R), !, 
  num_succ(CNT, SUCC),
  check_term(PROB, CTX_L, SUCC, PRF_L), !,
  check_term(PROB, CTX_R, SUCC, PRF_R).

check_term(PROB, CTX, CNT, c(PID, TERM, PRF)) :- 
  get_assoc(PID, CNT, PREM),
  ground(TERM),
  no_fv_term(0, TERM),
  counter_safe(CNT, TERM),
  cb(TERM, PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  num_succ(CNT, SUCC),
  check_term(PROB, CTX_N, SUCC, PRF).

check_term(PROB, CTX, CNT, d(PID, PRF)) :- 
  get_assoc(PID, CTX, PREM),
  db(CNT, PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  num_succ(CNT, SUCC),
  check_term(PROB, CTX_N, SUCC, PRF).

check_term(PROB, CTX, CNT, f(FORM, PRF_L, PRF_R)) :- 
  ground(FORM), % No logic variables in Form
  no_fv_form(0, FORM), % No free object variables in Form
  counter_safe(CNT, FORM), % No new parameters in Form
  num_succ(CNT, SUCC),
  put_assoc(CNT, CTX, $neg(FORM), CTX_N), !,
  check_term(PROB, CTX_N, SUCC, PRF_L),
  put_assoc(CNT, CTX, $pos(FORM), CTX_P), !,
  check_term(PROB, CTX_P, SUCC, PRF_R).

check_term(PROB, CTX, CNT, n(NAME, PRF)) :- 
  get_assoc(NAME, PROB, FORM),
  put_assoc(CNT, CTX, $pos(FORM), CTX_N), !,
  num_succ(CNT, SUCC),
  check_term(PROB, CTX_N, SUCC, PRF).

check_term(PROB, CTX, CNT, s(PID, PRF)) :- 
  get_assoc(PID, CTX, PREM),
  sb(PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  num_succ(CNT, SUCC),
  check_term(PROB, CTX_N, SUCC, PRF).

check_term(PROB, CTX, CNT, t(SF, PRF)) :- 
  no_fv_sf(0, SF),  
  justified(CNT, SF),
  put_assoc(CNT, CTX, SF, CTX_N), !,
  num_succ(CNT, SUCC),
  check_term(PROB, CTX_N, SUCC, PRF).

check_term(_, CTX, _, x(PID, NID)) :- 
  get_assoc(PID, CTX, $pos(FORM_P)),
  get_assoc(NID, CTX, $neg(FORM_N)),
  FORM_P == FORM_N.
  
check_term(TPTP, TESC) :- 
  style_check(-singleton),
  pose(TPTP, PROB),
  open(TESC, read, STRM, [encoding(octet)]), !, 
  get_prf(STRM, PRF),
  close(STRM), 
  empty_assoc(CTX),
  check_term(PROB, CTX, 0, PRF).

check_strm(TPTP, TESC) :- 
  style_check(-singleton),
  pose(TPTP, PROB),
  open(TESC, read, STRM, [encoding(octet)]), !, 
  empty_assoc(CTX),
  check_strm(STRM, PROB, CTX, 0),  
  close(STRM).

check_strm(STRM, PROB, CTX, CNT) :- 
  num_succ(CNT, SUCC),
  get_char(STRM, CH), !,
  check_strm(STRM, PROB, CTX, CNT, SUCC, CH), !.

check_strm(STRM, PROB, CTX, CNT, SUCC, 'A') :- 
  get_num(STRM, ID),  
  get_dir(STRM, DIR),
  get_assoc(ID, CTX, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  check_strm(STRM, PROB, CTX_N, SUCC), !. 
    
check_strm(STRM, PROB, CTX, CNT, SUCC, 'B') :- 
  get_num(STRM, PID), 
  get_assoc(PID, CTX, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc(CNT, CTX, CONC_L, CTX_L), !,
  put_assoc(CNT, CTX, CONC_R, CTX_R), !, 
  check_strm(STRM, PROB, CTX_L, SUCC), !,
  check_strm(STRM, PROB, CTX_R, SUCC), !.

check_strm(STRM, PROB, CTX, CNT, SUCC, 'C') :- 
  get_num(STRM, ID), 
  get_term(STRM, TERM), 
  get_assoc(ID, CTX, PREM),
  ground(TERM),
  no_fv_term(0, TERM),
  counter_safe(CNT, TERM),
  cb(TERM, PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  check_strm(STRM, PROB, CTX_N, SUCC), !.

check_strm(STRM, PROB, CTX, CNT, SUCC, 'D') :- 
  get_num(STRM, ID), 
  get_assoc(ID, CTX, PREM),
  db(CNT, PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  check_strm(STRM, PROB, CTX_N, SUCC), !.

check_strm(STRM, PROB, CTX, CNT, SUCC, 'F') :- 
  get_form(STRM, FORM), 
  ground(FORM), % No logic variables in Form
  no_fv_form(0, FORM), % No free object variables in Form
  counter_safe(CNT, FORM), % No new parameters in Form
  put_assoc(CNT, CTX, $neg(FORM), CTX_N), !,
  check_strm(STRM, PROB, CTX_N, SUCC), !,
  put_assoc(CNT, CTX, $pos(FORM), CTX_P), !,
  check_strm(STRM, PROB, CTX_P, SUCC), !.

check_strm(STRM, PROB, CTX, CNT, SUCC, 'N') :- 
  get_name(STRM, NAME), 
  get_assoc(NAME, PROB, FORM),
  put_assoc(CNT, CTX, $pos(FORM), CTX_N), !,
  check_strm(STRM, PROB, CTX_N, SUCC), !.

check_strm(STRM, PROB, CTX, CNT, SUCC, 'S') :- 
  get_num(STRM, ID), 
  get_assoc(ID, CTX, PREM),
  sb(PREM, CONC), 
  put_assoc(CNT, CTX, CONC, CTX_N), !,
  check_strm(STRM, PROB, CTX_N, SUCC), !.
    
check_strm(STRM, PROB, CTX, CNT, SUCC, 'T') :-
  get_sf(STRM, SF),
  no_fv_sf(0, SF),  
  justified(CNT, SF),
  put_assoc(CNT, CTX, SF, CTX_N), !,
  check_strm(STRM, PROB, CTX_N, SUCC), !.

check_strm(STRM, _, CTX, _, _, 'X') :- 
  get_num(STRM, PID), 
  get_num(STRM, NID), 
  get_assoc(PID, CTX, $pos(FORM_P)),
  get_assoc(NID, CTX, $neg(FORM_N)),
  FORM_P == FORM_N, !.

rust_check(TPTP, TESC) :-
  write("Translating TPTP to TTP...\n"),
  pose_path(TPTP, 'temp.ttp'),
  write("Calling Rust chekcer...\n"),
  concat_shell(["/home/sk/projects/tesc/rttv ", TESC], 0),
  write("Rust checker successfully terminated.\n").
  
  
