:- [prelude].

name_probpath(NAME, PROB_PATH) :- 
  atom_codes(NAME, [C0, C1, C2 | _]),
  atom_codes(CAT, [C0, C1, C2]),  
  format(string(PROB_PATH), "$TPTP/Problems/~w/~w.p", [CAT, NAME]).

name_solpath(SOLVER, NAME, SOL_PATH) :- 
  format(string(SOL_PATH), "$ITP/solutions/~w/~w.s", [SOLVER, NAME]).

name_prfpath(SOLVER, NAME, PRF_PATH) :- 
  format(string(PRF_PATH), "$ITP/proofs/~w/~w.tesc", [SOLVER, NAME]).

take_upto(0, _, []) :- !. 
take_upto(_, [], []):- !. 
take_upto(NUM, [ELEM | LIST], [ELEM | REM]) :- 
  num_pre(NUM, PRED),
  take_upto(PRED, LIST, REM).

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
