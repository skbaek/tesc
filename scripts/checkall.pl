#!/usr/bin/env swipl

:- initialization(main, main).
:- [misc].

check_proof(OPTS, PRF_PATH) :-
  tptp_path(TPTP_PATH),
  tesc_path(TESC_PATH),
  codes_after_last_slash(PRF_PATH, CODES),
  atom_codes(TEMP1, CODES),
  atom_concat(NAME, '.tesc', TEMP1), 
  write(" ────────────────────────────────────────────────────────────────── "), 
  format("Verifying proof : ~w\n", NAME),
  path_cat(NAME, CAT),
  atomic_list_concat([TPTP_PATH, 'Problems/', CAT, "/", NAME, ".p"], PROB_PATH),
  atomic_list_concat([TESC_PATH, 'ttv'], TTV_PATH),
  concat_shell([TTV_PATH, PROB_PATH, PRF_PATH | OPTS], " ", 0). 

main([PROVER | OPTS]) :- 
  tesc_path(TESC_PATH),
  atom_firstchar(PROVER, PRVR),
  (
    member('-pl', OPTS) ->
    set_prolog_flag(stack_limit, 4_294_967_296) ;
    true
  ),
  atomic_list_concat([TESC_PATH, PRVR, prf], PATH),
  rec_path_filenames(PATH, PATHS),
  maplist_count(check_proof(OPTS), 0, 0, PATHS, CNT, TTL), 
  format("VERFIED/TOTAL = ~w/~w\n", [CNT, TTL]).
