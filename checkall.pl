#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].
:- [check].

check_proof(PRVR, TESC) :-
  tptp_directory(PATH),
  atom_concat(PRVR, TEMP0, TESC), 
  atom_concat('prf/', TEMP1, TEMP0), 
  atom_concat(NAME, '.tesc', TEMP1), 
  write(" ────────────────────────────────────────────────────────────────── "), 
  format("Verifying proof : ~w\n", NAME),
  path_cat(NAME, CAT),
  atomic_list_concat([PATH, 'Problems/', CAT, "/", NAME, ".p"], TPTP),
  check_strm(TPTP, TESC),
  write("Proof verified\n").

main([PROVER]) :- 
  atom_firstchar(PROVER, PRVR),
  set_prolog_flag(stack_limit, 4_294_967_296),
  atom_concat(PRVR, prf, PATH),
  rec_path_filenames(PATH, PATHS),
  maplist_count(check_proof(PRVR), 0, 0, PATHS, CNT, TTL), 
  format("VERFIED/TOTAL = ~w/~w\n", [CNT, TTL]).
