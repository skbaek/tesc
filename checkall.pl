#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].
:- [check].

check_proof(PRVR, TESC) :- 
  atom_concat(PRVR, TEMP0, TESC), 
  atom_concat('e/', TEMP1, TEMP0), 
  atom_concat(NAME, '.tesc', TEMP1), 
  write(" ────────────────────────────────────────────────────────────────── "), 
  format("Verifying proof : ~w\n", NAME),
  atomic_list_concat(["p/", NAME, ".tptp"], TPTP), 
  check(TPTP, TESC).

% is_temp(NAME) :- atom_concat(_, ".temp", NAME).
  
main([PRVR]) :- 
  set_prolog_flag(stack_limit, 4_294_967_296),
  atom_concat(PRVR, e, PATH),
  rec_dir_files(PATH, PATHS),
  maplist_count(check_proof(PRVR), 0, 0, PATHS, CNT, TTL), 
  format("VERFIED/TOTAL = ~w/~w\n", [CNT, TTL]).
