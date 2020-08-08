#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].
:- [prove].

bench(PROVER, PRVR, NAME) :- 
  write(" ────────────────────────────────────────────────────────────────── "), 
  format("Proving problem : ~w\n", NAME),
  path_cat(NAME, CAT),
  tptp_directory(TPTP_DIR),
  atomic_list_concat([TPTP_DIR, "Problems/", CAT, "/", NAME, ".p"], TPTP), 
  atomic_list_concat([PRVR, "sol/", NAME, ".tstp"], TSTP), 
  atomic_list_concat([PRVR, "prf/", NAME, ".tesc"], TESC), 
  atomic_list_concat(["./ttc.pl ", PROVER, " ", TPTP, " ", TSTP, " temp.tesc"], CMD_C),
  shell(CMD_C, RST), nl,
  (
    RST = 0 -> 
    mv("temp.tesc", TESC)
  ;
    rm("temp.tesc"),
    false
  ).

main([PROVER, DROP_ATOM, TAKE_ATOM]) :- 
  atom_number(DROP_ATOM, DROP),
  atom_number(TAKE_ATOM, TAKE),
  prover_abrv(PROVER, PRVR),
  set_prolog_flag(stack_limit, 4_294_967_296),
  names_stashed(PRVR, ALL),
  slice(DROP, TAKE, ALL, NAMES),
  length(NAMES, NUM), 
  format("Proving ~w problems\n", NUM),
  maplist_count(bench(PROVER, PRVR), 0, 0, NAMES, CNT, TTL), 
  format("PROVEN/TOTAL = ~w/~w.\n", [CNT, TTL]).
