#!/usr/bin/env swipl

:- initialization(main, main).
:- [misc].

bench(SLVR, NAME) :- 
  write(" ────────────────────────────────────────────────────────────────── "), 
  write("Proving problem = "),
  write(NAME),
  write("\n"),
  atom_firstchar(SLVR, CH),
  path_cat(NAME, CAT),
  tptp_folder(TPTP_DIR),
  tesc_folder(TESC_DIR),
  atomic_list_concat([TPTP_DIR, "Problems/", CAT, "/", NAME, ".p"], TPTP), 
  atomic_list_concat([TESC_DIR, CH, "sol/", NAME, ".s"], TSTP), 

  size_file(TSTP, SIZE),
  format("FILE SIZE = ~w\n\n", SIZE),

  atomic_list_concat([TESC_DIR, CH, "prf/", NAME, ".tesc"], TESC), 
  atomic_list_concat([TESC_DIR, "ttc.pl ", SLVR, " ", TPTP, " ", TSTP, " temp.tesc"], CMD_C),
  % ttc(SLVR, TPTP, TSTP, TESC).
  shell(CMD_C, RST), 
  (
    RST = 0 -> 
    mv("temp.tesc", TESC)
  ;
    rm("temp.tesc"),
    false
  ).

proofgen(SLVR, NAMES) :-
  length(NAMES, NUM), 
  format("Proving ~w problems\n", NUM),
  maplist_count(bench(SLVR), 0, 0, NAMES, CNT, TTL),
  format("PROVEN/TOTAL = ~w/~w.\n", [CNT, TTL]).

main([SLVR, DA, TA | OPTS]) :-
  trace_if_debug(OPTS),
  inc_mem, 
  atom_firstchar(SLVR, S),
  tesc_folder(TESC_DIR),
  atomic_list_concat([TESC_DIR, S, "sol/"], SOL_DIR), 
  folder_roots(SOL_DIR, NAMES),
  atom_number(DA, DROP),
  atom_number(TA, TAKE),
  slice(DROP, TAKE, NAMES, LIST),
  writeln_list(LIST),
  proofgen(SLVR, LIST),
  true.