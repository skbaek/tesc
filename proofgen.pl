#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].
:- [prove].
:- [probs].

bench(SLVR, NAME) :- 
  write(" ────────────────────────────────────────────────────────────────── "), 
  write("Proving problem = "),
  write(NAME),
  write("\n"),
  atom_firstchar(SLVR, CH),
  path_cat(NAME, CAT),
  tptp_directory(TPTP_DIR),
  atomic_list_concat([TPTP_DIR, "Problems/", CAT, "/", NAME, ".p"], TPTP), 
  atomic_list_concat([CH, "sol/", NAME, ".tstp"], TSTP), 
  atomic_list_concat([CH, "prf/", NAME, ".tesc"], TESC), 
  atomic_list_concat(["./ttc.pl ", SLVR, " ", TPTP, " ", TSTP, " temp.tesc"], CMD_C),
  shell(CMD_C, RST), 
  (
    RST = 0 -> 
    mv("temp.tesc", TESC)
  ;
    rm("temp.tesc"),
    false
  ).

main([SLVR | ARGS]) :- 
  set_prolog_flag(stack_limit, 4_294_967_296),
  valid_sol_names(SLVR, ALL),
  (
    ARGS = [DROP_ATOM, TAKE_ATOM] -> 
    atom_number(DROP_ATOM, DROP),
    atom_number(TAKE_ATOM, TAKE),
    slice(DROP, TAKE, ALL, NAMES)
  ;
    ARGS = [DROP_ATOM] -> 
    atom_number(DROP_ATOM, DROP),
    drop(DROP, ALL, NAMES)
  ;
    NAMES = ALL
  ),
  length(NAMES, NUM), 
  format("Proving ~w problems\n", NUM),
  maplist_count(bench(SLVR), 0, 0, NAMES, CNT, TTL),
  format("PROVEN/TOTAL = ~w/~w.\n", [CNT, TTL]).
