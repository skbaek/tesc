#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].

bench(PRVR, SOL_PATH) :- 
  atom_concat(PRVR, TEMP0, SOL_PATH), 
  atom_concat('s/', TEMP1, TEMP0), 
  atom_concat(NAME, '.tstp', TEMP1), 
  write(" ────────────────────────────────────────────────────────────────── "), 
  format("Bench problem : ~w\n", NAME),
  atomic_list_concat(["./ttc.pl ", PRVR, " p/", NAME, ".tptp ", SOL_PATH, " temp.tesc"], CMD_C),
  atomic_list_concat(["./ttv.pl p/", NAME, ".tptp temp.tesc"], CMD_V),
  shell(CMD_C, _), nl,
  shell(CMD_V, _), nl, nl.

main([PRVR]) :- 
  set_prolog_flag(stack_limit, 4_294_967_296),
  atom_concat(PRVR, s, SOLS_PATH),
  rec_dir_files(SOLS_PATH, SOL_PATHS),
  maplist_count(0, bench(PRVR), SOL_PATHS).

maplist_count(_, _, []).
maplist_count(NUM, GOAL, [ELEM | LIST]) :- 
  format("COUNT : ~w\n\n", [NUM]),
  call(GOAL, ELEM), !, 
  SUCC is NUM + 1, 
  maplist_count(SUCC, GOAL, LIST).

% is_temp(NAME) :- atom_concat(_, ".temp", NAME).
  

