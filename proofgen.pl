#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].
:- [prove].

bench(PRVR, NAME) :- 
  % atom_concat(PRVR, TEMP0, TSTP), 
  % atom_concat('s/', TEMP1, TEMP0), 
  % atom_concat(NAME, '.tstp', TEMP1), 
  write(" ────────────────────────────────────────────────────────────────── "), 
  format("Proving problem : ~w\n", NAME),
  atomic_list_concat(["p/", NAME, ".tptp"], TPTP), 
  atomic_list_concat([PRVR, "s/", NAME, ".tstp"], TSTP), 
  atomic_list_concat([PRVR, "e/", NAME, ".tesc"], TESC), 
  % (
  %   prove(PRVR, TPTP, TSTP, "temp.tesc") -> 
  %   mv("temp.tesc", TESC)
  % ; 
  %   rm("temp.tesc"),
  %   false
  % ).
  atomic_list_concat(["./ttc.pl ", PRVR, " ", TPTP, " ", TSTP, " temp.tesc"], CMD_C),
  % atomic_list_concat(["./ttv.pl p/", NAME, ".tptp temp.tesc"], CMD_V),
  shell(CMD_C, RST), nl,
  (
    RST = 0 -> 
    mv("temp.tesc", TESC)
  ;
    rm("temp.tesc"),
    false
  ).


  % shell(CMD_V, _), nl, nl.

% is_temp(NAME) :- atom_concat(_, ".temp", NAME).
  
main([PRVR]) :- 
  set_prolog_flag(stack_limit, 4_294_967_296),
  % atom_concat(PRVR, s, SOLS_PATH),
  % rec_dir_files(SOLS_PATH, SOL_PATHS),
  names_from_e(PRVR, NAMES),
  length(NAMES, NUM), 
  format("Proving ~w problems\n", NUM),
  maplist_count(bench(PRVR), 0, 0, NAMES, CNT, TTL), 
  format("PROVEN/TOTAL = ~w/~w\n.", [CNT, TTL]).
