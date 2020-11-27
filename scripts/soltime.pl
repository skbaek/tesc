#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].

e_check(STRM) :- 
  read_line_to_string(STRM, LINE), 
  (
    LINE = "# Proof found!" -> true  
  ;
    LINE = end_of_file -> false  
  ;
    e_check(STRM) 
  ).
  
call_prover(e, TPTP, TSTP) :- 
  atomic_list_concat(["./eprover --auto --cpu-limit=120 -p ", TPTP, " > ", TSTP], CMD), 
  shell(CMD, _), 
  open(TSTP, read, STRM), 
  e_check(STRM), 
  close(STRM).

call_prover(v, TPTP, TSTP) :- 
  atomic_list_concat(["./vampire_rel --proof tptp --time_limit 120s ", TPTP, " > ", TSTP], CMD),  
  shell(CMD, _), 
  open(TSTP, read, STRM), 
  read_line_to_string(STRM, LINE), 
  close(STRM), 
  LINE = "% Refutation found. Thanks to Tanya!".

call_prover(m, TPTP, TSTP) :- 
  atomic_list_concat(["timeout 60s metis --time-limit 60 --show proof ", TPTP, " > ", TSTP], CMD), 
  shell(CMD, _),
  open(TSTP, read, STRM), 
  read_line_to_string(STRM, _), 
  read_line_to_string(STRM, LINE), 
  close(STRM), 
  string_concat("% SZS status Unsatisfiable for", _, LINE).

solve_time(PRVR, NAME) :- 
  write(" ────────────────────────────────────────────────────────────────── "), 
  format("Proving problem : ~w\n", NAME),
  atomic_list_concat(["../tptp/", NAME, ".tptp"], TPTP), 
  atomic_list_concat(["temp/", NAME, ".tstp"], NEW_PATH), 
  (
    call_prover(PRVR, TPTP, "temp.tstp") -> 
    write("-- pass\n"),
    mv("temp.tstp", NEW_PATH)
  ; 
    write("--fail-!!!!!!!!\n"),
    rm("temp.tstp")
  ).

  % atomic_list_concat(["./ttc.pl ", PRVR, " ", TPTP, " ", TSTP, " temp.tesc"], CMD_C),
  % % atomic_list_concat(["./ttv.pl p/", NAME, ".tptp temp.tesc"], CMD_V),
  % shell(CMD_C, RST), nl,
  % (
  %   RST = 0 -> 
  %   mv("temp.tesc", TESC)
  % ;
  %   rm("temp.tesc"),
  %   false
  % ).


  % shell(CMD_V, _), nl, nl.

% is_temp(NAME) :- atom_concat(_, ".temp", NAME).

main([PROVER]) :- 
  atom_firstchar(PROVER, PRVR),
  names_stashed(PRVR, NAMES),
  length(NAMES, NUM), 
  format("Solving ~w problems\n", NUM),
  cmap(solve_time(PRVR), NAMES), 
  % format("PROVEN/TOTAL = ~w/~w\n.", [CNT, TTL]).
  true.
