#!/usr/bin/env swipl
:- initialization(main, main).
:- [prelude, common, proofs].

delete_file_if_exists(FILE) :- exists_file(FILE) -> delete_file(FILE) ; true.

read_item_core(Goal, Stream, Item) :- 
  read_line_to_string(Stream, String), 
  (
    String = end_of_file -> 
    (
      write("Read item fail, EOF\n"),
      false
    ) ; 
    (
      call(Goal, String, Item) ; 
      read_item_core(Goal, Stream, Item)
    )
  ).

read_item(Goal, File, Time) :- 
  open(File, read, Stream), 
  read_item_core(Goal, Stream, Time),
  close(Stream).

read_time(String, Time) :- 
  string_concat("\tUser time (seconds): ", TimeString, String),
  number_string(Time, TimeString).

read_mem(String, PeakMem) :-
  string_concat("\tMaximum resident set size (kbytes): ", PeakMemStr, String), 
  number_string(PeakMem, PeakMemStr).

s_to_ms(S, MS) :- MS is round(S * 1000).

check_name(SOLVER, KERNEL, NAME) :- 
  format("Checking problem = ~w\n", [NAME]), !,
  name_probpath(NAME, PROB_PATH),
  (
    format_shell("/usr/bin/time -v $TESC/t3p verify ~w ~w proofs/~w/~w.tesc 1>> errmsg 2> measure", [KERNEL, PROB_PATH, SOLVER, NAME], 0) ->
    read_item(read_time, "measure", TIME_SEC),
    s_to_ms(TIME_SEC, TIME),
    read_item(read_mem, "measure", MEM),
    add_entry('verifications.pl', verification(SOLVER, KERNEL, NAME, (TIME,MEM)))
  ;
    add_entry('verifications.pl', verification(SOLVER, KERNEL, NAME, failed))
  ),
  delete_file_if_exists("errmsg"), !,
  delete_file_if_exists("measure").

main([SOLVER, VERIFIER]) :- 
  findall(NAME, proof(SOLVER, NAME, passed(_, _)), NAMES), !,
  cmap(check_name(SOLVER, VERIFIER), NAMES), !.

main([]) :- 
  shell("echo \"\" > verifications.pl", 0),
  main([vampire,otv]),
  main([vampire,vtv]),
  main([eprover,otv]),
  main([eprover,vtv]).