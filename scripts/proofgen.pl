#!/usr/bin/env swipl

:- initialization(main, main).
:- [misc].
% :- consult('/home/sk/projects/tesc/ttc').


bench(SLVR, NAME) :- 
  write(" ────────────────────────────────────────────────────────────────── "), 
  write("Proving problem = "),
  write(NAME),
  write("\n"),
  atom_firstchar(SLVR, CH),
  path_cat(NAME, CAT),
  tptp_path(TPTP_DIR),
  tesc_path(TESC_DIR),
  atomic_list_concat([TPTP_DIR, "Problems/", CAT, "/", NAME, ".p"], TPTP), 
  atomic_list_concat([TESC_DIR, CH, "sol/", NAME, ".tstp"], TSTP), 

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

main([SLVR | OPTS]) :-
  trace_if_debug(OPTS),
  set_prolog_flag(stack_limit, 4_294_967_296),
  atom_firstchar(SLVR, S),
  tesc_path(TESC_DIR),
  atomic_list_concat([TESC_DIR, S, "sol/"], SOL_DIR), 
  path_filenames(SOL_DIR, FILENAMES),
  maplist([FILENAME, NAME]>> atom_concat(NAME, '.tstp', FILENAME), FILENAMES, NAMES), 
  write(NAMES),
  % valid_sol_names(SLVR, ALL),
  % random_n(NUM, ALL, NAMES),
  proofgen(SLVR, NAMES),
  true.
  

% main([SLVR | ARGS]) :- 
%   set_prolog_flag(stack_limit, 4_294_967_296),
%   trace_if_debug(ARGS),
%   valid_sol_names(SLVR, ALL),
%   (
%     (
%       ARGS = [DROP_ATOM, TAKE_ATOM | _],
%       atom_number(DROP_ATOM, DROP),
%       atom_number(TAKE_ATOM, TAKE)
%     ) ->
%     slice(DROP, TAKE, ALL, NAMES)
%   ;
%     (
%       ARGS = [DROP_ATOM | _], 
%       atom_number(DROP_ATOM, DROP)
%     ) ->
%     drop(DROP, ALL, NAMES)
%   ;
%     NAMES = ALL
%   ),
%   proofgen(SLVR, NAMES),
%   true.
% 