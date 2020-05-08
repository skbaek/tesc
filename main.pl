#!/usr/bin/env swipl

:- initialization(main, main).

:- [solve, prove, check].

% test_all([]).
% test_all([TPTP | TPTPS]) :- 
%   format("Solving problem : ~w\n\n", TPTP),
%   atomic_concat("vp/", TPTP, PATH),
%   main(['-t', PATH]), 
%   format("Verifying proof : ~w\n\n", TPTP),
%   main(['-v', PATH, "temp.txtx"]), 
%   test_all(TPTPS).
% 
% main(['-tl']) :- 
%   file_strings("/home/sk/problist", TPTPS), 
%   time(test_all(TPTPS)).

% main(['-t', TPTP]) :- 
%   style_check(-singleton),
%   atom_string(TPTP, STR),
%   string_concat("vp/", TEMP, STR), 
%   string_concat(NAME, ".tptp", TEMP), 
%   atomics_to_string(["vs/", NAME, ".tstp"], TSTP),
%   tptp_prob(TPTP, PIDS, PROB),
%   tstp_sol(PRVR, PIDS, TSTP, SOL),
%   open("temp.txtx", write, STRM, [encoding(octet)]),
%   prove(STRM, PRVR, SOL, PROB),
%   close(STRM).

main(['-p', PRVR, TPTP, TSTP, TXTX]) :- 
  set_prolog_flag(stack_limit, 2_147_483_648),
  style_check(-singleton),
  pose(TPTP, PIDS, PROB),
  solve(PRVR, PIDS, TSTP, SOL),
  write_list(SOL),
  open(TXTX, write, STRM, [encoding(octet)]),
  prove(STRM, none, PRVR, SOL, PROB),
  close(STRM).
  
main(['-v', TPTP, TXTX]) :- 
  check(TPTP, TXTX).