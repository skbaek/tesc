#!/usr/bin/env swipl
:- initialization(main, main).

% thm_indicator(STR) :-
%   split_string(STR, ":", " %", ["Status", STAT]), 
%   member(STAT, ["Theorem", "Unsatisfiable", "ContradictoryAxioms"]).
% 
% thm(PATH) :- 
%   any_line_path(PATH, thm_indicator).


line_count_path(PATH, CNT) :- 
  open(PATH, read, STRM),
  line_count(STRM, CNT),
  close(STRM).
  

main([PATH]) :- 
  line_count_path(PATH, CNT),
  write(CNT).
  
  % set_prolog_flag(stack_limit, 4_294_967_296),
  % findall(PROB, problem(PROB), PROB_NAMES),
  % maplist(probname_probpath, PROB_NAMES, PROB_PATHS),
  % include(thm, PROB_PATHS, THM_PATHS),
  % maplist([THM_PATH, theorem(THM_NAME)]>>probpath_probname(THM_PATH, THM_NAME), THM_PATHS, TERMS),
  % update_problems(TERMS).


  