#!/usr/bin/env swipl
:- initialization(main, main).
:- ['$HOME/scripts/prelude', verifications].

zip([], [], []).
zip([X | XS], [Y | YS], [(X,Y) | XYS]) :- zip(XS, YS, XYS).

ms_min(MS, MIN) :- MIN is MS / 60000.

write_sans(_, []). 
write_sans(0, [(X,Y) | LIST]) :- !,
  format("(~w, ~w)\n        ", [X, Y]), !,
  write_sans(5, LIST), !.
write_sans(NUM, [(X,Y) | LIST]) :- !,
  format("(~w, ~w) ", [X, Y]),
  num_pre(NUM, PRE), !,
  write_sans(PRE, LIST), !.

pair_time(KERNEL, (SOLVER, NAME), TIME) :- 
  verification(SOLVER, KERNEL, NAME, TIME).

timecmp(CMP, X, Y) :- 
  compare(TRI_CMP, X, Y), !, 
  timecmp(TRI_CMP, CMP). 
  
timecmp(<, <).
timecmp(=, <).
timecmp(>, >).

collapse(_, [ELEM], [ELEM]).

collapse(0, [(TIME, _), (TIME, CNT) | POINTS], CLPS) :- !, collapse(0, [(TIME, CNT) | POINTS], CLPS). 
collapse(0, [ELEM | POINTS], [ELEM | CLPS]) :- !, collapse(5, POINTS, CLPS). 
collapse(NUM, [_ | POINTS], CLPS) :- 
  num_pre(NUM, PRE), 
  collapse(PRE, POINTS, CLPS). 

print_datapoints(KERNEL, PAIRS) :- 
  cmap(pair_time(KERNEL), PAIRS, TIMES), 
  predsort(timecmp, TIMES, SORTED), 
  length(SORTED, LEN), 

  format("Sorted length = ~w\n", [LEN]),

  range(1, LEN, RNG), 
  zip(SORTED, RNG, POINTS), 
  collapse(0, POINTS, CLPS),
  write_sans(5, CLPS).

all_pairs(PAIRS) :- 
  findall(
    (SOLVER, NAME), 
    (verification(SOLVER, verified, NAME, TIME), TIME \= failed), 
    PAIRS
  ). 


main([KERNEL]) :-
  all_pairs(PAIRS),
  print_datapoints(KERNEL, PAIRS).


%   cmap(pair_time(KERNEL), PAIRS, TIMES), 
%   length(TIMES, ALL_LEN),
% 
%   include(<(5000), TIMES, LOWS), 
%  
%   length(LOWS, LOWS_LEN),
% 
%   X is (ALL_LEN - LOWS_LEN) / ALL_LEN,
% 
%   write(X),

%   length(TIMES, LEN),
%   predsort(timecmp, TIMES, SORTED), 
%   length(TIMES, LEN),
%   length(SORTED, SORTED_LEN),
%   format("~w = ~w\n", [LEN, SORTED_LEN]),
% 
%   MIDDLE is (LEN - 1) / 2,
% 
%   nth0(MIDDLE, SORTED, MEDIAN),
%   format("MEDIAN = ~w\n", [MEDIAN]),
  
  
  



