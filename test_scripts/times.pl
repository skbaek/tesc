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

get(time, KERNEL, (SOLVER, NAME), TIME) :- 
  verification(SOLVER, KERNEL, NAME, (TIME,_)).

get(mem, KERNEL, (SOLVER, NAME), MEM) :- 
  verification(SOLVER, KERNEL, NAME, (_,MEM)).

timecmp(CMP, X, Y) :- 
  compare(TRI_CMP, X, Y), !, 
  timecmp(TRI_CMP, CMP). 
  
timecmp(<, <).
timecmp(=, <).
timecmp(>, >).

% collapse([ELEM], [ELEM]) :- !.
% collapse([(TIME, _), (TIME, CNT) | POINTS], CLPS) :- !, collapse([(TIME, CNT) | POINTS], CLPS). 
% collapse([ELEM | POINTS], [ELEM | CLPS]) :- !, collapse(POINTS, CLPS). 

collapse(_, [ELEM], [ELEM]) :- !.
collapse(0, [(TIME, _), (TIME, CNT) | POINTS], CLPS) :- !, collapse(0, [(TIME, CNT) | POINTS], CLPS). 
collapse(0, [ELEM | POINTS], [ELEM | CLPS]) :- !, 
  resolution(RES), 
  collapse(RES, POINTS, CLPS). 
collapse(NUM, [_ | POINTS], CLPS) :- 
  num_pre(NUM, PRE), 
  collapse(PRE, POINTS, CLPS). 

all_pairs(PAIRS) :- 
  findall(
    (SOLVER, NAME), 
    (verification(SOLVER, verified, NAME, TIME), TIME \= failed), 
    PAIRS
  ). 
  
main([mean, TYPE, KERNEL]) :-
  all_pairs(PAIRS),
  cmap(get(TYPE, KERNEL), PAIRS, TIMES), 
  sum_list(TIMES, TIME),
  length(TIMES, LEN),
  MEAN is TIME / LEN, 
  format("MEAN for ~w = ~w\n", [KERNEL, MEAN]).

main([median, TYPE, KERNEL]) :-
  all_pairs(PAIRS),
  cmap(get(TYPE, KERNEL), PAIRS, TIMES), 
  length(TIMES, LEN),
  predsort(timecmp, TIMES, SORTED), 
  length(TIMES, LEN),
  length(SORTED, SORTED_LEN),
  format("~w = ~w\n", [LEN, SORTED_LEN]),
  MIDDLE is (LEN - 1) / 2,
  nth0(MIDDLE, SORTED, MEDIAN),
  format("MEDIAN = ~w\n", [MEDIAN]).

main([under, time, KERNEL]) :-
  all_pairs(PAIRS),
  cmap(get(time, KERNEL), PAIRS, TIMES), 
  include(>(5000), TIMES, U5), 
  include(>(1000), TIMES, U1), 
  length(TIMES, LEN_ALL),
  length(U5, LEN_U5),
  length(U1, LEN_U1),
  R5 is (LEN_U5 / LEN_ALL) * 100,
  R1 is (LEN_U1 / LEN_ALL) * 100,
  format("U5 : ~w percent\n", [R5]),
  format("U1 : ~w percent\n", [R1]).

main([data, TYPE, KERNEL]) :-
  all_pairs(PAIRS),
  cmap(get(TYPE, KERNEL), PAIRS, TIMES), 
  length(TIMES, LEN),
  predsort(timecmp, TIMES, SORTED), 
  length(SORTED, LEN),
  range(1,LEN,RNG), 
  zip(SORTED, RNG, POINTS), 
  collapse(0, POINTS, CLPS),
  length(CLPS, SIZE),
  write_sans(5, CLPS),
  format("\n\nCollapsed datapoint size = ~w\n", SIZE),
  true.

resolution(35).



