:- module(solve, [solve/3]).

:- use_module(vsolve).
:- use_module(esolve).

solve(e, TSTP, SOL) :- esolve(TSTP, SOL).
solve(v, TSTP, SOL) :- vsolve(TSTP, SOL).

