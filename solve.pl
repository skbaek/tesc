% :- module(solve, [solve/3]).

:- [vsolve].
:- [esolve].

solve(e, TSTP, SOL) :- esolve(TSTP, SOL).
solve(v, TSTP, SOL) :- vsolve(TSTP, SOL).

