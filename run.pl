#!/usr/bin/env swipl

:- initialization(main, main).

:- ["results/vampire"].

main([]) :-
  vampire(X, Y),
  write(X),
  write(Y).
  