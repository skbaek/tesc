#!/usr/bin/env swipl

:- initialization(main, main).

main :- 
  writeln("TPTP path ="), 
  shell("echo $TPTP"),
  writeln("TESC path = "), 
  shell("echo $TESC").