#!/usr/bin/env swipl
:- initialization(main, main).
:- ['$HOME/prelude'].

sed(BASE) :- 
 format_shell("cat ./solutions/eprover/~w | sed '/\\(^%\\|^#\\|^\\$\\)/d' > newsols/~w", [BASE, BASE], 0). 

main :- 
  folder_bases("solutions/eprover", BASES),
  cmap(sed, BASES).
