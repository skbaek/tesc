#!/usr/bin/env swipl

:- initialization(main, main).
:- [basic].

main :- 
  tptp_folder(TPTP),
  atom_concat(TPTP, 'Problems/', PATH),
  folder_files_rec(PATH, PROBS),
  writeln_list(PROBS),
  true.
  