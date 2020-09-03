#!/usr/bin/env swipl
:- initialization(main, main).

del_comments_aux(READ, WRITE) :- 
  read_line_to_codes(READ, CODES), 
  del_comments_aux(READ, WRITE, CODES).

del_comments_aux(_, _, end_of_file) :- !.
del_comments_aux(READ, WRITE, [35 | _]) :- !, del_comments_aux(READ, WRITE), !.
del_comments_aux(READ, WRITE, CODES) :- 
  atom_codes(ATOM, CODES), 
  writeln(WRITE, ATOM), !, 
  del_comments_aux(READ, WRITE), !.

del_comments(FILE) :- 
  open(FILE, read, READ), 
  open('temp', write, WRITE), 
  del_comments_aux(READ, WRITE),
  close(READ),
  close(WRITE), 
  mv('temp', FILE).

main :- 
  directory_files(".", X), 
  delete(X, '.', Y),
  delete(Y, '..', Z),
  write(Z),
  maplist(del_comments, Z).