#!/usr/bin/env swipl

:- initialization(main, main).
:- [misc, problems].

in_assoc(KEY, ASC) :- get_assoc(KEY, ASC, _).
  
put_assoc_if_new(KEY, ACC, VAL, NEW) :- 
  in_assoc(KEY, ACC) -> 
  format("\nDuplicate key found = ~w\n\n", KEY),
  false 
;
  put_assoc(KEY, ACC, VAL, NEW).

sq_balanced([39 | CODES]) :- !, last(CODES, 39).
sq_balanced([_ | _]). 

check_line(ACC, LINE, NEW) :- 
  (append([102, 111, 102, 40], TEMP, LINE) ; append([99, 110, 102, 40], TEMP, LINE)), !, 
  append(CODES, [44 | _], TEMP), !, 
  sq_balanced(CODES), 
  atom_codes(ID, CODES),
  put_assoc_if_new(ID, ACC, c, NEW). 
check_line(ACC, LINE, NEW) :- 
  append([105, 110, 99, 108, 117, 100, 101, 40, 39], TEMP, LINE), !,
  append(CODES, [39 | _], TEMP), 
  atom_codes(AXIOM, CODES),
  check_axiom(ACC, AXIOM, NEW).
check_line(_, ACC, _, ACC). 

check_axiom(ACC, AX, NEW) :- 
  tptp_folder(TPTP),
  atom_concat(TPTP, AX, PATH), 
  check_path(ACC, PATH, NEW).

check_strm(ACC, STRM, NEW) :- 
  read_line_to_codes(STRM, LINE), 
  (
    LINE = end_of_file -> 
    NEW = ACC,
    close(STRM)
  ;
    check_line(ACC, LINE, TEMP), !,
    check_strm(TEMP, STRM, NEW)
  ).

check_path(ACC, PATH, NEW) :- 
  open(PATH, read, STRM), 
  check_strm(ACC, STRM, NEW).

check_name(NAME) :- 
  format("Checking problem = ~w for duplicates\n", NAME),
  empty_assoc(EMP),
  name_probpath(NAME, PROB), 
  check_path(EMP, PROB, _).

main :- 
  findall([PROB]>>(problem(PROB), firstorder(PROB)), PROBS), !,
  exclude(check_name, PROBS, DUPS), !, 
  write("Problems with dups :\n"),
  writeln_list(DUPS).
  
  

