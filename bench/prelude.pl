giga(1073741824).

high_mem(MEM) :- giga(GB), MEM is GB * 14.

inc_mem(NUM) :-
  giga(GB), 
  MEM is GB * NUM,
  set_prolog_flag(stack_limit, MEM).

num_suc(NUM, SUC) :-
  SUC is NUM + 1.

num_pre(NUM, PRE) :-
  0 < NUM,
  PRE is NUM - 1.

drop(0, LIST, LIST). 
drop(NUM, [_ | LIST], REM) :- 
  num_pre(NUM, PRED),
  drop(PRED, LIST, REM).

take(0, _, []). 
take(NUM, [ELEM | LIST], [ELEM | REM]) :- 
  num_pre(NUM, PRED),
  take(PRED, LIST, REM).

slice(DROP, TAKE, LIST, SLICE) :- 
  drop(DROP, LIST, TEMP), 
  take(TAKE, TEMP, SLICE). 

jmap(_, [], []).
jmap(GOAL, [ELEM | LIST], RSTS) :- 
  call(GOAL, ELEM, PFX), !,
  append(PFX, SFX, RSTS),
  jmap(GOAL, LIST, SFX).

imap(_, _, [], []).
imap(GOAL, IDX, [ELEM | LIST], [RST | RSTS]) :- 
  call(GOAL, IDX, ELEM, RST), !,
  num_suc(IDX, SUC),
  imap(GOAL, SUC, LIST, RSTS).

cmap(_, []).

cmap(GOAL, [Elem | List]) :- 
  call(GOAL, Elem), !, 
  cmap(GOAL, List). 

cmap(_, [], []).

cmap(GOAL, [ElemA | ListA], [ElemB | ListB]) :- 
  call(GOAL, ElemA, ElemB), !, 
  cmap(GOAL, ListA, ListB). 

cmap(_, [], [], []).

cmap(GOAL, [ElemA | ListA], [ElemB | ListB], [ElemC | ListC]) :- 
  call(GOAL, ElemA, ElemB, ElemC), !, 
  cmap(GOAL, ListA, ListB, ListC). 

cmap(_, [], [], [], []).

cmap(GOAL, [ElemA | ListA], [ElemB | ListB], [ElemC | ListC], [ElemD | ListD]) :- 
  call(GOAL, ElemA, ElemB, ElemC, ElemD), !, 
  cmap(GOAL, ListA, ListB, ListC, ListD). 
  
take_until_first(CODE, ATOM, PFX) :- 
  atom_codes(ATOM, CODES), !,
  append(PFX_CODES, [CODE | _], CODES), !, 
  atom_codes(PFX, PFX_CODES). 
  
take_until_last(CODE, ATOM, PFX) :- 
  atom_codes(ATOM, CODES), !,
  append(PFX_CODES, [CODE | SFX_CODES], CODES), 
  \+ member(CODE, SFX_CODES), !,
  atom_codes(PFX, PFX_CODES). 

drop_until_last(CODE, ATOM, SFX) :- 
  atom_codes(ATOM, CODES), !,
  append(_, [CODE | SFX_CODES], CODES), 
  \+ member(CODE, SFX_CODES), !,
  atom_codes(SFX, SFX_CODES). 

%     YOU
% FOO/BAR/BAZ/QUUX.QUZ
%             ---- ---
%             ROOT EXT
%             --------
%               BASE
%         ------------
%           REL-PATH
% --------------------
%       ABS-PATH
        

abs_base(ABS, BASE) :- drop_until_last(47, ABS, BASE), !.
abs_base(ABS, ABS).

base_root(BASE, ROOT) :- take_until_last(46, BASE, ROOT), !.
base_root(BASE, BASE). 

abs_root(ABS, ROOT) :- abs_base(ABS, BASE), base_root(BASE, ROOT).

folder_children(FD, CHDR) :-
  directory_files(FD, TEMP), 
  subtract(TEMP, ['.', '..'], CHDR).

codes_concat_with_47([], Y, [47 | Y]) :- !.
codes_concat_with_47([47], Y, [47 | Y]) :- !.
codes_concat_with_47([C], Y, [C , 47 | Y]) :- !.
codes_concat_with_47([C | X], Y, [C | Z]) :- codes_concat_with_47(X, Y, Z).

atom_concat_with_backslash(X, Y, Z) :-
  atom_codes(X, XAS),
  atom_codes(Y, YAS),
  codes_concat_with_47(XAS, YAS, ZAS),
  atom_codes(Z, ZAS).

exists_file_at(FD, BS) :-  
  atom_concat_with_backslash(FD, BS, ABS),
  exists_file(ABS).

exists_directory_at(FD, BS) :-  
  atom_concat_with_backslash(FD, BS, ABS),
  exists_directory(ABS).

folder_bases(FD, BSS) :- 
  folder_children(FD, CHDR), 
  include(exists_file_at(FD), CHDR, BSS). 

folder_roots(FD, RTS) :- 
  folder_bases(FD, BSS), 
  cmap(base_root, BSS, RTS).

folder_folders(FD, FDS) :- 
  folder_children(FD, CHDR), 
  include(exists_directory_at(FD), CHDR, FDS).

write_list(_, []).
write_list(STRM, [ELEM | LIST]) :- 
  writeln(STRM, ELEM),
  write_list(STRM, LIST).

write_list([]).
write_list([ELEM | LIST]) :- 
  writeln(ELEM),
  write_list(LIST).

write_term_punct(STRM, TERM) :- 
  write_term(STRM, TERM, [nl(true), quoted(true), fullstop(true)]).

findall(GOAL, BAG) :- findall(X, call(GOAL, X), BAG).
  
pluck([ELEM | REM], ELEM, REM).
pluck([ELEM | LIST], PLUCK, [ELEM | REM]) :- pluck(LIST, PLUCK, REM).

maplines(GOAL, STM, LIST) :- 
  read_line_to_string(STM, LINE), 
  (
    LINE = end_of_file -> LIST = [] ;
    call(GOAL, LINE, ELEM),
    LIST = [ELEM | REST],
    maplines(GOAL, STM, REST) 
  ).

convlines(GOAL, STM, LIST) :- 
  read_line_to_string(STM, LINE), 
  (
    LINE = end_of_file -> LIST = [] ;
    call(GOAL, LINE, ELEM) -> 
    LIST = [ELEM | REST],
    convlines(GOAL, STM, REST) ;
    convlines(GOAL, STM, LIST) 
  ).

anylines(GOAL, STM, ELEM) :- 
  read_line_to_string(STM, LINE), 
  (
    LINE = end_of_file -> false ;
    call(GOAL, LINE, ELEM) -> true ; 
    anylines(GOAL, STM, ELEM) 
  ).

range(LOW, HIGH, NUMS) :-
  HIGH < LOW ->
  NUMS = []
;
  NUMS = [LOW | TAIL],
  num_suc(LOW, SUC),
  range(SUC, HIGH, TAIL).

goal_time(GOAL, TIME) :- 
  statistics(walltime, [START | _]),
  call(GOAL),
  statistics(walltime, [END | _]),
  TIME is END - START.

format_shell(PATTERN, ARGS, EXIT) :-
  format(string(CMD), PATTERN, ARGS), 
  shell(CMD, EXIT).

add_entry(FILE, ENTRY) :- 
  open(FILE, append, STM),
  write_term_punct(STM, ENTRY),
  close(STM).