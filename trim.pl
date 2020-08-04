#!/usr/bin/env swipl

:- initialization(main, main).
% :- use_module(library(shell)).
:- [basic].

readfile(TEMP, TERMS) :-
  read_file_to_terms(TEMP, TERMS, []).

is_import(:- _).

def_head_body(X :- Y, X, Y) :- !.
def_head_body(X, X, none).

% get_pred(TERM, PRED) :- 
%   split_head_body(TERM, HEAD, _), 
%   HEAD =.. [PRED | _].

def_pa_body(DEF, (PRED, ARITY), BODY) :- 
  def_head_body(DEF, HEAD, BODY), 
  HEAD =.. [PRED | ARGS], 
  length(ARGS, ARITY).

is_term(X) :-
  X =.. ARGS,
  write("ERROR!"), nl, nl,
  format("~w is not a term, decomposes to : ", [X | ARGS]).

vars(0, []) :- !.
vars(NUM, [_ | VARS]) :- 
  num_pred(NUM, PRED), 
  vars(PRED, VARS).

is_used_core(BODY, TERM) :- 
  sub_term(SUB, BODY), 
  \+ var(SUB), 
  SUB = TERM.

% is_used(BODY, (PRED, ARITY)) :- 
%   vars(ARITY, VARS),
%   TERM =.. [PRED | VARS], 
%   is_used_core(BODY, TERM).

is_used(DEFS, PA_A) :- 
  member(DEF, DEFS), 
  def_pa_body(DEF, PA_B, BODY),
  PA_A \= PA_B,
  PA_A = (PRED, _),
  pred_used(PRED, BODY).

pred_used(PRED, TERM) :- 
  \+ var(TERM), 
  TERM =.. [REL | TERMS], 
  (
    PRED == REL 
  ; 
    member(SUB, TERMS), 
    pred_used(PRED, SUB)
  ).

  


main :- 
  %dir_files(".", X),
  %delete(X, 'ttv.pl', Y),
  %delete(Y, 'ttc.pl', Z),
  %delete(Z, 'mv_nc.pl', A),
  %delete(A, '.gitignore', B),
  %delete(B, '.git', C),
  %delete(C, 'trim.pl', FILES),
  %maplist_cut(readfile, FILES, TERMSS),
  % FILES = ['prove.pl', 'solve.pl', 'check.pl', 'basic.pl'],
FILES = ['basic.pl', 'check.pl', 'esolve.pl', 'vsolve.pl', 'solve.pl', 'prove.pl'],
  maplist_cut(readfile, FILES, TERMSS),
  append(TERMSS, TERMS),
  exclude(is_import, TERMS, DEFS),
  maplist(def_pa_body, DEFS, PAS, _),
  sort(PAS, SORTED),
  nl, nl,
  % write_list(SORTED), 
  partition(is_used(DEFS), SORTED, USED, UNUSED),
  write("USED = "), nl, nl,
  write_list(USED), nl, nl,
  write("UNUSED = "), nl, nl,
  write_list(UNUSED), nl, nl.
  