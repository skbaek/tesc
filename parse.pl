#!/usr/bin/env swipl
:- initialization(main, main).

% fof(_, _, _).
% cnf(_, _, _).

:-op(70,fx,'$$').
:-op(80,fx,'$').
:-op(85,fx,'&').    %----DLF dereference 
:-op(90,xfx,/).     %----Rationals need to bind tighter than =
:-op(100,fx,++).
:-op(100,fx,--).
%----Postfix for !=
:-op(100,xf,'!').
%---- .. used for range in tptp2X. Needs to be stronger than :
:-op(400,xfx,'..').
%----! and ? are of higher precedence than : so ![X]:p(X) is :(![X],p(X))
%----Otherwise ![X]:![Y]:p(X,Y) cannot be parsed.
%----! is fy so Prolog can read !! (blah) as !(!(blah)) and it gets fixed
:-op(400,fy,!).
:-op(400,fx,?).
:-op(400,fx,^).
:-op(400,fx,'!>').
:-op(400,fx,'?*').
:-op(400,fx,'@-').
:-op(400,fx,'@+').
:-op(401,fx,'@@-').
:-op(401,fx,'@@+').
:-op(402,fx,'!!').
:-op(402,fx,'??').
:-op(403,yfx,*).     %----X product
:-op(403,yfx,+).     %----Union
%----DLF ++ and ** and <+> and -= stronger than = and << and >>
:-op(403,yfx,'**').  %----DLF intersection
:-op(403,yfx,'++').  %----DLF union
:-op(403,yfx,'<+>'). %----DLF disjoint union
%----= must bind more tightly than : for ! [X] : a = X. = must binder looser
%----than quantifiers for otherwise X = ! [Y] : ... is a syntax error (the =
%----grabs the quantifier). That means for THF it is necessary to bracket 
%----formula terms, e.g., a = (! [X] : p(X))
:-op(405,xfx,'=').
%---!= not possible because ! is special - see postfix cheat :-op(405,xfx,'!=').
:-op(440,xfy,>).     %----Type arrow
:-op(450,xfx,'-=').  %----DLF role inverse_of
:-op(450,xfx,'<>').  %----DLF class disjoint
:-op(450,xfx,'<<').  %----DLF subclass, Subtype arrow
:-op(450,xfx,'>>').  %----DLF superclass
%----Need : stronger than binary connectives for ! [X] : p(X) <=> !Y ...
%----Need ~ and : equal and right-assoc for ![X] : ~p and for ~![X] : ...
:-op(450,fy,~).      %----Logical negation
:-op(450,xfy,:).
:-op(501,yfx,@).
% :-op(502,xfy,'|').
:-(system_mode(true),op(502,xfy,'|'),system_mode(false)).
:-op(502,xfx,'~|').
:-op(503,xfy,&).
:-op(503,xfx,~&).
:-op(504,xfx,=>).
:-op(504,xfx,<=).
:-op(505,xfx,<=>).
:-op(505,xfx,<~>).
:-op(510,xfx,-->).

%----DLF separators, very weak, but stronger than :=
:-op(525,xfx,#).
:-op(525,xf,#).

:-op(550,xfx,:=).

%----DLF == is built in, precedence 700 - weak!
%------------------------------------------------------------------------------
%----Runtime version of operators
declare_TPTP_operators:-
    op(70,fx,'$$'),
    op(80,fx,'$'),
    op(85,fx,'&'),
    op(90,xfx,/),
    op(100,fx,++),
    op(100,fx,--),
    op(100,xf,'!'),
    op(400,xfx,'..'),
    op(400,fy,!),
    op(400,fx,?),
    op(400,fx,^),
    op(400,fx,'!>'),
    op(400,fx,'?*'),
    op(400,fx,'@-'),
    op(400,fx,'@+'),
    op(400,fx,'@@-'),
    op(400,fx,'@@+'),
    op(402,fx,'!!'),
    op(402,fx,'??'),
    op(403,yfx,*),
    op(403,yfx,+),
    op(403,yfx,'**'),
    op(403,yfx,'++'),
    op(403,yfx,'<+>'),
    op(405,xfx,'='),
    op(440,xfy,>),
    op(450,yfx,'-='),
    op(450,yfx,'<>'),
    op(450,xfx,'<<'),
    op(450,xfx,'>>'),
    op(450,fy,~),
    op(450,xfy,:),
    op(501,yfx,@),
%    op(502,xfy,'|'),
    (system_mode(true),op(502,xfy,'|'),system_mode(false)),
    op(502,xfx,'~|'),
    op(503,xfy,&),
    op(503,xfx,~&),
    op(504,xfx,=>),
    op(504,xfx,<=),
    op(505,xfx,<=>),
    op(505,xfx,<~>),
    op(510,xfx,-->),
    op(525,xfx,#),
    op(525,xf,#),
    op(550,xfx,':=').

tptp_directory("/home/sk/programs/TPTP").

current_directory(X) :-
  working_directory(X, X).

name_cat(NAME, CAT) :- 
  atom_chars(NAME, [A, B, C | _]), 
  atomic_list_concat([A, B, C], CAT).


% print_clause_name :- 
%   cnf(NAME, _, _), write(NAME) ;
%   fof(NAME, _, _), write(NAME).
% 
% print_clause_names :- 
%   findall(c, print_clause_name, _).

% retract_all_tptp_clauses :- 
%   dynamic(cnf/3),
%   dynamic(fof/3),
%   retractall(cnf(_, _, _)),
%   retractall(fof(_, _, _)).

% prep :- 
%   style_check(-singleton),
%   retract_all_tptp_clauses,
%   declare_TPTP_operators.

write_list([]).
write_list([ELEM | LIST]) :- 
  write(ELEM), nl,
  write_list(LIST).

is_include(include(_)).

include_terms(include(AXIOM), TERMS) :- 
  tptp_directory(TPTP), 
  atomics_to_string([TPTP, "/", AXIOM], PATH),
  read_file_to_terms(PATH, TERMS, []).
  
tptp_prob(PATH, PROB) :- 
  style_check(-singleton),
  % retract_all_tptp_clauses,
  declare_TPTP_operators,
  % tptp_directory(TPTP_DIR), 
  % current_directory(CURR_DIR), 
  % cd(TPTP_DIR),
  % name_cat(NAME, CAT),
  % atomic_list_concat(["Problems/", CAT, "/", NAME, ".p"], PATH),
  read_file_to_terms(TPTP, TERMS, []),
  partition(is_include, TERMS, INCLS, ORIG),
  maplist(include_terms, INCLS, AXIOMSS),
  append([ORIG | AXIOMSS], PRECLAS),
  maplist(precla_cla, PRECLAS, PROB), 
  true.
