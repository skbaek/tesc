% :- module(op, [declare_TPTP_operators/0, tf_form/3, tptp_terms/2]).
:-[basic].

:-op(70,fx,'$$').
:-op(80,fx,'$').
:-op(85,fx,'&').    %----DLF dereference 
:-op(90,xfx,/).     %----Rationals need to bind tighter than =
:-op(100,fx,++).
:-op(100,fx,--).
%----Postfix for !5
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
:-op(405,xfx,'\\=').  
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
% :-op(525,xfx,#).   % Disabled for TESC
% :-op(525,xf,#).   % Disabled for TESC

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
    op(405,xfx,'\\='),
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
%   op(525,xfx,#),   % Disabled for TESC
%   op(525,xf,#),   % Disabled for TESC
    op(550,xfx,':=').

fof_form(_, $true, $true).
fof_form(_, $false, $false).

fof_form(VARS, ~ TPTP, $not(FORM)) :- !, 
 fof_form(VARS, TPTP, FORM).

fof_form(VARS, ! [VAR] : TPTP, $fa(FORM))  :- !,
  fof_form([VAR | VARS], TPTP, FORM).

fof_form(VARS, ! [VAR | REM] : TPTP, $fa(FORM))  :- !,
  fof_form([VAR | VARS], ! REM : TPTP, FORM).

fof_form(VARS, ? [VAR] : TPTP, $ex(FORM))  :- !,
  fof_form([VAR | VARS], TPTP, FORM).

fof_form(VARS, ? [VAR | REM] : TPTP, $ex(FORM))  :- !,
  fof_form([VAR | VARS], ? REM : TPTP, FORM).

fof_form(VARS, (TT_A \= TT_B), FORM) :- !, 
  fof_form(VARS, ~ (TT_A = TT_B), FORM). 

fof_form(VARS, TF_A & TF_B, $and(FORM_A, FORM_B)) :- !,
  fof_form(VARS, TF_A, FORM_A), 
  fof_form(VARS, TF_B, FORM_B).

fof_form(VARS, TF_A | TF_B, $or(FORM_A, FORM_B)) :- !,
  fof_form(VARS, TF_A, FORM_A),
  fof_form(VARS, TF_B, FORM_B).

fof_form(VARS, TF_A => TF_B, $imp(FORM_A, FORM_B)) :- !,
  fof_form(VARS, TF_A, FORM_A), 
  fof_form(VARS, TF_B, FORM_B).

fof_form(VARS, TF_A <=> TF_B, $iff(FORM_A, FORM_B)) :- !,
  fof_form(VARS, TF_A, FORM_A),
  fof_form(VARS, TF_B, FORM_B).

fof_form(VARS, TF_A '~|' TF_B, FORM) :- !,
  fof_form(VARS, ~ (TF_A | TF_B), FORM).

fof_form(VARS, TF_A ~& TF_B, FORM) :- !,
  fof_form(VARS, ~ (TF_A & TF_B), FORM).

fof_form(VARS, TF_A <= TF_B, FORM) :- !,
  fof_form(VARS, TF_B => TF_A, FORM).

fof_form(VARS, TF_A <~> TF_B, FORM) :- !,
  fof_form(VARS, ~ (TF_A <=> TF_B), FORM).

fof_form(VARS, TF, FORM) :- 
  TF =.. [REL | TTS], 
  maplist_cut(tt_term(VARS), TTS, TERMS),
  FORM =.. [REL | TERMS], !.

tf_form(fof, TF, FORM) :-
  fof_form([], TF, FORM).

tf_form(cnf, TF, FORM) :- 
  term_variables(TF, VARS), 
  length(VARS, NUM),
  fof_form(VARS, TF, TEMP), 
  add_fas(NUM, TEMP, FORM).

insert_spaces(IN, OUT) :- 
  re_replace("(~|&|=>|<=>|<~>|:)(~|\\!|\\?|\\$)"/g, "$1 $2", IN, TEMP),
  (
    IN = TEMP -> 
    OUT = TEMP   
  ;
    insert_spaces(TEMP, OUT)
  ).

prep_line(IN, OUT) :- 
  re_replace("!="/g, "\\=", IN, TEMP), 
  insert_spaces(TEMP, OUT).

prep_file(SRC, TGT) :- 
  read_line_to_string(SRC, LINE), 
  (
    LINE = end_of_file -> true 
  ; 
    (
      (
        first_char(LINE, '%') ;
        first_char(LINE, '#') ;
        first_char(LINE, '\n') 
      ) -> prep_file(SRC, TGT) 
    ;
      prep_line(LINE, NORM),
      write(TGT, NORM), 
      write(TGT, "\n"), 
      prep_file(SRC, TGT)
    )
  ).


tptp_terms(FILE, TERMS) :- 
  open(FILE, read, SRC), 
  atomic_concat(FILE, ".temp", TEMP),
  open(TEMP, write, TGT), 
  prep_file(SRC, TGT), 
  close(SRC),
  close(TGT),
  % atomic_concat("cat ", TEMP, CMD),
  % shell(CMD),
  read_file_to_terms(TEMP, TERMS, []),
  delete_file(TEMP),
  true.
