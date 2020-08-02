#!/usr/bin/env swipl
:- initialization(main, main).

:- [op].

first( 
  ! [U] :
        ( ssList(U)
       => ! [V] :
            ( ssList(V)
           => ! [W] :
                ( ssList(W)
               => ! [X] :
                    ( ssList(X)
                   => ( V != X
                      | U != W
                      | ? [Y] :
                          ( ssItem(Y)
                          & ! [Z] :
                              ( ssItem(Z)
                             => ( ~ memberP(U,Z)
                                | Y = Z ) ) )
                      | ( ! [X1] :
                            ( ssItem(X1)
                           => ( cons(X1,nil) != W
                              | ~ memberP(X,X1)
                              | ? [X2] :
                                  ( ssItem(X2)
                                  & X1 != X2
                                  & memberP(X,X2)
                                  & leq(X1,X2) ) ) )
                        & ( nil != X
                          | nil != W ) ) ) ) ) ) ) ).


second(
  ![X1]:(ssList(X1)=>![X2]:(ssList(X2)=>![X3]:(ssList(X3)=>![X4]:(ssList(X4)=>(X2!=X4|X1!=X3|?[X5]:(ssItem(X5)&![X6]:(ssItem(X6)=>(~(memberP(X1,X6))|X5=X6)))|(![X7]:(ssItem(X7)=>(cons(X7,nil)!=X3|~(memberP(X4,X7))|?[X8]:(((ssItem(X8)&X7!=X8)&memberP(X4,X8))&leq(X7,X8))))&(nil!=X4|nil!=X3)))))))
).

compare(! X : P, ! X : Q) :- compare(P, Q).
compare(? X : P, ? X : Q) :- compare(P, Q).

compare(P1 => P2, Q1 => Q2) :- compare(P1, Q1), compare(P2, Q2).
compare(P1 <=> P2, Q1 <=> Q2) :- compare(P1, Q1), compare(P2, Q2).
compare(P1 & P2, Q1 & Q2) :- compare(P1, Q1), compare(P2, Q2).
compare(P1 | P2, Q1 | Q2) :- compare(P1, Q1), compare(P2, Q2).

compare(X, X).

main :- 
  declare_TPTP_operators,
  guitracer,
  trace, 
  first(X),
  second(Y),
  compare(X, Y).
  


