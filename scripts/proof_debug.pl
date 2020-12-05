#!/usr/bin/env swipl
:- initialization(main, main).

:- ['../prove'].
:- ['../proof_trace'].

main :- 
  debug_prvr(PRVR), 
  debug_hints(HINTS), 
  debug_ctx(CTX), 
  debug_hyp(HYP), 
  debug_goal(GOAL), 
  trace, 
  infer(PRVR, HINTS, CTX, HYP, GOAL),
  % debug_prob(PROB), 
  % debug_prf(PRF), 
  % check(PROB, 0, PRF).
  true.
