#!/usr/bin/env swipl
:- initialization(main, main).

:- [proof_trace].
:- [prove].
% :- [check].

main :- 
  debug_prvr(PRVR), 
  debug_hints(HINTS), 
  debug_ctx(CTX), 
  debug_clas(CLAS), 
  debug_hyp(HYP), 
  debug_goal(GOAL), 
  guitracer,
  trace, 
  infer(PRVR, HINTS, CTX, CLAS, HYP, GOAL),
  % debug_prob(PROB), 
  % debug_prf(PRF), 
  % check(PROB, 0, PRF).
  true.
