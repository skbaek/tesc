:- [debug_trace].

debug :- 
  debug_prvr(PRVR), 
  debug_hints(HINTS), 
  debug_ctx(CTX), 
  debug_hyp(HYP), 
  debug_goal(GOAL), 
  debug_prob(PROB), 
  debug_prf(PRF), 
  infers(PRVR, HINTS, CTX, HYP, GOAL),
  check(PROB, 0, PRF).
