:- [debug_trace].

debug :- 
  debug_ctx(CTX), 
  debug_ant(ANT), 
  % debug_prob(PROB), 
  % debug_prf(PRF), 
  e_tup_insts(CTX, ANT, INSTS).
  % verify(PROB, 0, PRF).
