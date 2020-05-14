:- [prove, solve].

main :- 
  current_prolog_flag(argv, [_, PRVR, TPTP, TSTP, TXTX]), 
  set_prolog_flag(stack_limit, 2_147_483_648),
  style_check(-singleton),
  pose(TPTP, PIDS, PROB),
  solve(PRVR, PIDS, TSTP, SOL),
  open(TXTX, write, STRM, [encoding(octet)]),
  prove(STRM, none, PRVR, SOL, PROB),
  close(STRM).