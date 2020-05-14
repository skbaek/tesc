:- [check].
  
main :- 
  current_prolog_flag(argv, [_, TPTP, TESC]), 
  check(TPTP, TESC).