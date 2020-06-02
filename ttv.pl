% #!/usr/bin/env swipl
% :- initialization(main, main).

:- [check].
  
% main([TPTP, TESC]) :-
%   check(TPTP, TESC).

main :- 
  current_prolog_flag(argv, [_, TPTP, TESC]), 
  check(TPTP, TESC).
