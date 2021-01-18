:- [basic].
:- [vsolve, esolve].
:- [prove, merge].

solve(eprover, TSTP, SOL) :- esolve(TSTP, SOL).
solve(vampire, TSTP, SOL) :- vsolve(TSTP, SOL).

goal_time(GOAL, TIME) :- 
  statistics(walltime, [START | _]),
  call(GOAL),
  statistics(walltime, [END | _]),
  TIME is END - START.

premerge(SOLVER, TPTP, TSTP) :- 
  set_mem_gb(14), !,
  style_check(-singleton), !,
  writeln("Fetching problem..."), !,
  tptp_prob(TPTP, PROB), !,
  writeln("Generating solution..."), !,
  solve(SOLVER, TSTP, SOL), !,
  open(temp, write, STRM, [encoding(octet)]), !,
  empty_assoc(EMP), !,
  writeln("Generating temp file..."), !,
  atom_firstchar(SOLVER, SLVR),
  prove(STRM, SLVR, PROB, SOL, EMP, 0), !,
  close(STRM), !.

main([SOLVER, TPTP, TSTP, TESC | _]) :-
  premerge(SOLVER, TPTP, TSTP), !,
  writeln("Merging problem and temp file..."), !,
  merge(TPTP, temp, TESC), !,
  delete_file(temp), !,
  writeln("Proof complete."), !.
  true. 
