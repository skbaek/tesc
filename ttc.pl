:- [basic].
:- [vsolve, esolve].
:- [prove, merge].

solve(e, TSTP, SOL) :- esolve(TSTP, SOL).
solve(v, TSTP, SOL) :- vsolve(TSTP, SOL).

main([SOLVER, TPTP, TSTP, TESC | OPTS]) :-
  trace_if_debug(OPTS),
  set_mem_gb(14),
  style_check(-singleton),
  atom_firstchar(SOLVER, SLVR),
  writeln("Fetching problem..."),
  tptp_prob(TPTP, PROB), !,
  writeln("Generating solution..."), !,
  solve(SLVR, TSTP, SOL), !,
  open(temp, write, STRM, [encoding(octet)]),
  empty_assoc(EMP),
  writeln("Generating temp file..."), !,
  prove(STRM, SLVR, PROB, SOL, EMP, 0), !,
  close(STRM), 
  writeln("Merging problem and temp file..."), !,
  merge(TPTP, temp, TESC), !,
  delete_file(temp),
  writeln("Proof complete.").
