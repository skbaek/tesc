:- [basic, vsolve, esolve, prove, verify].

kernels([fast, verified, debug]).

use_kernel(debug, PROB, PRF) :- verify(PROB, PRF).

use_kernel(verified, PROB, PRF) :- 
  format_shell("$TESC/t3p-rs/target/release/t3p serialize ~w | $TESC/vtv/vtv ~w", [PROB, PRF], 0).

use_kernel(fast, PROB, PRF) :- 
  format_shell("$TESC/t3p-rs/target/release/t3p verify ~w ~w", [PROB, PRF], 0).

solve(eprover, TSTP, SOL) :- esolve(TSTP, SOL).
solve(vampire, TSTP, SOL) :- vsolve(TSTP, SOL).

main(['verify' | ARGS]) :-
  select_arg('--kernel', ARGS, fast, ARG), 
  kernels(KERNELS), 
  select_by_prefix(ARG, KERNELS, KERNEL), !,
  append(_, [PROB, PRF], ARGS),
  use_kernel(KERNEL, PROB, PRF). 

main(['compile', SOLVER, TPTP, TSTP, TESC]) :-
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
  close(STRM), !,
  writeln("Merging problem and temp file..."), !,
  format_shell("$TESC/t3p-rs/target/release/t3p relabel ~w temp ~w", [TPTP, TESC], 0),
  delete_file(temp), !,
  writeln("Proof complete."), !.