:- [basic, folders].

kernels([attv, rttv, pttv]).

use_kernel(pttv, PROB, PRF) :- 
  format_shell("$TESC/pttv ~w ~w", [PROB, PRF], 0).

use_kernel(attv, PROB, PRF) :- 
  format_shell("$TESC/tts/target/release/tts ~w | $TESC/attv/attv ~w", [PROB, PRF], 0).

use_kernel(rttv, TESC, PROB, PRF) :- 
  format_shell("$TESC/rttv/target/release/rttv ~w ~w", [PROB, PRF], 0).

main(ARGS) :- 
  select_arg('--kernel', ARGS, rttv, ARG), 
  kernels(KERNELS), 
  select_by_prefix(ARG, KERNELS, KERNEL), !,
  append(_, [PROB, PRF], ARGS),
  use_kernel(KERNEL, PROB, PRF).