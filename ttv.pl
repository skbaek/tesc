:- [basic, folders].

kernels([attv, rttv, pttv]).

use_kernel(pttv, TESC, PROB, PRF) :- 
  format_shell("~wpttv ~w ~w", [TESC, PROB, PRF], 0).

use_kernel(attv, TESC, PROB, PRF) :- 
  format_shell("~wtts/target/release/tts ~w | ~wattv/attv ~w", [TESC, PROB, TESC, PRF], 0).

use_kernel(rttv, TESC, PROB, PRF) :- 
  format_shell("~wrttv/target/release/rttv ~w ~w", [TESC, PROB, PRF], 0).

main(ARGS) :- 
  select_arg('--kernel', ARGS, rttv, ARG), 
  kernels(KERNELS), 
  select_by_prefix(ARG, KERNELS, KERNEL), !,
  append(_, [PROB, PRF], ARGS),
  tesc_folder(TESC),
  use_kernel(KERNEL, TESC, PROB, PRF).