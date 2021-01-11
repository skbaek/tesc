:- [basic, folders].

kernels([attv, attv_old, rttv, pttv, pttv2]).

use_kernel(pttv, TESC, PROB, PRF) :- 
  format_shell("~wpttv ~w ~w", [TESC, PROB, PRF], 0).

use_kernel(pttv_old, TESC, PROB, PRF) :- 
  format_shell("~wpttv_old ~w ~w", [TESC, PROB, PRF], 0).

use_kernel(attv, TESC, PROB, PRF) :- 
  format_shell("./tts/target/release/tts ~w | ~wattv/attv ~w", [PROB, TESC, PRF], 0).

use_kernel(attv_old, TESC, PROB, PRF) :- 
  format_shell("./tts/target/release/tts ~w | ~wattv/attv_old ~w", [PROB, TESC, PRF], 0).

use_kernel(rttv, TESC, PROB, PRF) :- 
  format_shell("~wrttv/target/release/rttv ~w ~w", [TESC, PROB, PRF], 0).

use_kernel(rttv_old, TESC, PROB, PRF) :- 
  format_shell("~wrttv/target/release/rttv_old ~w ~w", [TESC, PROB, PRF], 0).

main(ARGS) :- 
  select_arg('--kernel', ARGS, rttv, ARG), 
  kernels(KERNELS), 
  select_by_prefix(ARG, KERNELS, KERNEL), !,
  append(_, [PROB, PRF], ARGS),
  tesc_folder(TESC),
  use_kernel(KERNEL, TESC, PROB, PRF).