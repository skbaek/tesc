:- [basic, paths].

main :- 
  current_prolog_flag(argv, [PROB_PATH, PRF_PATH | OPTS]), 
  tesc_path(TESC_PATH),
  (
    member('-p', OPTS) -> 
    atomic_concat(TESC_PATH, pttv, PTTV_PATH), !,
    concat_shell([PTTV_PATH, PROB_PATH, PRF_PATH | OPTS], " ", 0)
  ;
    member('-a', OPTS) -> 
    atomic_concat(TESC_PATH, attv, ATTV_PATH), !,
    concat_shell(['./tts/target/release/tts', PROB_PATH, "|", ATTV_PATH, PRF_PATH | OPTS], " ", 0)
  ;
    atomic_concat(TESC_PATH, 'rttv/target/release/rttv', RTTV_PATH), !,
    concat_shell([RTTV_PATH, PROB_PATH, PRF_PATH | OPTS], " ", 0)
  ).