:- [solve].

is_axiom(CLA) :- 
  CLA =.. [_, _, _, _, file(_, _)].

is_axiom(CLA) :- 
  CLA =.. [_, _, _, _, INFO],
  INFO =.. [inference, TYPE | _],
  axiomatic(TYPE).

cmp_vamp(ORD, CLA_A, CLA_B) :- 
  CLA_A =.. [_, ID_A | _],
  CLA_B =.. [_, ID_B | _],
  compare(ORD, ID_A, ID_B).

tstp_test(FILE) :- 
  tptp_terms(FILE, TERMS), 
  partition(is_axiom, TERMS, TEMP_AXMS, REST),
  write("Axioms : "), nl, nl,
  predsort(cmp_vamp, TEMP_AXMS, AXMS),
  write_list(AXMS),
  write("Rest : "), nl, nl,
  write_list(REST).
