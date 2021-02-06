#!/usr/bin/env swipl
:- initialization(main, main).

:-[ 
  '$HOME/scripts/prelude',
  problems,
  solutions, 
  proofs,
  verifications
].

header( 
  [
    name, 'first-order', unsatisfiable, 'well-formed', 'unique names', 

    'vampire solution result',  
    'vampire solution time (ms)', 'vampire TSTP size (bytes)', 

    'vampire compilation result',
    'vampire compilation time (ms)', 'vampire TESC size (bytes)',

    'vampire VTV verification result',
    'vampire VTV verification time (ms)', 'vampire VTV verification memory (kb)',

    'vampire OTV verification result',
    'vampire OTV verification time (ms)', 'vampire OTV verification memory (kb)',

    'eprover solution result',  
    'eprover solution time (ms)', 'eprover TSTP size (bytes)', 

    'eprover compilation result',
    'eprover compilation time (ms)', 'eprover TESC size (bytes)',

    'eprover VTV verification result',
    'eprover VTV verification time (ms)', 'eprover VTV verification memory (kb)',

    'eprover OTV verification result',
    'eprover OTV verification time (ms)', 'eprover OTV verification memory (kb)'
  ]
).

fo(NAME, VAL) :- firstorder(NAME) -> VAL = yes ; VAL = no.

unsat(NAME, VAL) :- 
  fo(NAME, yes) -> (unsat(NAME) -> VAL = yes ; VAL = no)
; 
  VAL = 'N/A'.

wf(NAME, VAL) :- 
  unsat(NAME, yes) -> (ill_formed(NAME) -> VAL = no ; VAL = yes) 
; 
  VAL = 'N/A'.

unq(NAME, VAL) :- 
  wf(NAME, yes) -> (dup(NAME) -> VAL = no ; VAL = yes)
; 
  VAL = 'N/A'.

vsol(NAME, 'N/A', 'N/A', 'N/A') :- (unq(NAME, 'N/A') ; unq(NAME, no)), !.
vsol(NAME, success, VS_TIME, VS_SIZE) :- solution(vampire, NAME, passed(VS_TIME, VS_SIZE)).
vsol(NAME, failure, 'N/A', 'N/A') :- solution(vampire, NAME, failed).

esol(NAME, 'N/A', 'N/A', 'N/A') :- (unq(NAME, 'N/A') ; unq(NAME, no)), !.
esol(NAME, success, ES_TIME, ES_SIZE) :- solution(eprover, NAME, passed(ES_TIME, ES_SIZE)).
esol(NAME, failure, 'N/A', 'N/A') :- solution(eprover, NAME, failed).

vprf(NAME, 'N/A', 'N/A', 'N/A') :- \+ vsol(NAME, success, _, _), !.
vprf(NAME, success, VP_TIME, VP_SIZE) :- proof(vampire, NAME, passed(VP_TIME, VP_SIZE)).
vprf(NAME, failure, 'N/A', 'N/A') :- proof(vampire, NAME, failed).

eprf(NAME, 'N/A', 'N/A', 'N/A') :-  \+ esol(NAME, success, _, _), !.
eprf(NAME, success, EP_TIME, EP_SIZE) :- proof(eprover, NAME, passed(EP_TIME, EP_SIZE)).
eprf(NAME, failure, 'N/A', 'N/A') :- proof(eprover, NAME, failed).

vvv(NAME, 'N/A', 'N/A', 'N/A') :- \+ vprf(NAME, success, _, _), !.
vvv(NAME, success, VVV_TIME, VVV_MEM) :- verification(vampire, vtv, NAME, passed(VVV_TIME, VVV_MEM)).
vvv(NAME, failure, 'N/A', 'N/A') :- verification(vampire, vtv, NAME, failed).

vvo(NAME, 'N/A', 'N/A', 'N/A') :- \+ vprf(NAME, success, _, _), !. 
vvo(NAME, success, VVO_TIME, VVO_MEM) :- verification(vampire, otv, NAME, passed(VVO_TIME, VVO_MEM)).
% vvo(NAME, failure, 'N/A', 'N/A') :- verification(vampire, otv, NAME, failed).

evv(NAME, 'N/A', 'N/A', 'N/A') :- \+ eprf(NAME, success, _, _), !. 
evv(NAME, success, TIME, MEM) :- verification(eprover, vtv, NAME, passed(TIME, MEM)).
% evv(NAME, failure, 'N/A', 'N/A') :- verification(eprover, vtv, NAME, failed).

evo(NAME, 'N/A', 'N/A', 'N/A') :- \+ eprf(NAME, success, _, _), !. 
evo(NAME, success, TIME, MEM) :- verification(eprover, otv, NAME, passed(TIME, MEM)).
% evo(NAME, failure, 'N/A', 'N/A') :- verification(eprover, otv, NAME, failed).

name_data(
  NAME, 
  [
    NAME, FO, UNSAT, WF, UNQ, 
    VSOL, VS_TIME, VS_SIZE, VPRF, VP_TIME, VP_SIZE, VVV, VVV_TIME, VVV_MEM, VVO, VVO_TIME, VVO_MEM,  
    ESOL, ES_TIME, ES_SIZE, EPRF, EP_TIME, EP_SIZE, EVV, EVV_TIME, EVV_MEM, EVO, EVO_TIME, EVO_MEM
  ]
) :- 
  fo(NAME, FO),
  unsat(NAME, UNSAT),
  wf(NAME, WF),
  unq(NAME, UNQ),
  vsol(NAME, VSOL, VS_TIME, VS_SIZE),
  esol(NAME, ESOL, ES_TIME, ES_SIZE),
  vprf(NAME, VPRF, VP_TIME, VP_SIZE),
  eprf(NAME, EPRF, EP_TIME, EP_SIZE),
  vvv(NAME, VVV, VVV_TIME, VVV_MEM),
  vvo(NAME, VVO, VVO_TIME, VVO_MEM),
  evv(NAME, EVV, EVV_TIME, EVV_MEM),
  evo(NAME, EVO, EVO_TIME, EVO_MEM).

name_data(NAME, _) :- format("CANNOT FILL = ~w\n", NAME), false.

main :- 
  findall(NAME, problem(NAME), NAMES), 
  header(HDR),
  cmap(name_data, NAMES, DATA), 
  write_csv("results.csv", [HDR | DATA]).
