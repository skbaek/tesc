main: tts ttc ttv rttv attv pttv pttv_old

attv: attv/attv.agda attv/verify.agda attv/basic.agda 
	cd ./attv/ && agda --compile attv.agda 

tts: FORCE 
	cd ./tts/ && cargo build --release 

rttv: FORCE
	cd ./rttv/ && cargo build --release 

pttv: FORCE
	swipl --goal=main --stand_alone=true -o pttv -c pttv.pl 

pttv_old: FORCE
	swipl --goal=main --stand_alone=true -o pttv_old -c pttv_old.pl 

ttc: FORCE
	swipl --goal=main --stand_alone=true -o ttc -c ttc.pl 

ttv: FORCE
	swipl --goal=main --stand_alone=true -o ttv -c ttv.pl 

FORCE: ;