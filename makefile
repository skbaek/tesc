main: tts ttc ttv rttv attv pttv 

tts: FORCE 
	cd ./tts/ && cargo build --release 

ttc: FORCE
	swipl --goal=main --stand_alone=true -o ttc -c ttc.pl 

ttv: FORCE
	swipl --goal=main --stand_alone=true -o ttv -c ttv.pl 

attv: attv/attv.agda attv/verify.agda attv/basic.agda 
	cd ./attv/ && agda --compile attv.agda 

pttv: FORCE
	swipl --goal=main --stand_alone=true -o pttv -c pttv.pl 

rttv: FORCE
	cd ./rttv/ && cargo build --release 

FORCE: ;