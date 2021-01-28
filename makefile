main: t3p_rs t3p_pl vtv

t3p_rs: FORCE 
	cd ./t3p-rs/ && cargo build --release 

t3p_pl: FORCE
	swipl --goal=main --stand_alone=true -o t3p -c t3p.pl 

vtv: vtv/vtv.agda vtv/verify.lagda vtv/basic.lagda 
	cd ./vtv/ && agda --compile vtv.agda 

FORCE: ;