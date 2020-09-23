cd basic/
cargo build --release
cd ../tts/
cargo build --release
cd ../rttv/
cargo build --release
cd ..
agda --compile attv.agda
swipl --goal=main --stand_alone=true -o pttv -c pttv.pl 
swipl --goal=main --stand_alone=true -o ttv -c ttv.pl 


