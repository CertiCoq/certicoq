#!/bin/sh

#sh mkexecT.sh $1
#sh mkexecT.sh $1old
#sh mkexecT.sh $1oldopt
#sh mkexecT.sh $1opt

start=`gdate +%s.%6N`
./$1ccomp.out
end=`gdate +%s.%6N`
ccomp=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldccomp.out
end=`gdate +%s.%6N`
ccompold=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldoptccomp.out
end=`gdate +%s.%6N`
ccompoldopt=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1.out
end=`gdate +%s.%6N`
llvm=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1old.out
end=`gdate +%s.%6N`
llvmold=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldopt.out
end=`gdate +%s.%6N`
llvmoldopt=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1Frame.out
end=`gdate +%s.%6N`
llvmframe=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldFrame.out
end=`gdate +%s.%6N`
llvmframeold=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldoptFrame.out
end=`gdate +%s.%6N`
llvmframeoldopt=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1CC.out
end=`gdate +%s.%6N`
ghc=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1CCFrame.out
end=`gdate +%s.%6N`
ghcframe=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldCC.out
end=`gdate +%s.%6N`
ghcold=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldoptCC.out
end=`gdate +%s.%6N`
ghcoldopt=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldCCFrame.out
end=`gdate +%s.%6N`
ghcframeold=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldoptCCFrame.out
end=`gdate +%s.%6N`
ghcframeoldopt=$(bc -l <<<"${end} - ${start}")

printf "|\t\toptions\t\t\t|\tCompCert\t|\tLLVM\t\t|\tLLVM ghcc\t|\n"
printf "|\t%s\t\t|\t%f\t|\t%f\t|\t%f\t|\n" "no param, w/ frame" $ccompold $llvmframeold $ghcframeold
printf "|\t%s\t\t|\t%s\t\t|\t%f\t|\t%f\t|\n" "no param, w/o frame" "N/A" $llvmold $ghcold
printf "|\t%s\t\t|\t%f\t|\t%f\t|\t%f\t|\n" "no param, opt, w/ frame" $ccompoldopt $llvmframeoldopt $ghcframeoldopt
printf "|\t%s\t|\t%s\t\t|\t%f\t|\t%f\t|\n" "no param, opt, w/o frame" "N/A" $llvmoldopt $ghcoldopt
printf "|\t%s\t\t\t|\t%f\t|\t%f\t|\t%f\t|\n" "param, w/ frame" $ccomp $llvmframe $ghcframe
printf "|\t%s\t\t|\t%s\t\t|\t%f\t|\t%f\t|\n" "param, w/o frame" "N/A" $llvm $ghc 
