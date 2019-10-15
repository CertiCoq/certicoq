#!/bin/sh

sh mkexecT.sh $1
sh mkexecT.sh $1old

start=`gdate +%s.%6N`
./$1ccomp.out
end=`gdate +%s.%6N`
ccomp=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldccomp.out
end=`gdate +%s.%6N`
ccompold=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1.out
end=`gdate +%s.%6N`
llvm=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1old.out
end=`gdate +%s.%6N`
llvmold=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1Frame.out
end=`gdate +%s.%6N`
llvmframe=$(bc -l <<<"${end} - ${start}")

start=`gdate +%s.%6N`
./$1oldFrame.out
end=`gdate +%s.%6N`
llvmframeold=$(bc -l <<<"${end} - ${start}")

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
./$1oldCCFrame.out
end=`gdate +%s.%6N`
ghcframeold=$(bc -l <<<"${end} - ${start}")

printf "|\t\tOptions\t\t|\tCompCert\t|\tLLVM\t\t|\tLLVM ghcc\t|\n"
printf "|\t%s\t|\t%f\t|\t%f\t|\t%f\t|\n" "no params, w/ frame" $ccompold $llvmframeold $ghcframeold
printf "|\t%s\t|\t%s\t\t|\t%f\t|\t%f\t|\n" "no params, w/o frame" "N/A" $llvmold $ghcold
printf "|\t%s\t|\t%f\t|\t%f\t|\t%f\t|\n" "params, w/ frame" $ccomp $llvmframe $ghcframe
printf "|\t%s\t|\t%s\t\t|\t%f\t|\t%f\t|\n" "params, w/o frame" "N/A" $llvm $ghc 
