#!/bin/sh
#sh mkexec.sh $1 -make-ocaml


if [ "$3" = '-make-exec' ]; then 
    sh mkexec.sh $1
    sh mkexec.sh $1old
fi

reps=500
if [ "$2" != '' ]; then
    reps=$2
fi

native=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1.native  
    end=`gdate +%s.%6N`
    native=$(bc -l <<<"${native} + (${end} - ${start})")
done

byte=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1.byte
    end=`gdate +%s.%6N`
    byte=$(bc -l <<<"${byte} + (${end} - ${start})")
done

ccomp=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1ccomp.out  
    end=`gdate +%s.%6N`
    ccomp=$(bc -l <<<"${ccomp} + (${end} - ${start})")
done

ccompold=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1oldccomp.out  
    end=`gdate +%s.%6N`
ccompold=$(bc -l <<<"${ccompold} + (${end} - ${start})")
done

llvm=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1.out  
    end=`gdate +%s.%6N`
    llvm=$(bc -l <<<"${llvm} + (${end} - ${start})")
done

llvmold=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1old.out  
    end=`gdate +%s.%6N`
    llvmold=$(bc -l <<<"${llvmold} + (${end} - ${start})")
done

llvmframe=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1Frame.out  
    end=`gdate +%s.%6N`
    llvmframe=$(bc -l <<<"${llvmframe} + (${end} - ${start})")
done

llvmframeold=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1oldFrame.out  
    end=`gdate +%s.%6N`
    llvmframeold=$(bc -l <<<"${llvmframeold} + (${end} - ${start})")
done

ghc=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1CC.out  
    end=`gdate +%s.%6N`
    ghc=$(bc -l <<<"${ghc} + (${end} - ${start})")
done

ghcframe=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1CCFrame.out  
    end=`gdate +%s.%6N`
    ghcframe=$(bc -l <<<"${ghcframe} + (${end} - ${start})")
done

ghcold=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1oldCC.out  
    end=`gdate +%s.%6N`
    ghcold=$(bc -l <<<"${ghcold} + (${end} - ${start})")
done

ghcframeold=0.0
for (( c=0; c <= $reps; c++ ))
do
    start=`gdate +%s.%6N`
    ./$1oldCCFrame.out  
    end=`gdate +%s.%6N`
    ghcframeold=$(bc -l <<<"${ghcframeold} + (${end} - ${start})")
done

printf "|\t\tOptions\t\t|\tCompCert\t|\tLLVM\t\t|\tLLVM ghcc\t|\tOCaml native\t|\tOCaml byte\t|\n"
printf "|\t%s\t|\t%f\t|\t%f\t|\t%f\t|\t%s\t\t|\t%s\t\t|\n" "no params, w/ frame" $ccompold $llvmframeold $ghcframeold "N/A" "N/A"
printf "|\t%s\t|\t%s\t\t|\t%f\t|\t%f\t|\t%s\t\t|\t%s\t\t|\n" "no params, w/o frame" "N/A" $llvmold $ghcold "N/A" "N/A"
printf "|\t%s\t|\t%f\t|\t%f\t|\t%f\t|\t%s\t\t|\t%s\t\t|\n" "params, w/ frame" $ccomp $llvmframe $ghcframe "N/A" "N/A"
printf "|\t%s\t|\t%s\t\t|\t%f\t|\t%f\t|\t%s\t\t|\t%s\t\t|\n" "params, w/o frame" "N/A" $llvm $ghc "N/A" "N/A"
printf "|\t\t%s\t\t|\t%s\t\t|\t%s\t\t|\t%s\t\t|\t%f\t|\t%f\t|\n" "ocaml" "N/A" "N/A" "N/A" $native $byte
