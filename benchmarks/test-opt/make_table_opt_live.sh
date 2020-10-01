#!/bin/zsh

FILES=`cat TESTS`

echo "Running each test ${1} times"

N=$1

# First run ocaml scripts


echo "Running CertiCoq programs..."
printf "      &  LIVE 0  &  LIVE 1  &  LIVE 2  &  LIVE 10 \n"
for f in $FILES
do
    # Find ANF time    
    time0=$(./${f}_opt3 ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    time1=$(./${f}_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    time2=$(./${f}_opt4 ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    time10=$(./${f}_opt5 ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    
    ESC='\\'
    # output latex table
    printf "{${ESC}tt ${f}} &  %.3f  &  %.3f  &  %.3f  &  %.3f  \n" "$time0" "$time1" "$time2" "$time10"
done
