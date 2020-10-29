#!/bin/zsh

FILES=`cat TESTS`

echo "Running each test ${1} times"

N=$1

# First run ocaml scripts


echo "Running CertiCoq programs..."
printf "      &   ANF   & ANF OPT & SPEEDUP &   CPS   & CPS OPT & SPEEDUP \n"
for f in $FILES
do
    # Find ANF time    
    timeanf=$(./${f} ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find CPS time
    timecps=$(./${f}_cps ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find ANF OPT time    
    timeanfopt=$(./${f}_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find CPS OPT time
    timecpsopt=$(./${f}_cps_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')

    #Find anf/ocamlopt ratio
    speedupanf=$(awk -v ANF=${timeanf} -v OPT=${timeanfopt} 'BEGIN { print  ( (ANF - OPT) / ANF ) }')
    speedupcps=$(awk -v CPS=${timecps} -v OPT=${timecpsopt} 'BEGIN { print ( (CPS - OPT) / CPS ) }')
    
    ESC='\\'
    # output latex table
    printf "{${ESC}tt ${f}} &  %.3f  &  %.3f  &  %.3f  &  %.3f  &  %.3f  &  %.3f  %s \n" "$timeanf" "$timeanfopt" "$speedupanf" "$timecps" "$timecpsopt" "$speedupcps" "\\\\"
done
