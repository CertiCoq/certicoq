#!/bin/zsh

FILES=`cat TESTS`

echo "Running each test ${1} times"

N=$1

# First run ocaml scripts

# Compare no inlining in wrappers  vs. inlining known functions in wrappers

echo "Running CertiCoq programs..."
printf "      & ANF OPT & ANF OPT INL & SPEEDUP & CPS OPT & CPS OPT INL & SPEEDUP \n"

for f in $FILES
do
    # Find ANF OPT time    
    timeanfo=$(./${f}_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find CPS OPT time
    timecpso=$(./${f}_cps_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find ANF OPT time    
    timeanfoinl=$(./${f}_opt2 ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find CPS OPT time
    timecpsoinl=$(./${f}_cps_opt2 ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')

    #Find anf/ocamlopt ratio
    speedupanf=$(awk -v ANF=${timeanfo} -v OPT=${timeanfoinl} 'BEGIN { print  ( (ANF - OPT) / ANF ) }')
    speedupcps=$(awk -v CPS=${timecpso} -v OPT=${timecpsoinl} 'BEGIN { print ( (CPS - OPT) / CPS ) }')
    
    ESC='\\'
    # output latex table
    printf "{${ESC}tt ${f}} &  %.3f  &  %.3f  &  %.3f  &  %.3f  &  %.3f  &  %.3f  \n" "$timeanfo" "$timeanfoinl" "$speedupanf" "$timecpso" "$timecpsoinl" "$speedupcps"
done
