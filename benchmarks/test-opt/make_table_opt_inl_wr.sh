#!/bin/zsh

FILES=`cat TESTS`

echo "Running each test ${1} times"

N=$1

# First run ocaml scripts

# Compare inlining all known calls vs. inline defensively (to not increase closure environments)

echo "Running CertiCoq programs..."
printf "      & ANF OPT & ANF OPT DEF & SPEEDUP & CPS OPT & CPS OPT DEF & SPEEDUP \n"

for f in $FILES
do
    # Find ANF OPT time    
    timeanfo=$(./${f}_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find CPS OPT time
    timecpso=$(./${f}_cps_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find ANF OPT time    
    timeanfodef=$(./${f}_opt1 ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find CPS OPT time
    timecpsodef=$(./${f}_cps_opt1 ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')

    #Find anf/ocamlopt ratio
    speedupanf=$(awk -v ANF=${timeanfo} -v OPT=${timeanfodef} 'BEGIN { print  ( (ANF - OPT) / ANF ) }')
    speedupcps=$(awk -v CPS=${timecpso} -v OPT=${timecpsodef} 'BEGIN { print ( (CPS - OPT) / CPS ) }')
    
    ESC='\\'
    # output latex table
    printf "{${ESC}tt ${f}} &  %.3f  &  %.3f  &  %.3f  &  %.3f  &  %.3f  &  %.3f  \n" "$timeanfo" "$timeanfodef" "$speedupanf" "$timecpso" "$timecpsodef" "$speedupcps"
done
