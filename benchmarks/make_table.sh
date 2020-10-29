#!/bin/zsh

FILES=`cat TESTS`

echo "Running each test ${1} times"

N=$1

# First run ocaml scripts

echo "Running ocamlc programs..."
./ocaml/main $N > ocamlc_bench.txt
echo "Running ocamlopt program..."
./ocaml/mainopt $N > ocamlopt_bench.txt

echo "Running CertiCoq programs..."
printf "      &   ANF   &    CPS    &  ocamlc  & ocamlopt %s \n" "\\\\"
for f in $FILES
do
    # Find ANF time    
    timeanf=$(./${f} ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find CPS time
    timecps=$(./${f}_cps ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find OCamlc time (assumes ocaml programs run for N times)
    timeocamlc=`awk -v N=${N} -v pat="${f}" '$0 ~ pat {print ($4 / N) }' ocamlc_bench.txt`
    # Find OCamlopt time
    timeocamlopt=`awk -v N=${N} -v pat="${f}" '$0 ~ pat {print ($4 / N)}' ocamlopt_bench.txt`

    if [ "${f}" = "color" ]; then
	printf "{${ESC}tt ${f}} &  %.3f  &  %.3f  &   -   &   -   &   -   \n" "$timeanf" "$timecps"
    else
	#Find anf/ocamlopt ratio
	ratio=`awk -v ANF=${timeanf} -v OPT=${timeocamlopt} 'BEGIN { print  ( ANF / OPT ) }'`

	ESC='\\'
	# output latex table
	printf "{${ESC}tt ${f}} &  %.3f  &  %.3f  &  %.3f  &  %.3f  &  %.3f  %s \n" "$timeanf" "$timecps" "$timeocamlopt" "$timeocamlc" "$ratio" "\\\\"
    fi
done
