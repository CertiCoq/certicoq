#!/bin/sh

FILES=`cat TESTS`

echo "Running each test ${1} times"

N=$1

# First run ocaml scripts

echo "Running ocamlc programs..."
./ocaml/main $N > ocamlc_bench.txt
echo "Running ocamlopt program..."
./ocaml/mainopt $N > ocamlopt_bench.txt

echo "Running CertiCoq programs..."
printf "%10s %10s %10s %10s %10s %10s %10s %10s %10s %10s %10s \n" "Benchmark" "CertiCoq" "Ratio" "CertiCoqO" "Ratio" "CertiCoqL" "Ratio" "ocamlc" "Ratio" "ocamlopt" "Ratio"

for f in $FILES
do
    # Find ANF time    
    timeanf=$(./${f} ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find OPT time
    timeopt=$(./${f}_opt ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find OPT time with non-selective lambda lifting
    timeoptll=$(./${f}_opt_ll ${N} | awk -v N=${N} '/Time taken/ {print ($5 / N) }')
    # Find OCamlc time (assumes ocaml programs run for N times)
    timeocamlc=`awk -v N=${N} -v pat="${f}" '$0 ~ pat {print ($4 / N) }' ocamlc_bench.txt`
    # Find OCamlopt time
    timeocamlopt=`awk -v N=${N} -v pat="${f}" '$0 ~ pat {print ($4 / N)}' ocamlopt_bench.txt`

    #Find ratios
    ratioanf=`awk -v ANF=${timeanf} -v OPT=${timeanf} 'BEGIN { print  ( OPT / ANF ) }'`
    ratioopt=`awk -v ANF=${timeanf} -v OPT=${timeopt} 'BEGIN { print  ( OPT / ANF ) }'`
    ratiooptll=`awk -v ANF=${timeanf} -v OPT=${timeoptll} 'BEGIN { print  ( OPT / ANF ) }'`
    ratioocamlc=`awk -v ANF=${timeanf} -v OPT=${timeocamlc} 'BEGIN { print  ( OPT / ANF ) }'`
    ratioocamlopt=`awk -v ANF=${timeanf} -v OPT=${timeocamlopt} 'BEGIN { print  ( OPT / ANF ) }'`



    
    if [ "${f}" = "color" ]; then # Because ocaml code does not compile
	printf "%10s   %.3f      %.3f      %.3f      %.3f      %.3f      %.3f        -         -         -         - \n" "${f}" "$timeanf" "$ratioanf" "$timeopt" "$ratioopt" "$timeoptll" "$ratiooptll" 
    else

	printf "%10s   %.3f      %.3f      %.3f      %.3f      %.3f      %.3f      %.3f      %.3f      %.3f      %.3f \n" "${f}" "$timeanf" "$ratioanf" "$timeopt" "$ratioopt" "$timeoptll" "$ratiooptll"  "$timeocamlc" "$ratioocamlc" "$timeocamlopt" "$ratioocamlopt"

    fi
done
