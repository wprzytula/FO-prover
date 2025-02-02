#!/bin/bash

TIMEOUT_AMOUNT=10s
TIMEOUT=$(if which timeout >& /dev/null; then echo "timeout"; else echo "gtimeout"; fi)
PROVER=FO-prover

correct=0
timeout=0
total_A=0
total_B=0
total_C=0
score=0

maxpoints=25

for test in ./tests/A/t*.txt; do
	[ -e "$test" ] || continue
	
	if [[ "$test" =~ ^./tests/A/t(.*).txt ]]
	then
		n="${BASH_REMATCH[1]}"
	else
		printf "no match\n"
	fi
	
	echo -n "Running test A $n..."

	# run the solver with a timeout
	result=$(cat "$test" | $TIMEOUT -sHUP $TIMEOUT_AMOUNT ./"$PROVER")

	if (( $? == 0 )) ; then

		if (( $result == "1" )) ; then
			# passing a positive test gains +1
			score=$((score + 1))
			echo "OK (+1)"
		elif (( $result == "0" )) ; then
			# failing a positive test gains -2
			score=$((score - 2))
			echo "FAIL (-2)"
		else 
			# abort on unexpected output
			echo "unexpected output"
			return -1
		fi

	else
		# timeout a positive test gains 0
		echo "TIMEOUT (0)"
	fi

	total_A=$((total_A+1))
done

for test in ./tests/B/t*.txt; do
	[ -e "$test" ] || continue
	
	if [[ "$test" =~ ^./tests/B/t(.*).txt ]]
	then
		n="${BASH_REMATCH[1]}"
	else
		printf "no match\n"
	fi
	
	echo -n "Running test B $n..."

	# run the solver with a timeout
	result=$(cat "$test" | $TIMEOUT -sHUP $TIMEOUT_AMOUNT ./"$PROVER")

	if (( $? == 0 )) ; then

		if (( $result == "1" )) ; then
			score=$((score - 2))
			echo "FAIL (-2)"
		elif (( $result == "0" )) ; then
			score=$((score + 2))
			echo "WOW (+2)"
		else 
			# abort on unexpected output
			echo "unexpected output"
			return -1
		fi

	else
		# timeout a test B gains 1
		score=$((score + 1))
		echo "TIMEOUT (OK +1)"
	fi

	total_B=$((total_B+1))
done

for test in ./tests/C/t*.txt; do
	[ -e "$test" ] || continue
	
	if [[ "$test" =~ ^./tests/C/t(.*).txt ]]
	then
		n="${BASH_REMATCH[1]}"
	else
		printf "no match\n"
	fi
	
	echo -n "Running test C $n..."

	# run the solver with a timeout
	result=$(cat "$test" | $TIMEOUT -sHUP $TIMEOUT_AMOUNT ./"$PROVER")

	if (( $? == 0 )) ; then

		if (( $result == "1" )) ; then
			score=$((score - 2))
			echo "FAIL (-1)"
		elif (( $result == "0" )) ; then
			score=$((score + 0))
			echo "OK (0)"
		else 
			# abort on unexpected output
			echo "unexpected output"
			return -1
		fi

	else
		score=$((score - 1))
		echo "TIMEOUT (-1)"
	fi

	total_C=$((total_C+1))
done

total=$((total_A + total_B + total_C))
echo "Score: $score in $total tests"
echo "$score" > "score.txt"

# calculation of the awarded points for the project
score=$(( score > 0 ? score : 0 ))
score=$(( score < 81 ? score : 81 ))
points=$(( (score * maxpoints) / 81 + 1 ))

echo "Points: $points"
echo "$points" > "points.txt"
