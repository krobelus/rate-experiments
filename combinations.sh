#!/usr/bin/env bash

cd "$(dirname "$0")"

solvers="$(cat solvers.txt)"

while read instance
do
	for solver in $solvers
	do
		# only already solved instances
		test -f benchmarks/"$instance"/"$solver"/proof.out.zst && printf "%s/%s\n" $instance $solver||:
	done
done < instances.txt
