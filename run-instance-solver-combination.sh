#!/usr/bin/env bash

set -e -u
cd "$(dirname "$0")"

checkers="$1"
instance="${2%/*}"
solver_with_config="${2#*/}"


if [[ "$solver_with_config" =~ DISCARD ]]; then
	solver_with_config="${solver_with_config%DISCARD}"
	while true
	do
		DISCARD=1 ./run-checker.sh 'rate-dDISCARD' "$solver_with_config" "$instance"
	done
fi

./run-solver.sh "$solver_with_config" "$instance"
for checker in $checkers
do
  ./run-checker.sh "$checker" "$solver_with_config" "$instance"
done
