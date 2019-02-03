#!/bin/sh

set -e -u
cd "$(dirname "$0")"

checkers="$1"
instance="${2%/*}"
solver_with_config="${2#*/}"

./run-solver.sh "$solver_with_config" "$instance"
for checker in $checkers
do
  ./run-checker.sh "$checker" "$solver_with_config" "$instance"
done
