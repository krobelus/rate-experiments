#!/bin/sh

cd "$(dirname "$0")"

solvers="$(cat solvers.txt)"

while read instance
do
  for solver in $solvers
  do
    printf "%s/%s\n" $instance $solver
  done
done < instances.txt
