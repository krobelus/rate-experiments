#!/bin/sh

set -e -u
cd "$(dirname "$0")"

make -C tools
(cd tools/rate && cargo build --release)
./prepare-benchmarks-and-solvers.sh

if test -n "${RATE_EXPERIMENTS_TEST_ONLY+x}"; then
  mv instances.txt instances.bak
  for instance in example1 example2
  do
    echo "$instance" >> instances.txt
    find benchmarks/"$instance"/ -mindepth 1 -maxdepth 1 -type d | xargs rm -rf
    for solver in CaDiCaL@DONTUNZIP-fixed Maple_CM_Dist@default
    do
      printf "%s/%s\n" "$instance" "$solver"
    done
  done | ./run-instance-solver-combinations.sh --verbose
  # make
  mv instances.bak instances.txt
  exit 0
fi

# run on readily solved instances first, then all other combinations
(
    ./combinations-instance-solver.sh | perl -aF/ -ne 'chomp $F[1]; print if -d "benchmarks/$F[0]/$F[1]"'
    ./combinations-instance-solver.sh | shuf
) | ./run-instance-solver-combinations.sh
