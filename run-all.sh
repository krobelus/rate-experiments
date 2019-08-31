#!/bin/sh

set -e -u
cd "$(dirname "$0")"

make -C tools
(cd tools/rate && cargo build --release)
./prepare-benchmarks-and-solvers.sh

if [ -n "${1:+x}" ]; then
	# run everything with rate first because we only care about verified benchmarks
	./combinations-with-padding.sh |
	CHECKERS='rate' ./run-instance-solver-combinations.sh
	exit 0
fi

./combinations-with-padding.sh |
CHECKERS='rate-d drat-trim gratgen' ./run-instance-solver-combinations.sh


# 1/3 is verified by rate (200/ 600) using about 50GB
# total number of benchmarks: 2000 (*3), will use 150GB

# interesting instances
#     cat <<EOF
# Nb51T6/smallsat@default
# cms-scheel-md5-families-r24-c5-p6-11-15-16-19/Minisat-v2.2.0-106-ge2dd095@simp_proof
# Problem14_label19_true-unreach-call.c/Sparrow2Riss-2018-fixfix@MAIN
# T129.2.0/Riss7.1-fix@BVE_DRAT
# EOF

# if test -n "${RATE_EXPERIMENTS_TEST_ONLY+x}"; then
#   mv instances.txt instances.bak
#   for instance in example1 example2
#   do
#     echo "$instance" >> instances.txt
#     find benchmarks/"$instance"/ -mindepth 1 -maxdepth 1 -type d | xargs rm -rf
#     for solver in CaDiCaL@DONTUNZIP-fixed Maple_CM_Dist@default
#     do
#       printf "%s/%s\n" "$instance" "$solver"
#     done
#   done | ./run-instance-solver-combinations.sh --verbose
#   # make
#   mv instances.bak instances.txt
#   exit 0
# fi
