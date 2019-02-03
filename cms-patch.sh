#!/bin/sh

set -e -u
cd "$(dirname "$0")"

git stash

# TODO
# rm -rf benchmarks/*/cryptominisat@baseline
rm -rf benchmarks/*/cryptominisat@patched
rm -rf benchmarks/*/myMapleLCMDistChronoBT@default
for d in benchmarks/*/cryptominisat@patched benchmarks/*/myMapleLCMDistChronoBT@default
do
	test -d $d/rate || continue
	grep -q reason.deletions.shrinking.trail.\*[1-9] $d/rate/stdout || continue
	rm -rf $d
done

# TODO
(cd .. && sh ~/build-cms.sh)

make -C tools
(cd tools/rate && cargo build --release)
./prepare-benchmarks-and-solvers.sh

mv checkers.txt checkers.bak
echo rate > checkers.txt
shuf instances.txt | while read instance
do
	# TODO
	# for solver in cryptominisat@baseline cryptominisat@patched
	# for solver in cryptominisat@patched
	for solver in myMapleLCMDistChronoBT@default
	do
  		printf "%s/%s\n" "$instance" "$solver"
	done
done | ./run-instance-solver-combinations.sh --verbose

mv checkers.bak checkers.txt

# run on readily solved instances first, then all other combinations
# (
#     ./combinations-instance-solver.sh | perl -aF/ -ne 'chomp $F[1]; print if -d "benchmarks/$F[0]/$F[1]"'
#     ./combinations-instance-solver.sh | shuf
# ) | ./run-instance-solver-combinations.sh

