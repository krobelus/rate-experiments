#!/bin/sh

set -e -u

cd "$(dirname "$0")"

url="http://sat2018.forsyte.tuwien.ac.at/"

mkdir -p archives/solvers

zstd="$(realpath tools/bin/zstd)"
parallel="$(realpath tools/bin/parallel)"
recompress_and_symlink_benchmark="$(realpath ./recompress-and-symlink-benchmark.sh)"
prepare_solver="$(realpath ./prepare-solver.sh)"

mkdir -p benchmarks
(cd archives
 zip="Main.zip"
 test -f "$zip" || curl "$url/benchmarks/Main.zip" -o "$zip"
 test -d Main || unzip "$zip" -d Main
 (cd Main && find * -name '*.bz2' | "$parallel" "$recompress_and_symlink_benchmark")
 for track in main nolimit parallel18 random
 do
     test -f "$track.csv" || curl "$url/results/$track.csv" | tr '\r' '\n' > "$track".csv
 done
)

mkdir -p solvers
cd solvers
awk -F@ '/^[^#]/ {print $1}' ../solvers.txt | "$parallel" "$prepare_solver"
