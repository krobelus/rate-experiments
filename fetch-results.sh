#!/bin/sh

set -e

instance="$1"
solver="$2"

mkdir -p benchmarks/"$instance"

test -d benchmarks/"$instance"/"$solver" || {
    scp -r uranus:rate-experiments/benchmarks/"$instance"/"$solver" benchmarks/"$instance"
}

cd benchmarks/"$instance"
zstd -d formula.cnf.zst
cd "$solver"
zstd -d proof.out.zst
