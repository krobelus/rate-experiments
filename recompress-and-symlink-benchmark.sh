#!/bin/sh

set -e -u

bzpath="$1"
path="$(dirname "$bzpath")"/"$(basename "$bzpath" .bz2)".zst
bzcat "$bzpath" | tools/bin/zstd -o "$path"
rm "$bzpath"
destination=../../benchmarks/"$(basename "$path" .cnf.zst)"
mkdir -p "$destination"
ln -sf ../../archives/Main/"$path" $destination/formula.cnf.zst
