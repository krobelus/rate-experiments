#!/bin/sh
#
# # run like this:
# for proof in benchmarks/*/*/proof.out.zst
# echo "$proof"
# do | parallel ./compress-proofs.sh

set -e -u

proof="$1"
echo "$proof"
pwd="$(dirname "$proof")"
uncompressed="$(echo "$proof"|sed 's/.zst$//')"
zstd -d "$proof" --force
if ! tools/bin/is-binary-drat.pl "$uncompressed"; then
	tools/bin/drat2cdrat < "$uncompressed" > "$uncompressed".tmp
	tools/bin/zstd -5 "$uncompressed".tmp -o "$proof" --force
fi
rm -f "$uncompressed"

