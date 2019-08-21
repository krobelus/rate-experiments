#!/bin/sh

set -e -u

for proof in benchmarks/*/*/proof.out.zst
do
	echo "$proof"
	pwd="$(dirname "$proof")"
	uncompressed="$(echo "$proof"|sed 's/.zst$//')"
	zstd -d "$proof"
	if ! tools/bin/is-binary-drat.pl "$uncompressed"; then
		tools/bin/drat2cdrat < "$uncompressed" > "$uncompressed".tmp
		tools/bin/zstd -5 "$uncompressed".tmp -o "$proof" --force
	fi
	rm -f "$uncompressed"
done

