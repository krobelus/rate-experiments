#!/bin/sh
#
# # run like this:
# for proof in benchmarks/*/*/proof.out.zst
# echo "$proof"
# do |
# parallel ./compress-proofs.sh \
# --limit "df | sort -nk 2 | tail -n1 | perl -ae 'exit 1 if @F[3] < 70*(1<<20)'" \

set -e -u

zstd() {
	tools/bin/zstd "$@"
}

proof="$1"
echo "$proof"
pwd="$(dirname "$proof")"

zstd -dcf "$proof" | tools/bin/is-binary-drat.pl /dev/stdin || (
	zstd -dcf "$proof" --force | tools/bin/drat2cdrat | zstd - -o "$proof".new -5 --force
	mv "$proof".new "$proof"
)

