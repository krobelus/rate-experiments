#!/bin/sh

set -e -u

cd "$(dirname "$0")"

runlim() {
  tools/bin/runlim --time-limit=20000 --space-limit=24000 "$@"
}

checker="$1"
solver_with_config="$2"
instance="$3"

s="$(realpath ./benchmarks/$instance/$solver_with_config)"
destination="$s/$checker"

test -d "$destination" && {
  # echo Skipping: "$instance.$solver_with_config" already checked with "$checker"
  exit 0
}

test -f "$s"/proof.out.zst || {
  # echo "Skipping: proof not found: '$s/proof.out.zst'"
  exit 0
}
if [ "$checker" != rate ]; then
  # echo Skipping: proof not verified by rate
  test -d "$s/rate"    && grep '^s NOT VERIFIED$' "$s/rate/stdout"    && exit 0 ||:
  test -d "$s/rateOLD" && grep '^s NOT VERIFIED$' "$s/rateOLD/stdout" && exit 0 ||:
fi

staging="$(realpath staging)"
mkdir -p "$staging"
tmp="$staging/$instance.$solver_with_config.$checker"
rm -rf "$tmp"
mkdir "$tmp"
tools/bin/zstd --quiet -d "benchmarks/$instance/formula.cnf.zst" -o "$tmp/formula.cnf"
tools/bin/zstd --quiet --decompress "$s"/proof.out.zst -o "$tmp/proof.drat"
params=
if [ "$checker" = gratgen ]; then
  params="$params --no-progress-bar"
  # if tools/bin/is-binary-drat.pl "$tmp/proof.drat"; then
    params="$params --binary-drat"
  # fi
else
  params="-L $tmp/proof.lrat -C"
  if [ "$checker" = rate ]; then
    params="$params -i $tmp/witness.sick"
  fi
fi
checker="$(echo "$checker" | sed 's/[A-Z]//g')"
checker="$(echo "$checker" | sed 's/^rate-/rate -/')"
runlim --output-file="$tmp/runlim.out" \
  tools/bin/$checker "$tmp/formula.cnf" "$tmp/proof.drat" \
  $params \
  > "$tmp"/stdout \
  2>"$tmp"/stderr \
  || : # "out of memory" and "out of time" are fine
# segfaults are not
test "$(awk '/^.runlim. status:/ {printf $3}' "$tmp"/runlim.out)" = 'signal(6)' && exit 1
# awk '/^.runlim..time:/ {printf "drat check: %.2f seconds\n", $3}' "$tmp"/runlim.out
# TODO we should run gratchk
if [ "$checker" != gratgen ]; then
  if [ -s "$tmp"/stderr ]; then
    echo error not empty: "$tmp"/stderr
    cat "$tmp"/stderr
  fi
  if grep -Eq 's (VERIFIED|ACCEPTED)$' "$tmp"/stdout; then
    test -f "$tmp/proof.lrat" && {
        runlim --output-file="$tmp/lrat-check.runlim.out" tools/bin/lrat-check \
          "$tmp/formula.cnf" "$tmp/proof.lrat" nil t \
    	| tee "$tmp"/lrat-check.out \
    	| grep -q '^s VERIFIED' || echo "lrat-check failed for $tmp"
	(
		printf 'DRAT size: '
		wc -c < "$tmp/proof.drat"
		printf 'LRAT size: '
		tools/bin/to-clrat "$tmp"/proof.lrat /dev/stdout | wc -c
	) >> "$tmp"/lrat-check.out
    }
    # awk '/^.runlim..time:/ {printf "lrat check: %.2f seconds\n", $3}' "$tmp"/lrat-check.runlim.out
    :
  else
    test -f "$tmp/witness.sick" && {
        runlim --output-file="$tmp/sick-check.runlim.out" tools/bin/sick-check \
          "$tmp/formula.cnf" "$tmp/proof.drat" "$tmp/witness.sick" \
    	| tee "$tmp"/sick-check.out \
	| grep -q '^s ACCEPTED' || echo "sick-check failed for $tmp"
    }
  fi
fi
trap : INT TERM
rm "$tmp/formula.cnf"
rm "$tmp/proof.drat"
rm -f "$tmp/proof.lrat"
if [ "${DISCARD:-}" = 1 ]; then
	rm -rf "$tmp"
else
	mkdir -p "$(dirname "$destination")"
	mv "$tmp" "$destination"
fi
