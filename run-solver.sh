#!/bin/sh

set -e -u
cd "$(dirname "$0")"

runlim="$(realpath tools/bin/runlim)"
runlim() {
    "$runlim" --time-limit=5000 --space-limit=24000 "$@"
}

solver_with_config="$1"
solver="${solver_with_config%@*}"
config="${solver_with_config#*@}"
instance="$2"

driver_directory=./solvers/"$solver"/bin/
status_in_competition="$(awk -F, "/^sat.$instance.cnf.bz2,$solver,$config/ {print \$5}" archives/main.csv)"
test -n "$status_in_competition" -a "$status_in_competition" != complete && {
  # echo Note: "$solver_with_config" failed to solve "$instance" in the \'18 competition, skipping
  exit 0
}
destination="$(realpath ./benchmarks/$instance/$solver_with_config)"
test -d "$destination" && {
  # echo Note: "$instance" already solved with "$solver_with_config"
  exit 0
}

staging="$(realpath staging)"
mkdir -p "$staging"
tmp="$staging/$instance.$solver_with_config"
rm -rf "$tmp"
mkdir "$tmp"
tools/bin/zstd -q -d "benchmarks/$instance/formula.cnf.zst" -o "$tmp/formula.cnf"
(cd "$driver_directory"
 executable="./starexec_run_$config"
 test -x "$executable" || {
   echo "Error: $executable" is not executable!
   exit 1
 }
 runlim --output-file="$tmp"/runlim.out \
  "$executable" \
  "$tmp/formula.cnf" \
  "$tmp" \
  > "$tmp"/stdout \
  2>"$tmp"/stderr \
  || : # echo "Error: runlim failed for $instance $solver"
  )
trap : INT TERM
rm "$tmp/formula.cnf"
# expGlucose@default prints ' UNSATISFIABLE'
grep -qE '^(s | UNSATISFIABLE)' "$tmp"/stdout && {
    test "$solver" = 'glucose4.2.1' -o "$solver" = 'expGlucose' \
        && tools/bin/fix-glucose-drat.pl "$tmp"/proof.out
    tools/bin/zstd -5 --quiet --rm "$tmp"/proof.out
} ||  {
    echo "solver failed to produce a solution: $solver_with_config on $instance"
    rm -f "$tmp"/proof.out
}
mkdir -p "$(dirname "$destination")"
mv "$tmp" "$destination"
