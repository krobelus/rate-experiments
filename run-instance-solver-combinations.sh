#!/bin/sh

set -e -u
cd "$(dirname "$0")"

checkers="$(grep -v old checkers.txt)"

# Each job is granted 24 GB of memory, just like in the SAT competiton.
# Machine uranus has 240 GB and 32 cores, so we want to run 32 jobs at a
# time. This would require 768 GB of memory in the worst case. However
# the jobs usually need far less than 24 GB. We can overcommit memory
# with GNU parallel's --memfree option.
freemem="$(free --gibi | awk 'NR == 2 {print ($2 / 5)}')"

# Additionally we use --limit to avoid starting jobs when there are less
# than 70 GB available on the largest disk.

exec tools/bin/parallel --memfree "$freemem"G \
  --limit "df | sort -nk 2 | tail -n1 | perl -ae 'exit 1 if @F[3] < 70*(1<<20)'" \
  --progress --eta "$@" \
  "./run-instance-solver-combination.sh '$checkers'"
