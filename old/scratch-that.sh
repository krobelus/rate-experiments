#!/bin/sh

set -e -u
cd "$(dirname "$0")"

host=uranus

(cd ../rate && git push "$host" master --force-with-lease) ||:

cat << EOF | ssh "$host"
set -e -u
cd rate-experiments

tmux send-keys C-c
sleep .2

rm -rf staging benchmarks/*/*/{rate,rate-d}

tmux send-keys './run-all.sh' Enter
EOF
