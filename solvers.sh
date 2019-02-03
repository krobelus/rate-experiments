#!/bin/sh

set -e -u

cd "$(dirname "$0")"

awk -F, '{ if (NR > 1) printf "%s@%s\n", $2, $3 }' archives/main.csv \
    | sort --unique \
    | grep -vFx 'inIDGlucose@default' `: does not compile?` \
    | grep -vFx 'YalSAT@default' `: takes a long time on trivial instances?` \


