#!/bin/sh

set -e -u

cd "$(dirname "$0")"

awk -F, '{ if ($6 == "UNSAT") print $1 }' archives/main.csv \
        | sort --unique \
        | sed -e 's#^sat/##' -e 's#.cnf.bz2$##'
