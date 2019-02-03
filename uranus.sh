#!/bin/sh

set -e

cd "$(dirname "$0")"

test -f results.json && mv results.json results.json.bak
ssh uranus 'cd rate-experiments && ./results.py' >  results.json
make p/plots t/tables
