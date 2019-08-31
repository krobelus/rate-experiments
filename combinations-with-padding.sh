#!/bin/sh

set -e -u
cd "$(dirname "$0")"

./combinations.sh
./combinations.sh | sed 's/$/DISCARD/'
