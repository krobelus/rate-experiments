#!/bin/sh

set -e -u

src="$1"
dst="$2"

for x in benchmarks/*/*/"$src"
do
  echo mv "$x" `dirname "$x"`/"$dst"
  mv "$x" `dirname "$x"`/"$dst"
done
