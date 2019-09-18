#!/bin/sh

checker=DEBUGrate-d

rm -rf benchmarks/*/*/DEBUG*
./combinations-instance-solver.sh \
    | perl -ane 'print if -d "benchmarks/$F[0]/$F[1]"'
    | while read arg; do ./task.sh $checker "$arg"; done
