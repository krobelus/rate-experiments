#!/bin/sh

(ls README.md plots.ipynb | entr pipenv run make README.pdf)&
p=$!
(echo poster/INF_Poster.tex | entr make poster)&
p="$p $!"
trap "kill $p" INT QUIT TERM EXIT
wait $p
