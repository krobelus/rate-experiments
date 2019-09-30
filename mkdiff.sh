#!/bin/sh

set -eu

old="$1"
new="$2"

for file in "$old" "$new"; do
	pandoc --filter pandoc-fignos --filter pandoc-citeproc --filter pandoc-placetable --standalone "$file" -o "$file".tex
done

latexdiff "$old".tex "$new".tex > diff.tex
xelatex diff.tex
