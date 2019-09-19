#!/bin/sh

set -eu

ignored='thesis.pdf poster/poster.pdf thesis.tex t p'

git commit -am "${1:-update}"||:
git filter-branch -f --prune-empty --index-filter "git rm -r --cached --ignore-unmatch $ignored" HEAD
git for-each-ref --format="%(refname)" refs/original/ | xargs -n 1 git update-ref -d
git reflog expire --expire=now --all
git gc --prune=now
pipenv run make
git add --force $ignored
git commit -m "generate $ignored"
