#!/bin/sh
echo README.md | entr pipenv run make README.pdf
