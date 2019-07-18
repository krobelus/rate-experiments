#!/bin/sh

ls README.md poster/poster.tex plots.ipynb | entr pipenv run make README.pdf README.markdown poster
