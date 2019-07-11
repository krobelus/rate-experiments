#!/bin/sh

ls README.md poster/INF_Poster.tex plots.ipynb | entr pipenv run make README.pdf README.markdown poster
