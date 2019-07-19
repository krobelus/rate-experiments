#!/bin/sh

pipenv run sh -c 'fd | entr make README.pdf README.markdown README.tex poster/poster.pdf'
