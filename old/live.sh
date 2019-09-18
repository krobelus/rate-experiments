#!/bin/sh

pipenv run sh -c 'fd | entr make thesis.pdf thesis.markdown thesis.tex poster/poster.pdf'
