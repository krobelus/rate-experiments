#!/bin/sh

qutebrowser file://"$(realpath index.html)"
while true
do
  find -maxdepth 1 -name '*.html' -o -name '*.png' | entr -d qutebrowser :reload
done
