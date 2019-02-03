#!/bin/sh

set -e -u

cd "$(dirname "$0")"

acl2="$(realpath acl2-devel/saved_acl2)"
cert="$(realpath acl2-devel/books/build/cert.pl)"

cd acl2-devel/books/projects/sat/lrat

"$cert" -j`nproc` --acl2 "$acl2" */*.lisp

cd stobj-based
"$acl2" << EOF
(include-book "run")
:q
(save-exec
  "lrat-check"
  "Large executable including run.lisp, saved with --dynamic-space-size 240000"
  :host-lisp-args "--dynamic-space-size 240000"
)
EOF
