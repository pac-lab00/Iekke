#!/bin/bash
# Runs the wrapper on the bundled examples; each run must end with a verdict line.
cd "$(dirname "$0")"
fail=0
for f in examples/*.i; do
  v=$(DEAGLE_BUDGET=60 ./iekke examples/unreach-call.prp "$f" --32 2>&1 | grep -v '^\s*$' | tail -1)
  echo "$f: $v"
  case "$v" in SUCCESSFUL|FAILED) ;; *) fail=1;; esac
done
exit $fail
