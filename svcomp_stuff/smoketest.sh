#!/bin/bash

./iekke_exe examples/lazy01.i --allow-pointer-unsoundness --graphml-witness error-witness.graphml  --unwind 2 --rounds 1 --verbosity 8 --minisat

./iekke_exe examples/queue.i --allow-pointer-unsoundness --graphml-witness error-witness.graphml  --unwind 2 --rounds 2 --verbosity 8 --minisat

./iekke_exe examples/singleton.i --allow-pointer-unsoundness --graphml-witness error-witness.graphml  --unwind 2 --rounds 3 --verbosity 8 --minisat

exit 0
