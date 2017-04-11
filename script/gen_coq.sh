#! /bin/bash

set -e

make lem-coq
rm -rf evm-coq
mkdir evm-coq
cp lem/*.v evm-coq
cp lem/Makefile evm-coq
cp lem/coqmakefile.in evm-coq
tar cjf evm-coq.tar.bz evm-coq/*.v evm-coq/Makefile evm-coq/coqmakefile.in
