# Formalization of Ethereum Virtual Machine in Lem

[![Build Status](https://travis-ci.org/pirapira/eth-isabelle.svg?branch=master)](https://travis-ci.org/pirapira/eth-isabelle)
[![CircleCI](https://circleci.com/gh/pirapira/eth-isabelle/tree/master.svg?style=svg)](https://circleci.com/gh/pirapira/eth-isabelle/tree/master)

This repository contains

* an EVM implementation in Lem `lem/evm.lem`
* a Keccak-256 implementation in Lem `lem/keccak.lem`
* a form of functional correctness defined in Lem `lem/evmNonExec.lem`
* a relational semantics that captures the environment's nondeterministic behavior `RelationalSem.thy`
* some example verified contracts in `example`
* a parser that parses hex code and emits an Isabelle/HOL expression representing the program `parser/hexparser.rb`

When you see `\<Rightarrow>` in the source, try using the [Isabelle2017](https://isabelle.in.tum.de/index.html) interface.  There you see `⇒` instead.

## Lem?

[Lem](https://www.cl.cam.ac.uk/~pes20/lem/) is a language that can be translated into [Coq](https://coq.inria.fr/), [Isabelle/HOL](https://isabelle.in.tum.de/), [HOL4](https://hol-theorem-prover.org/), [OCaml](http://www.ocaml.org/), HTML and [LaTeX](https://www.latex-project.org/).

## Prerequisites

* [Isabelle2017](https://isabelle.in.tum.de/installation.html)
* [lem](http://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-manual.html#installation)
* [OCaml](http://www.ocaml.org/) 4.02.3
* [opam](https://opam.ocaml.org/) 1.2.2
* Some opam packages: use `opam install ocamlfind batteries yojson bignum easy-format bisect_ppx ocamlbuild sha`
* [ECC-OCaml from mrsmkl](https://github.com/mrsmkl/ECC-OCaml)

## How to read the proofs

First translate the Lem definitions into Isabelle/HOL:
```
$ make lem-thy
```

Then, use Isabelle2017 to open `./examples/AlwaysFail.thy`.  The prerequisite Isabelle/HOL files are automatically opened.

## How to run VM tests and state tests

Make sure the tests submodule is cloned
```
$ git submodule init tests
$ git submodule update tests
```

Extract the OCaml definitions
```
$ make lem-ocaml
```

And move to `tester` directory.
```
$ cd tester
```

One way is to run the VM Test.
```
$ sh compile.sh
$ ./runVmTest.native
```
(When `./runVmTest.native` takes an argument, it executes only the test cases whose names contain the argument as a substring.)


Another way is to run the VM Test and measure the coverage.
```
$ sh measure_coverage.sh
```

Moreover, it's possible to run the state tests:
```
for j in `ls ../../tests/StateTests/*.json`
do
./stateTestReturnStatus.native $j || break
done
```

## Makefile goals

* `make doc` produces `output/document.pdf` as well as `lem/*.pdf`.
* `make lem-thy` compiles the Lem sources into Isabelle/HOL
* `make lem-hol` compiles the Lem sources into HOL4
* `make lem-coq; cd lem; make` compiles the Lem sources into Coq (and then compiles the Coq sources)
* `make lem-pdf` compiles some of the Lem sources into PDF through LaTeX
* `make all-isabelle` checks all Isabelle/HOL sources (but not the ones compiled from Lem)
* `make` does everything above
* `script/gen_coq.sh` generates a distribution useful for Coq users

## Links

* For a bigger picture, see [overview of Yoichi's formal verification efforts on smart contracts](https://github.com/pirapira/ethereum-formal-verification-overview/blob/master/README.md#formal-verification-of-ethereum-contracts-yoichis-attempts)
* For updates, visit [a gitter channel](https://gitter.im/ethereum/formal-methods)
* A related project [EVM formalization in K framework](https://github.com/kframework/evm-semantics)
