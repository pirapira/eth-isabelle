# Formalization of Ethereum Virtual Machine in Isabelle/HOL

This repository contains

* a Keccak-256 implementation in Isabelle/HOL `KEC.thy`
* a RLP implementation (in progress) `RLP.thy`
* an EVM implementation `ContractSem.thy`
* a relational semantics that captures the callee's nondeterministic behavior `RelationalSem.thy`
* some example verified contracts in `example`

When you see `\<Rightarrow>` in the source, try using the [Isabelle2016](https://isabelle.in.tum.de/index.html) interface.  There you see `⇒` instead.

## Prerequisites

* [Isabelle 2016](https://isabelle.in.tum.de/installation.html)
* [lem](http://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-manual.html#installation)

## Makefile goals

* `make deed` produces a verified PDF document for the Deed contract
* `make lem-thy` compiles the Lem sources into Isabelle/HOL
* `make all-isabelle` checks all Isabelle/HOL sources (but not the ones compiled from Lem)
* `make` does everything above

## Links

* For a bigger picture, see [overview of Yoichi's formal verification efforts on smart contracts](https://github.com/pirapira/ethereum-formal-verification-overview/blob/master/README.md#formal-verification-of-ethereum-contracts-yoichis-attempts)
* For updates, visit [a gitter channel](https://gitter.im/ethereum/formal-methods)
