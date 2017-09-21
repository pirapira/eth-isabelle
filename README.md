# Formalization of Ethereum Virtual Machine in Isabelle/HOL

The status is immature.  Currently [a Coq project](https://github.com/pirapira/evmverif) about EVM bytecode verification is being ported here.  The directory also contains

* a Keccak-256 implementation in Isabelle/HOL `KEC.thy`
* a RLP implementation (in progress) `RLP.thy`
* an EVM implementation `ContractSem.thy`
* a relational semantics that captures the callee's nondeterministic behavior `RelationalSem.thy`

When you see `\<Rightarrow>` in the source, try using the [Isabelle2016](https://isabelle.in.tum.de/index.html) interface.  There you see `⇒` instead.

## Checking Deed.thy

Use `Isabelle2016` (newer versions do not work), and open `Isabelle2016 example/Deed.thy`.

## Links

* For a bigger picture, see [overview of Yoichi's formal verification efforts on smart contracts](https://github.com/pirapira/ethereum-formal-verification-overview/blob/master/README.md#formal-verification-of-ethereum-contracts-yoichis-attempts)
* For updates, visit [a gitter channel](https://gitter.im/ethereum/formal-methods)
