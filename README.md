# TLA+ specification for Succinct Atomic Swap smart contract

This repository contains the [TLA+](https://lamport.azurewebsites.net/tla/tla.html)
specification of the smart contract for Succing Atomic Swaps
that can be implemented on the blockchain platform that uses UTXO model
such as Bitcoin on one side, and other blockchain platform that does not need
to be based on UTXO model or have transaction timelock properties
on the other side.

The contract was first described by Ruben Somsen in
[the post](https://lists.linuxfoundation.org/pipermail/bitcoin-dev/2020-May/017846.html)
 to bitcoin-dev mailing list

The specification can be found in `SASwap.tla`

Default values for constants can be found in `MC.tla`

`SASwap.pdf` is the spec rendered with `make pdf`

## What can be checked

Different safety invariants can be checked, by defining the
operators representing the invariants in the invariants section
of `SASwap.tla` and adding the corresponding `INVARIANT` line
into SASwap.cfg` (or in TLA+ toolbox model page)

The model can successfully detect the violation of
`NoConcurrentSecretKnowledge` invariant when 'stealthy' transaction
sending modelling is enabled with `STEALTHY_SEND_POSSIBLE = TRUE`
(this problem was pointed out by ZmnSCPxj in the [discussion](https://lists.linuxfoundation.org/pipermail/bitcoin-dev/2020-May/017861.html) in the original thread at bitcoin-dev)

## Limitations

At the moment, temporal properties checking does not work

Steps 5 and 6 from the [diagram](https://gist.githubusercontent.com/RubenSomsen/8853a66a64825716f51b409be528355f/raw/27b696dffbb1fc7bf6dea58b3767ed17b47ca6b4/SuccinctAtomicSwap.svg)
are not modelled

There may be mistakes or omissions in the model

There are certainly more safety invariants to add

## Working with TLA spec from command line

To run `TLC` on the spec via included Makefile instead of
TLA+ toolbox in unix-like environment, you need `tla2tools.jar`
from https://github.com/tlaplus/tlaplus/releases or your local
TLA+ toolbox installation.

Set environment variable `TLATOOLSDIR` to the path where
`tla2tools.jar` is located.

Make sure you have `java` in your `PATH`

run `make check` to apply `TLC` checker

run `make pdf` to generate PDF file for the TLA+ specification
(you need pdflatex to be in your `PATH` for that)

## Authors and contributors

The contract specification was created by Dmitry Petukhov
based on the explanations and diagrams presented by Ruben Somsen
