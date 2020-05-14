# TLA+ specification for Succinct Atomic Swap smart contract

This repository contains the [TLA+](https://lamport.azurewebsites.net/tla/tla.html)
specification of the smart contract for Succinct Atomic Swaps
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

Some interesting invariants that are enabled in SASwap.cfg:

- `NoConcurrentSecretKnowledge`:
  If Alice knows both secrets, then Bob doesn't, and vise versa

- `NoSingleParticipantTakesAll`:
  Neither participant can receive both A and B coins

- `AliceDoesNotKnowBobsSecretOnTimeout`:
  Contract can time out only when Alice never received Bob's secret

## Limitations

#### Only one miner in the model, so no reorgs

Reorgs are relevant only if we cannot say that
"one block in the model means 6 bitcoin blocks"
(or whatever reorg safety limit is acceptable)

#### Fees and mempool priorities are not modelled

Mempool priorities may be relevant because transaction being stuck
unconfirmed or expunged from mempool might mean that participant
misses deadline on important transaction confirmation, which leads
to ability of a counterparty to take all funds. But at the same time,
the task to confirm the transaction in time is the same in different
stages of the contract for different transactions. We can therefore
say that this is a concern of a lower level and can be modelled
separately.

#### There may be mistakes or omissions in the model

Reviews and corrections welcome! For extending the scope of the model,
a new project may be better option, though.

#### There are probably more safety invariants to add

Suggestions welcome!

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

Note that when running checking from the command line, you will
not be able to do the exploration of the state log in case some
invariant or temporal property is violated. TLA+ toolbox has
the functionality where you can evaluate TLA+ expressions in
the context of each state in the log, but there are currently
no tools to do this from the command line or with text UI.

## Authors and contributors

The contract specification was created by Dmitry Petukhov
based on the explanations and diagrams presented by Ruben Somsen
