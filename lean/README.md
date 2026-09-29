# HOLMS in Lean

This directory contains an ongoing translation of HOLMS (HOL-Light Library for
Modal Systems) from HOL Light to Lean 4.

The original HOL Light development is located in the repository root. The Lean
port follows its mathematical organization while using definitions, proofs,
and programming conventions appropriate for Lean. It is currently a work in
progress and should not yet be considered a complete replacement for the HOL
Light library.

## Structure

- `HOLMS.lean` is the root module of the Lean library.
- `HOLMS/Modal.lean` formalizes modal syntax, Kripke semantics, subformulas,
  countability, and bisimulation.
- `HOLMS/Calculus.lean` translates the Hilbert calculus for normal modal
  logics, including its derived propositional and modal rules, uniform
  substitution, and the deduction theorem.
- `HOLMS/ParametricCorrespondence.lean` defines characteristic and appropriate
  frame classes and proves the general semantic soundness theorem.
- `HOLMS/AdHocCorrespondence.lean` proves the standard frame-correspondence
  results for `D`, `T`, `4`, `B`, `5`, Löb, and Grzegorczyk.
- `TRANSLATION.md` documents the main representation and proof-engineering
  differences between the HOL Light sources and the Lean port.
- `lakefile.toml` defines the `HOLMS` Lake library.
- `lean-toolchain` pins the Lean version used by the project.

## Requirements

Install Lean through [Elan](https://github.com/leanprover/elan). Elan reads
`lean-toolchain` and selects or installs the required Lean version
automatically.

The project uses [Mathlib](https://github.com/leanprover-community/mathlib4)
for its set-theoretic and finite/countable infrastructure. Lake resolves the
pinned dependency recorded in `lake-manifest.json`.

## Building

Run the following commands from this directory:

```sh
lake update
lake exe cache get
lake build
```

The cache command is optional, but avoids compiling Mathlib locally.

To compile only the modal syntax module, run:

```sh
lake build HOLMS/Modal.lean
```

When using an editor with the Lean extension, open this `lean` directory as the
project root so that the Lake configuration and pinned toolchain are detected.
