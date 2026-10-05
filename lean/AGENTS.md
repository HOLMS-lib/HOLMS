# AGENTS.md

## Scope

These instructions apply to the Lean 4 port under this directory. The
repository-level `AGENTS.md` still applies where it does not conflict with the
Lean-specific guidance below.

## Project overview

This directory contains an ongoing translation of HOLMS (HOL-Light Library for
Modal Systems) from HOL Light to Lean 4. The original HOL Light development is
in the parent directory and is the mathematical reference for the port.

The goal is to reproduce the definitions, results, and formalized mathematics
of HOLMS using idiomatic Lean. The Lean development is incomplete and must not
be presented as a replacement for parts of the HOL Light library that have not
yet been translated and verified.

## Environment and structure

This is a Lake project:

- `lakefile.toml` defines the `HOLMS` library.
- `lean-toolchain` pins the Lean version.
- `HOLMS.lean` is the root library module.
- `HOLMS/*.lean` contains the implementation modules.
- `HOLMS/Modal.lean` corresponds to `../modal.ml` and contains syntax, Kripke
  semantics, subformulas, countability, and bisimulation.
- `CONVENTIONS.md` contains the authoritative translation choices that apply
  across multiple modules.
- `translation/README.md` indexes the implementation notes specific to each
  Lean module.
- `TRANSLATION.md` is a legacy snapshot. It is redundant, may be obsolete,
  and must not be treated as the current translation guide.

Run Lake commands from this directory. Do not treat the Lean port as part of
the HOL Light `make.ml` load sequence.

## Translation guidelines

Before translating a definition or theorem:

1. Read `CONVENTIONS.md` and the matching module note indexed by
   `translation/README.md`. For a new module, inspect the notes of its direct
   dependencies and create its own note as part of the translation.
2. Inspect the corresponding HOL Light source and its dependencies.
3. Search the existing Lean modules for reusable definitions and results.
4. Preserve the original mathematical meaning and public terminology where
   practical, while following established Lean naming and proof conventions.
5. Keep explicit which parts are faithful translations and which parts are
   Lean-specific implementation choices.

Prefer idiomatic Lean structures, inductive types, recursion, and theorem
statements over mechanical translations of HOL Light's OCaml proof scripts.
Avoid duplicating general results for individual modal systems when a reusable
abstraction is appropriate.

When adding a public module, import it from `HOLMS.lean`. Keep imports at the
beginning of each Lean file and avoid unnecessary dependencies. Consult the
corresponding HOL Light files before changing foundational syntax or semantic
definitions. Update the matching file under `translation/` when a
module-specific implementation decision changes; update `CONVENTIONS.md`
instead when the decision affects several modules.

## Formalization principles

Correctness of the formal development takes priority over making code compile.

Do not:

- use `sorry`, `admit`, or new axioms to bypass a proof;
- replace a theorem with unchecked computation;
- silently weaken a translated statement;
- claim equivalence with the HOL Light development without proving or clearly
  justifying the correspondence.

If a faithful translation cannot be completed, leave the existing statement
unchanged and report the obstruction.

## Style and changes

- Follow the style of nearby Lean code.
- Add concise docstrings to public definitions and theorems.
- Lean comments and docstrings must describe only the Lean definitions,
  statements, proofs, and usage, independently of their origin. Put source
  correspondences, translation history, naming compatibility, and comparisons
  with HOL Light in the matching `translation/*.md` document.
- Keep notation scoped when it could conflict with Lean or other libraries.
- Make focused changes and avoid unrelated refactoring.
- Preserve existing public names unless the task explicitly requires a change.
- Do not add external Lake dependencies unless they are necessary for the
  requested development.

## Verification

For a focused change, first build the relevant module, for example:

```sh
lake build HOLMS/Modal.lean
```

Before considering a broader change complete, build the full Lean library:

```sh
lake build
```

A proof is verified only when Lean accepts it without `sorry` or equivalent
placeholders. Report exactly which commands were run and any remaining
warnings or unverified behavior.
