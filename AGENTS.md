# AGENTS.md

## Project overview

HOLMS (HOL-Light Library for Modal Systems) is a library for formalized modal logic developed in the HOL Light theorem prover.

The project implements syntax and Kripke semantics for modal logic, axiomatic calculi, correspondence theory, soundness and completeness results, decision procedures, and certified countermodel construction for several normal modal logics.

For an overview of the project and its mathematics, see:

- `README.md`
- https://holms-lib.github.io/

## Environment

HOLMS is a HOL Light library. Source files are OCaml/HOL Light scripts (`.ml`).

The library assumes a working HOL Light installation.

The top-level HOLMS file is:

    make.ml

It loads the library components in dependency order.

Do not treat this repository as an ordinary standalone OCaml project: the source files are intended to be evaluated in the HOL Light environment.

## Repository structure

Important files include:

- `modal.ml` — syntax and Kripke semantics of modal logic.
- `calculus.ml` — axiomatic calculus.
- `parametric_correspondence.ml`, `ad_hoc_correspondence.ml` — correspondence theory.
- `gen_completeness.ml` — generic infrastructure for completeness proofs.
- `*_completeness.ml` — soundness/completeness developments for individual modal systems.
- `gen_decid.ml`, `gen_countermodel.ml` — generic decision and countermodel infrastructure.
- `*_decid.ml` — decision procedures for individual modal systems.
- `translations.ml` — translations between modal systems.
- `tests.ml`, `grz_tests.ml` — tests and examples.
- `make.ml` — top-level loader.

Consult `make.ml` before changing dependencies between files. Its load order reflects dependencies among the components of the library.

## Working with the code

Preserve the existing HOL Light programming and proof style unless there is a good reason to change it.

When proving a theorem:

1. Search the existing HOLMS code and HOL Light libraries for applicable definitions and theorems before introducing new machinery.
2. Prefer reusing existing general results over duplicating system-specific arguments.
3. Keep the distinction between HOL Light's OCaml meta-language and terms/theorems of HOL explicit.
4. A proof is complete only when it is accepted by HOL Light.

When modifying existing code:

- Make focused changes.
- Do not refactor unrelated code unless explicitly requested.
- Preserve theorem names and public definitions unless the task specifically requires changing them.
- Be particularly cautious when modifying foundational definitions or generic infrastructure, since many later files depend on them.
- Check `make.ml` when adding a new source file or changing dependencies.

## Verification

Whenever feasible, verify changes in HOL Light rather than relying only on static inspection.

The repository contains:

    ./runall.sh

which loads the library and its tests in the development environment for which the script is configured.

After a nontrivial change, run the relevant verification available in the current environment.

For local changes, prefer first testing the smallest relevant file or theorem when this avoids unnecessarily reloading the whole library. Run the broader test suite when appropriate before considering a substantial task complete.

Do not claim that a proof or change has been verified unless HOL Light has actually accepted it.

## Formalization principles

HOLMS is a formalized mathematics project. Correctness of the formal development takes priority over merely obtaining executable OCaml code.

Do not:

- introduce new axioms or unproved assumptions merely to make a proof succeed;
- bypass HOL Light's logical kernel;
- replace a theorem by an unchecked computation or assertion;
- silently weaken theorem statements or definitions in order to complete a task.

If a requested proof cannot be completed, report the obstruction rather than changing the mathematical statement without explicit approval.

## Changes and reporting

Before making substantial changes, inspect the relevant definitions, dependencies, and nearby proofs.

After making changes, summarize:

- what was changed;
- which files were modified;
- what verification was performed;
- any remaining uncertainty or unverified behavior.

Keep diffs small enough to review whenever possible.