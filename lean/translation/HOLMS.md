# `HOLMS.lean`

Lean module: [`../HOLMS.lean`](../HOLMS.lean)

This note records decisions specific to the root module. Project-wide choices
are documented in [`../CONVENTIONS.md`](../CONVENTIONS.md).

## Role of the module

`HOLMS.lean` is the public aggregate import for the translated library. It has
no direct HOL Light counterpart: in the original development, `make.ml`
performs the analogous orchestration by loading scripts in dependency order.

The root module contains imports only. Definitions and proofs belong in the
smallest appropriate module under `HOLMS/`; importing the root must not create
a second API layer or introduce compatibility aliases.

## Import policy

A translated module is added here only after it builds independently and its
dependencies are explicit in its own source file. The order of the imports is
kept close to the mathematical dependency order, even though Lean resolves
the dependency graph from the imports themselves.

Only completed public modules are exposed. Planned translations are not
represented by empty files, placeholder imports, or declarations containing
`sorry`. As a result, this module describes the actually available Lean
library rather than the complete eventual scope of HOLMS.

OCaml session setup, parser installation, printers, and test execution from
`make.ml` do not belong here. Lake, Lean notation scopes, and the test/build
commands provide those services separately.
