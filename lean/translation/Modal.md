# `HOLMS.Modal`

Lean module: [`../HOLMS/Modal.lean`](../HOLMS/Modal.lean)

HOL Light source: [`../../modal.ml`](../../modal.ml)

This note records implementation decisions specific to modal syntax and
Kripke semantics. The mathematical presentation is in
[`../../docs/Modal.md`](../../docs/Modal.md), while project-wide translation
choices are in [`../CONVENTIONS.md`](../CONVENTIONS.md).

## Formula syntax

The HOL datatype `form` becomes the inductive type `Form`. Lean derives
equality, representation, hashing, and countability infrastructure from this
datatype instead of reproducing the corresponding HOL Light constructions.
Derived connectives such as `diam` and `dotbox` are ordinary definitions, not
additional constructors, so structural recursion and induction continue to
follow the primitive formula grammar.

The destructors used later in the library are partial Lean functions returning
`Option Form` (`unneg?` and `unbox?`). This makes failure explicit and avoids
encoding it with a distinguished formula.

## Immediate parts and subformulas

`Minor` and `Subformula` are inductive propositions. `Subformula` directly
expresses reflexivity and closure under immediate constituents, and the module
derives the transitivity and constructor-specific inversion lemmas needed by
later proofs. This replaces the HOL Light presentation through generated
induction artifacts without changing the relation.

The computable enumeration of subformulas is a `Finset Form`. The theorem
identifying membership in that finset with the logical `Subformula` relation
connects computation with reasoning. `subformula_list` is retained only as a
compatibility enumeration where a list is useful; it is not the canonical
representation of a set of formulas.

## Frames, models, and semantics

HOL Light pairs and triples are replaced by the structures `Frame W` and
`Model W`, with named fields for designated worlds, accessibility, and
valuation. The accessibility relation remains a predicate on the ambient type;
well-formed frame classes later state explicitly that relevant edges stay
inside the designated set.

Truth is the recursive function `Form.holds`. Frame validity (`holdsIn`) and
class validity (`Valid`) are propositions quantified over valuations and
designated worlds. No executable model checker is introduced at this layer.

The modal concrete syntax is defined here as the scoped notation
`HOLMS.ModalNotation`. Parser and printer extensions from the OCaml source are
therefore replaced by Lean notation declarations rather than runtime setup.

## Bisimulation

Pointed bisimulation is represented by the structure `BisimulationAt`, whose
fields expose atomic agreement and the forth/back conditions. Global
`Bisimulation` and `Bisimilar` are built from it. Truth invariance is proved by
formula induction and then lifted to frame and class validity.

This explicit structure is used later by generic completeness to transport a
finite canonical model to another world type. It avoids tuple projections and
makes the proof obligations of a transport visible as named fields.

## Source material not reproduced

OCaml quotation syntax, parser installation, pretty-printers, and session-level
commands are tooling for HOL Light rather than modal mathematics, so they have
no declarations in this module. Lean's generated recursors and instances are
also used directly instead of introducing constants that merely imitate
generated HOL Light theorems.
