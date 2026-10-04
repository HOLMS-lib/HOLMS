# `HOLMS.TCompleteness`

Lean module: [`../HOLMS/TCompleteness.lean`](../HOLMS/TCompleteness.lean)

HOL Light source: [`../../t_completeness.ml`](../../t_completeness.ml)

This note records decisions specific to modal logic T. General conventions and
the shared design of completeness-based tactics are in
[`../CONVENTIONS.md`](../CONVENTIONS.md).

## Axiom and frame classes

The additional axiom set is `T_AX := Set.range T_SCHEMA`. This directly
represents all substitution instances of the T schema and makes schema
membership a witness in the range.

`REFL` is the class of well-formed reflexive frames, while `RF` is its finite
subclass. Their correspondence and appropriateness results reuse
`MODAL_REFL` and the parametric soundness infrastructure instead of repeating
the semantic proof of the T axiom.

As for K, syntactic consistency is established semantically on a one-world
`Unit` model. Here the accessibility relation is universal on that world so
that the frame is reflexive.

## Canonical specialization

The T standard frame, model, valuation, truth lemma, and relation specialize
the generic construction at `T_AX`. The underlying canonical relation remains
the generic K relation; T's extra proof obligation is to show that it is
reflexive on canonical worlds.

If `□B` belongs to a maximal T-consistent world, the T axiom derives `B` from
it. The closure theorem for maximal set-consistent worlds then turns this
derivability statement into membership of `B` in the same world. This direct
set argument replaces the source proof through a singleton list and
`CONJLIST`.

Once reflexivity is established, generic accessibility and countermodel
results provide the remaining finite countermodel and completeness theorems.
`T_COUNTERMODEL_FINITE_SETS` is again a direct set-world corollary rather than
the endpoint of a second representation change.

## Automation

`modal_t` is the single Lean counterpart of `T_TAC` and `T_RULE`. Its pipeline
matches `modal_k`, but its explicit simplification list also unfolds membership
in `RF` and the `REFLEXIVE` condition, giving `grind` access to the required
self-loop.

The five active `T_RULE` examples from the source are retained as local Lean
`example` declarations and compile with the module. The commented attempts at
axiom 4 and Löb formulas are not proof obligations for T and are not turned
into declarations. As with `modal_k`, the tactic produces checked proof terms
but is not a replacement for the later certified decision procedures.
