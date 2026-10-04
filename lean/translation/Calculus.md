# `HOLMS.Calculus`

Lean module: [`../HOLMS/Calculus.lean`](../HOLMS/Calculus.lean)

HOL Light source: [`../../calculus.ml`](../../calculus.ml)

This note concerns the implementation of the Hilbert calculus. See
[`../../docs/Calculus.md`](../../docs/Calculus.md) for the mathematical account
and [`../CONVENTIONS.md`](../CONVENTIONS.md) for shared conventions.

## Primitive proof system

`KAxiom` and `ModProves` are inductive propositions. Their constructors are the
axiom and inference rules, while Lean supplies their recursors and induction
principles. Separate translations of generated HOL Light values such as
`KAXIOM_RULES` and `MODPROVES_INDUCT_STRONG` are therefore unnecessary.

Both the additional axiom system and the hypothesis context are `Set Form`.
The necessitation constructor deliberately preserves the source restriction:
its premise must be derivable with no hypotheses, although its conclusion can
be used in an arbitrary hypothesis context. Several later modal arguments
depend on this exact formulation.

## Derived proof rules

The large derived-rule library is proved theorem by theorem over `ModProves`.
HOL Light conjunctions used only to package meta-level premises generally
become curried Lean arguments. This changes how a theorem is applied but not
the formula proved by the calculus.

Weakening is expressed by set inclusion. The deduction theorem is established
early in the module and used as a central proof interface for later derived
rules, rather than reconstructing changes of hypotheses with list operations.
Public HOLMS names are retained where practical, including historical spelling
variants that may be used downstream.

No tactic-level theorem producer corresponding to OCaml proof combinators is
introduced here. The results are ordinary Lean theorems whose proof terms are
checked by the kernel; system-specific automation belongs to the relevant
completeness module.

## Uniform substitution

Uniform substitution is the recursive function `Form.subst`. The uppercase
name `SUBST` is kept as a compatibility abbreviation, while new Lean code can
use the namespaced definition.

Closure of derivability under substitution explicitly assumes that the
additional axiom set is closed under the substitution in question. Primitive K
axioms are proved substitution-invariant separately. This exposes a condition
that is logically essential for arbitrary extra axiom systems rather than
hiding it in metaprogramming.

## Source material not reproduced

Generated rule and induction theorems are replaced by Lean constructors and
recursors. OCaml tactics and quotation-based rule wrappers are not part of the
logical calculus and are not copied into this module. List-specific context
machinery is also absent because derivability is set-based throughout the Lean
port.
