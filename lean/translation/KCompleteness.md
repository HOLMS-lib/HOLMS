# `HOLMS.KCompleteness`

Lean module: [`../HOLMS/KCompleteness.lean`](../HOLMS/KCompleteness.lean)

HOL Light source: [`../../k_completeness.ml`](../../k_completeness.ml)

This note records decisions specific to the specialization for modal logic K.
General conventions and the common tactic design are in
[`../CONVENTIONS.md`](../CONVENTIONS.md).

## Axiom and frame classes

K has no additional axioms, so its axiom set is represented directly by the
empty `Set Form`; no otherwise empty `K_AX` definition is introduced.
`FRAME_CHAR_K` identifies arbitrary well-formed frames with the characteristic
class of that empty axiom set, and `FINITE_FRAME_APPR_K` supplies the finite
appropriate-frame characterization.

Consistency is proved semantically with a one-world `Unit` frame whose
accessibility relation is empty. This witnesses a finite K-frame in which
modal falsity is not valid and avoids a separate syntactic consistency
argument.

## Canonical specialization

`K_STANDARD_FRAME`, `K_STANDARD_MODEL`, and `K_STANDARD_REL` are deliberately
thin specializations of the generic definitions at the empty axiom set. The
K canonical relation needs no strengthening, so the generic accessibility
lemma applies directly.

The named K truth, maximal-consistency, accessibility, countermodel, and
completeness theorems are retained even when their proofs are short
applications of generic results. They form the public system-specific API and
make comparison with `k_completeness.ml` straightforward.

Because the generic canonical model already has worlds of type `Set Form`,
`K_COUNTERMODEL_FINITE_SETS` is a direct corollary. The source's final
list-to-set bisimulation, `K_STDWORLDS`, and `K_STDREL` infrastructure is not
recreated.

## Automation

The single Lean tactic `modal_k` replaces the OCaml pair `K_TAC` and `K_RULE`.
It applies finite-frame completeness, unfolds only K's semantic and finite
frame definitions, and lets `grind` solve the resulting first-order goal.
There is no separate rule-producing wrapper because Lean tactics already
construct kernel-checked proof terms in the current declaration context.

The three active `K_RULE` uses from the source are nearby `example`
declarations. They are compile-time regression tests for the tactic, not
additional public theorem names. The tactic targets closed K-derivability
goals with empty hypotheses and is not presented as the later certified
decision procedure.
