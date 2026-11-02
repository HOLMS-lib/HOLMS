# `HOLMS.LabelledT`

Lean module: [`../HOLMS/LabelledT.lean`](../HOLMS/LabelledT.lean)

This module assembles modal T in the Lean deep embedding. HOL Light's
[`t_decid.ml`](../../t_decid.ml) supplies the related shallow proof search, but
does not expose the same rule and proof-tree datatypes. Common infrastructure
is documented in [`Labelled.md`](Labelled.md) and
[`LabelledSoundness.md`](LabelledSoundness.md).

## System composition and certificates

`T` is `K.union reflCalculus`. The `HasCore` and `HasRefl` instances are the
two component inclusions, and `k_included_t` makes certificate reuse explicit:
a K-valid raw tree remains the identical tree in T.

`reflexiveBoxTree` uses reflexivity and box-left to derive
`x : □A ⊢ x : A`. `tAxiomTree` adds implication-right and derives
`x : □A → A`. Its validity requests only propositional rules, box-left, and
reflexivity; it deliberately does not request box-right. A private regression
calculus omitting box-right checks that these capability hypotheses are
genuinely granular. The concrete T-schema tree is rejected in K because it
contains a primitive reflexivity node.

## Soundness

`T_soundOn` unions K soundness with `reflCalculus_soundOn`. It therefore
requires `REFLEXIVE frame.worlds frame.rel`. `T_derivable_sound` lifts this
local result to every T derivation.

## Verification

From `lean/`, run `lake build HOLMS/LabelledT.lean`. Its examples also check
the height and node count of the explicit T-schema certificate.
