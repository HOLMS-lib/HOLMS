# `HOLMS.LabelledB`

Lean module: [`../HOLMS/LabelledB.lean`](../HOLMS/LabelledB.lean)

This module assembles modal B in the Lean deep embedding. It follows the
existing HOLMS convention from [`b_completeness.ml`](../../b_completeness.ml):
`B_AX` contains both the T schema and the B schema, so B is reflexive and
symmetric. The merely symmetric system is KB and will receive its own module.

## System composition and certificates

`B` is `T.union symmCalculus`. It inherits the core and reflexivity
capabilities through T and obtains `HasSymm` from the right component.
`t_included_b` preserves T certificates without changing their raw trees.

The central `symmetricContradictionTree` starts with `x R y`, `x : A`, and
`y : □¬A`. A symmetry step adds `y R x`; box-left and negation-left then
reduce the branch to identity. `bAxiomTree` surrounds this subderivation with
negation-right, box-right, and implication-right, yielding the seven-node
certificate for `A → □◇A`. The eigenlabel must be fresh. T rejects this
particular raw tree because it contains the primitive symmetry rule.

## Soundness

`B_soundOn` composes T soundness with `symmCalculus_soundOn`. Its hypotheses
are `REFLEXIVE frame.worlds frame.rel` and
`SYMMETRIC frame.worlds frame.rel`. `B_derivable_sound` lifts the resulting
local soundness theorem to every B derivation.

## Verification

From `lean/`, run `lake build HOLMS/LabelledB.lean`. The compiled examples
check the B-schema certificate, T-to-B reuse, rejection by T, and the expected
height and node count.
