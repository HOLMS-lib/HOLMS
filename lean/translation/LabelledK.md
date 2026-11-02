# `HOLMS.LabelledK`

Lean module: [`../HOLMS/LabelledK.lean`](../HOLMS/LabelledK.lean)

This is the K-specific assembly of the new Lean deep embedding. It has no
declaration-by-declaration HOL Light counterpart: HOLMS implements labelled K
proof search shallowly in [`k_decid.ml`](../../k_decid.ml). The reusable syntax,
rules, trees, and semantic infrastructure are documented in
[`Labelled.md`](Labelled.md) and
[`LabelledSoundness.md`](LabelledSoundness.md).

## System composition

`K` is definitionally `standardCalculus`, the union of the fifteen
propositional singleton calculi with box-left and box-right. Its `HasCore`
instance is therefore reflexive calculus inclusion. K introduces no new rule
schema and serves as the base imported by the later system modules.

The module also owns K-specific rejection results: a reflexivity node is not
a K step, and a box-right node with no premise is invalid. Generic certificate
builders remain in `HOLMS.Labelled`; K instantiates them to check a branching
conjunction certificate and a boxed-identity certificate with a fresh
eigenlabel.

## Soundness

`K_soundOn` specializes `standardCalculus_soundOn`, so K is sound on every
Kripke frame. `K_derivable_sound` combines this with generic proof-tree
soundness to show that every K-derivable labelled sequent is semantically
valid on every frame.

## Verification

From `lean/`, run `lake build HOLMS/LabelledK.lean`. The public aggregate also
imports this module through `HOLMS.lean`.
