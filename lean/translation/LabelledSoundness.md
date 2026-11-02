# `HOLMS.LabelledSoundness`

Lean module:
[`../HOLMS/LabelledSoundness.lean`](../HOLMS/LabelledSoundness.lean)

This module is a new Lean development with no direct HOL Light counterpart.
It supplies Kripke soundness for the deep embedding defined in
[`HOLMS.Labelled`](../HOLMS/Labelled.lean). The existing HOL Light proof-search
tactics are a shallow embedding and do not expose corresponding rule schemas
or proof trees. Shared translation conventions are in
[`CONVENTIONS.md`](../CONVENTIONS.md), and the mathematical design is described
in [`docs/Labelled.md`](../../docs/Labelled.md).

## Semantic interpretation

A `LabelAssignment W` maps every syntactic natural-number label to a world of
type `W`. `LabelAssignment.Respects frame assignment` requires every assigned
world to belong to the designated set `frame.worlds`. Quantifying over total
assignments keeps rule soundness uniform; on a well-formed nonempty frame it is
equivalent to choosing designated interpretations for the finitely many labels
that occur in a sequent.

`LFormula.Holds` evaluates the underlying modal formula at the world assigned
to its label. `RelAtom.Holds` evaluates a syntactic relational atom using the
frame relation. A `Sequent.Counterexample` consists of an assignment and
valuation under which every relational atom and every antecedent formula is
true while every succedent formula is false. `Sequent.ValidOn` says that no
such counterexample exists for any frame-respecting assignment and valuation.
The counterexample presentation is equivalent to the ordinary multiple-
succedent reading and makes local rule proofs direct.

## Compositional soundness

`RuleSchema.SoundOn frame schema` states that every accepted instance of the
schema preserves semantic validity from all its premises to its conclusion.
`Calculus.SoundOn frame C` requires this property for every name registered by
the calculus. The module proves:

- the empty calculus is sound;
- a singleton calculus is sound when its schema is sound;
- pointwise union of sound calculi is sound;
- a finite `Calculus.unions` of sound calculi is sound.

Thus semantic soundness follows the same composition structure as the rule
maps themselves. It is not encoded as an additional field of `Calculus` and
does not affect raw certificates.

## Primitive rules

Every primitive schema in `HOLMS.Labelled` has its own `soundOn` theorem. The
initial and propositional cases use only the truth clauses of `Form.holds`.
`BoxLeftStep.soundOn` uses the relational atom in the conclusion and the fact
that all assigned labels denote designated worlds.

`BoxRightStep.soundOn` is the significant eigenlabel argument. A
counterexample to the conclusion supplies a designated successor at which the
principal boxed formula fails. The proof updates the assignment only at the
fresh eigenlabel and uses the freshness condition to show that the relational,
antecedent, and old succedent contexts retain their meanings. The updated
assignment is therefore a counterexample to the premise.

`ReflStep.soundOn` requires
`REFLEXIVE frame.worlds frame.rel`, reusing the relational property already
defined by `HOLMS.AdHocCorrespondence`. The added self-edge is then true at
the world assigned to its label. `SymmStep.soundOn` similarly requires
`SYMMETRIC frame.worlds frame.rel`: truth of the forward edge in the
conclusion supplies truth of the auxiliary reverse edge in the premise.

Each primitive result is packaged for its singleton calculus. Their unions
prove `propositionalCalculus_soundOn` and `standardCalculus_soundOn`, while
`reflCalculus_soundOn` and `symmCalculus_soundOn` expose the frame-relative
extension results. The individual K, T, and B modules compose these theorems
in exactly the same shape as their calculus definitions.

## From local rules to derivability

`Valid.soundOn` inducts over a valid raw proof tree. At each node it invokes
local calculus soundness and the induction hypotheses for the children.
`Derivable.soundOn` removes the existential proof-tree wrapper. System-level
specializations are intentionally colocated with their definitions:
`K_derivable_sound` in `HOLMS.LabelledK`, `T_derivable_sound` in
`HOLMS.LabelledT`, and `B_derivable_sound` in `HOLMS.LabelledB`.

These generic results are the reusable semantic foundation for implemented
and future calculi. They do not establish completeness, correspondence with
the Hilbert calculi, structural admissibility, cut elimination, or an
executable certificate checker.

## Verification

From `lean/`, build the module with
`lake build HOLMS/LabelledSoundness.lean`, then run `lake build` to verify the
public aggregate. The development contains no proof placeholders or added
axioms.
