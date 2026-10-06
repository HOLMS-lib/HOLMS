# `HOLMS.AdHocCorrespondence`

Lean module: [`../HOLMS/AdHocCorrespondence.lean`](../HOLMS/AdHocCorrespondence.lean)

HOL Light source: [`../../ad_hoc_correspondence.ml`](../../ad_hoc_correspondence.ml)

This note documents choices specific to the concrete correspondence results.
The mathematical presentation is in
[`../../docs/AdHocCorrespondence.md`](../../docs/AdHocCorrespondence.md).
Shared representation conventions are in
[`../CONVENTIONS.md`](../CONVENTIONS.md).

## Axiom schemata and relational properties

The modal schemata D, T, 4, B, 5, Löb, and Grzegorczyk are ordinary functions
from formulas to formulas. A logic-specific axiom set can consequently be
formed later with `Set.range` and combined with ordinary set operations.

Relational properties are parameterized by both a designated set of worlds
and an accessibility relation. Their quantifiers are restricted to designated
worlds, matching the HOLMS notion of frame instead of silently imposing a
property on every value of the ambient type. The argument orientation of
`EUCLIDEAN` follows the source development, which is the orientation used by
the corresponding modal proof.

Uppercase names such as `REFLEXIVE`, `TRANSITIVE`, and `SYMMETRIC` are retained
because these predicates include the designated-world parameter and are not
identical as interfaces to Lean's unrestricted relation predicates.

## Converse well-foundedness

`WWF` preserves the source's field-based formulation: each nonempty subset
of the field must have a point with no distinct predecessor in that subset.
Self-loops are permitted. The
bridge theorem `wwf_iff_wellFounded_strict` relates this definition to Lean's
`WellFounded` predicate after removing the diagonal of the supplied relation.
Applied to converse accessibility, it gives induction on distinct accessible
successors in the Grzegorczyk proof. Löb's correspondence uses ordinary
well-foundedness of converse accessibility directly.

The companion results `WWF_EQ` and `WWF_IND` expose source-compatible
characterizations and induction principles. `WWF_EQ` unfolds the definition;
the forward direction of `WWF_IND` uses the bridge. Neither is postulated
as an additional axiom.

## Correspondence proofs

Elementary correspondence theorems use direct valuations tailored to a
chosen world when proving a relational property from validity. Conversely,
the semantic directions unfold `Form.holds` and apply the assumed relational
property to accessible designated worlds.

The Löb and Grzegorczyk correspondences require well-founded induction and
chain arguments. Lean uses the `WWF` bridge for Grzegorczyk and a library
characterization of failure of well-foundedness by descending chains in both
converse proofs. The formula schemata and frame conditions are unchanged.

## Deliberate boundaries

This module does not redefine `CHAR` or the generic soundness machinery from
`ParametricCorrespondence`. It proves semantic equivalences for individual
schemata; completeness modules later package those equivalences into named
frame classes for particular modal systems.
