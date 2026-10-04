# `HOLMS.AdHocCorrespondence`

Lean module: [`../HOLMS/AdHocCorrespondence.lean`](../HOLMS/AdHocCorrespondence.lean)

HOL Light source: [`../../ad_hoc_correspondence.ml`](../../ad_hoc_correspondence.ml)

This note documents choices specific to the concrete correspondence results.
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

`WWF` preserves the source's field-based formulation: well-foundedness is
required on the field of the relation, not on unrelated ambient elements. The
bridge theorem `wwf_iff_wellFounded_strict` relates this definition to Lean's
`WellFounded` predicate for the reversed strict relation. This permits the
Löb and Grzegorczyk arguments to use Lean's well-founded induction while
retaining the exact HOLMS frame condition.

The companion results `WWF_EQ` and `WWF_IND` expose source-compatible
characterizations and induction principles. They are proved from the bridge
rather than postulated as additional axioms.

## Correspondence proofs

Elementary correspondence theorems use direct valuations tailored to a
chosen world when proving a relational property from validity. Conversely,
the semantic directions unfold `Form.holds` and apply the assumed relational
property to accessible designated worlds.

The transitive nonterminal and reflexive-transitive well-founded
correspondences require induction or minimality arguments. In Lean these are
organized around the `WWF` bridge instead of duplicating HOL Light's tactic
script. The formula schemata and frame conditions themselves are unchanged.

## Deliberate boundaries

This module does not redefine `CHAR` or the generic soundness machinery from
`ParametricCorrespondence`. It proves semantic equivalences for individual
schemata; completeness modules later package those equivalences into named
frame classes for particular modal systems.
