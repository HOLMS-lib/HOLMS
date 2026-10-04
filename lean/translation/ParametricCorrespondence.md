# `HOLMS.ParametricCorrespondence`

Lean module: [`../HOLMS/ParametricCorrespondence.lean`](../HOLMS/ParametricCorrespondence.lean)

HOL Light source: [`../../parametric_correspondence.ml`](../../parametric_correspondence.ml)

This note records module-specific representation and proof choices. General
conventions are in [`../CONVENTIONS.md`](../CONVENTIONS.md).

## Frame classes

The module works with sets of `Frame W` structures rather than HOL Light pairs
`(W, R)`. `FRAME W` requires a nonempty designated set of worlds and closure of
accessibility edges inside it. This condition is kept explicit because the
ambient Lean type may contain elements that are not worlds of the frame.

`FINITE_FRAME W` adds `Set.Finite frame.worlds`; it does not require the whole
ambient type `W` to be finite. This distinction is important in later
completeness theorems, where finite designated frames are embedded in an
arbitrary infinite carrier.

## Characteristic and appropriate frames

`CHAR S` is the class of well-formed frames validating every formula in the
axiom set `S`. `APPR S` is the finite subclass validating all formulas
derivable from `S` with no hypotheses. Both remain extensional sets of
structured frames.

The generic soundness proof proceeds by induction on `ModProves`. Primitive K
axioms are handled semantically, additional axioms by membership in `CHAR`,
modus ponens pointwise, and necessitation by the empty-context premise built
into the calculus. Substitution variants are derived using the substitution
infrastructure from `Calculus`.

The characterizations `CHAR_CAR`, `APPR_CAR`, and `APPR_EQ_CHAR_FINITE` are
proved as equalities or membership equivalences of sets. Named structure fields
and extensionality replace the repeated pair decomposition and rewriting used
in HOL Light.

## Deliberate boundaries

Frames remain semantic predicates, not finite executable graphs. This module
does not enumerate valuations or provide a decision procedure for validity.
Concrete relational conditions such as reflexivity and transitivity belong to
`AdHocCorrespondence`; this module supplies only the parametric framework that
connects arbitrary axiom sets with frame classes.
