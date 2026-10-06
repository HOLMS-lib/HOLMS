# Module-specific translation notes

This directory documents the translation of HOLMS from HOL Light to Lean,
with implementation decisions specific to each Lean module. Before changing a module, read the
project-wide [`CONVENTIONS.md`](../CONVENTIONS.md) and then the matching note
below.

| Lean module | Translation note | HOL Light source |
|---|---|---|
| [`HOLMS.lean`](../HOLMS.lean) | [`HOLMS.md`](HOLMS.md) | root aggregate; no direct source file |
| [`HOLMS.Modal`](../HOLMS/Modal.lean) | [`Modal.md`](Modal.md) | [`modal.ml`](../../modal.ml) |
| [`HOLMS.Calculus`](../HOLMS/Calculus.lean) | [`Calculus.md`](Calculus.md) | [`calculus.ml`](../../calculus.ml) |
| [`HOLMS.ParametricCorrespondence`](../HOLMS/ParametricCorrespondence.lean) | [`ParametricCorrespondence.md`](ParametricCorrespondence.md) | [`parametric_correspondence.ml`](../../parametric_correspondence.ml) |
| [`HOLMS.AdHocCorrespondence`](../HOLMS/AdHocCorrespondence.lean) | [`AdHocCorrespondence.md`](AdHocCorrespondence.md) | [`ad_hoc_correspondence.ml`](../../ad_hoc_correspondence.ml) |
| [`HOLMS.SetConsistent`](../HOLMS/SetConsistent.lean) | [`SetConsistent.md`](SetConsistent.md) | [`setconsistent.ml`](../../setconsistent.ml) |
| [`HOLMS.GenCompleteness`](../HOLMS/GenCompleteness.lean) | [`GenCompleteness.md`](GenCompleteness.md) | [`gen_completeness.ml`](../../gen_completeness.ml) |
| [`HOLMS.KCompleteness`](../HOLMS/KCompleteness.lean) | [`KCompleteness.md`](KCompleteness.md) | [`k_completeness.ml`](../../k_completeness.ml) |
| [`HOLMS.TCompleteness`](../HOLMS/TCompleteness.lean) | [`TCompleteness.md`](TCompleteness.md) | [`t_completeness.ml`](../../t_completeness.ml) |

Lean docstrings describe the Lean code on its own terms. Each explicit
Lean declaration also has a concise `-- HOL:` annotation identifying its
HOL Light counterpart and source file, or explaining its role when there is
no separately named counterpart. Constructors and split theorems identify the
relevant source clause; unnamed examples refer to the corresponding source
example. Generated instances are documented at the `deriving` clause.

These annotations are navigation aids, not claims of identical encodings or
formally proved equivalence. A reference can identify a counterpart adapted
to sets, a clause of a larger theorem, or a local construction rather than a
standalone HOL declaration. Statements that no named counterpart exists refer
to the corresponding HOLMS source development.

Detailed translation choices, source comparisons, and the reasons for naming
or representation differences belong in these notes. The concise declaration
annotations are the exception to keeping translation details out of `.lean`
files.

The notes describe representation choices, proof interfaces, deliberate
departures from a mechanical translation, and source material that was not
reproduced. They are not substitutes for the natural-language mathematical
expositions indexed in [`docs/README.md`](../../docs/README.md). That directory
explains definitions, results, and proofs essentially independently of either
implementation; implementation-specific details belong there only when they
are particularly important to understanding the mathematics.

The available mathematical chapters are [Modal](../../docs/Modal.md) and
[Calculus](../../docs/Calculus.md). Each module note should link to its
corresponding mathematical chapter when one is available, without duplicating
that exposition.

When a new Lean module is added, add its note and index entry in the same
change. A choice affecting several modules belongs in `CONVENTIONS.md`; a
choice local to one implementation belongs in that module's note.

[`../TRANSLATION.md`](../TRANSLATION.md) is retained only as a legacy snapshot
of the earlier combined documentation and is not authoritative.
