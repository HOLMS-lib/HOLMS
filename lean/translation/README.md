# Module-specific translation notes

This directory documents implementation decisions that apply to one Lean
module rather than to the port as a whole. Before changing a module, read the
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

Lean comments and docstrings describe the Lean code on its own terms. Details
about translation, source correspondence, historical names, and comparisons
with HOL Light belong in these notes, not in `.lean` files.

The notes describe representation choices, proof interfaces, deliberate
departures from a mechanical translation, and source material that was not
reproduced. They are not substitutes for the natural-language mathematical
expositions under [`../../docs`](../../docs).

When a new Lean module is added, add its note and index entry in the same
change. A choice affecting several modules belongs in `CONVENTIONS.md`; a
choice local to one implementation belongs in that module's note.

[`../TRANSLATION.md`](../TRANSLATION.md) is retained only as a legacy snapshot
of the earlier combined documentation and is not authoritative.
