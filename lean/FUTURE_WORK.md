# Future work for the Lean implementation

This document collects TODOs, possible improvements, and plans for the Lean
implementation of HOLMS. These are prospective changes, not current
translation requirements. Current conventions are in
[`CONVENTIONS.md`](CONVENTIONS.md); the
[module-specific translation notes](translation/README.md) describe the
implementation choices already made.

## Systematic renaming and use of namespaces

For now, the Lean port preserves public HOLMS definition and theorem names
where practical so the HOL Light and Lean developments can be compared and
corresponding results found easily. This is a deliberate convenience during
the port, rather than a commitment to these names as the final Lean API.

The inherited naming is often unidiomatic in Lean: all-uppercase identifiers
and long names such as `MLK_*` and `MODPROVES_*` reflect HOL Light's flat
naming environment, where prefixes serve the organizational role that Lean
namespaces can provide. We retain these names for now despite their less
natural appearance in Lean. Some foundational declarations already use more
idiomatic names, such as `Form`, `KAxiom`, and `ModProves`.

A future systematic renaming may introduce shorter, more natural and
idiomatic Lean identifiers and make fuller use of namespaces. Such a
migration should update downstream uses and the documented HOL Light
correspondences together, retaining compatibility aliases where needed.
The naming scheme and timing remain to be decided; this is a coordinated
future change, not a request for piecemeal renaming during the translation.
