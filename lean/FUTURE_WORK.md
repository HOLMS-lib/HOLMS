# Future work for the Lean implementation

This document collects the remaining work needed to complete the HOL Light
port, new mathematical developments planned for Lean, and possible
improvements to the implementation. These are tasks to be carried out;
current conventions are in [`CONVENTIONS.md`](CONVENTIONS.md), and the
[module-specific translation notes](translation/README.md) describe the
implementation choices already made.

## Remaining translation work

The Lean port is not yet complete. The following tasks concern the remaining
translation work.

- **Complete the logic-specific soundness and completeness developments.**
  K and T are already implemented. Translate the remaining developments for
  K4, S4, KB, B, S5, GL, and D, reusing the generic set-based infrastructure
  and shared arguments wherever possible. Include the equivalences between
  alternative axiomatisations of D and account explicitly for every source
  result that is adapted or deferred.
- **Translate decision procedures and certified countermodel construction.**
  Port the generic infrastructure in `gen_decid.ml` and
  `gen_countermodel.ml`, then the system-specific procedures and generators.
  Preserve certification by Lean proofs and distinguish these procedures from
  the completeness-based tactics already available for K and T.
- **Translate the remaining modal translations and Grzegorczyk development.**
  Cover the supporting well-foundedness results, the splitting translation,
  the Grz metatheory and decision procedure via GL, and the
  Gödel–McKinsey–Tarski translation. Review [`make.ml`](../make.ml) and the
  source files to account for results outside the currently translated modules.
- **Complete coverage and verification.** Translate the relevant examples and
  regression tests from `tests.ml` and `grz_tests.ml`, maintain the root
  imports and module notes, and audit coverage against the HOL Light sources.
  Record representation-specific omissions separately from mathematical
  results still to be proved. Completion requires Lean to accept all ported
  proofs without placeholders and the full library build to succeed.

## Further development

The following development extends HOLMS beyond the existing HOL Light library.

### Labelled sequent calculi

In addition to the translation, develop the proof theory of normal modal
logics in Lean using labelled sequent calculi in the style of Sara Negri and
related work. This is a new development: the corresponding proof theory has
not been implemented in the HOL Light library.

The first task is to **implement derivations for modal systems based on
labelled sequents**. Define labels, labelled formulas, relational atoms,
sequent contexts, and inductively generated derivations, making rule premises
and freshness conditions explicit.

The design must be modular: share the propositional and modal core, and
parameterize the calculus by additional rules and their side conditions.
Support all systems currently studied in HOLMS (K, T, K4, S4, KB, B, S5, GL,
D, and Grz), while allowing other normal modal logics to be added without
duplicating the core. Identify the rules and proof obligations needed for
each system, including cases that require more than the usual geometric
frame rules; do not assume that one rule scheme already covers every system.

Subsequent tasks are to establish soundness and completeness, connect the
labelled calculi to the existing Hilbert derivability and Kripke semantics,
and develop structural results such as the admissibility of weakening and
contraction, and cut elimination for the chosen calculi. These are future
proof obligations, not results supplied by the initial derivation definitions.

## Implementation improvements

### Systematic renaming and use of namespaces

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
