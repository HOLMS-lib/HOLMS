# Conventions for the HOLMS Lean Port

This document records project-wide conventions for translating HOLMS from
HOL Light to Lean 4. It contains only choices that affect several modules.
Module-specific implementation decisions are indexed in
[`translation/README.md`](translation/README.md).

The HOL Light development remains the mathematical reference. The conventions
below change representation and proof engineering, not the intended modal
logic.

## Modules and dependencies

The Lean port is a Lake library. A HOL Light `needs` dependency becomes a Lean
`import`, and `HOLMS.lean` is the root import for public modules. Add a module
to the root only after it builds independently.

The load order in `make.ml` remains useful for understanding mathematical
dependencies, but it is not copied mechanically. Lean imports should state
the smallest stable dependency needed by a module.

OCaml session initialization, parser installation, printers, and load-order
commands are not mathematical declarations and are not translated.

## Core representations

Modal syntax is the inductive type `HOLMS.Form`. Recursive HOL Light
definitions become ordinary recursive Lean definitions. Lean-generated
instances such as `DecidableEq`, `Repr`, and `Countable` should be reused
rather than reconstructed manually.

HOL predicates used as collections are represented by `Set`. In particular:

- axiom systems and hypothesis contexts have type `Set Form`;
- frame classes have type `Set (Frame W)`;
- finiteness is expressed with `Set.Finite`;
- relations remain predicates rather than executable graph structures.

Kripke frames and models use the structures `Frame W` and `Model W` with named
fields. HOL Light pairs such as `(W,R)` are not reproduced when a structure
already expresses the same object.

## Consistency and canonical worlds

Lean uses only the set-based notion of consistency:

```lean
SETCONSISTENT S X := ¬S ⊢ₘ[X] ⊥ₘ
```

Canonical worlds are likewise `Set Form` and use
`MAXIMAL_SETCONSISTENT`. The list-based predicates `CONSISTENT` and
`MAXIMAL_CONSISTENT` are not independent public notions in the port: the HOL
Light development already proves that they merely present the corresponding
set notions through `set_of_list`.

Lists may still be used locally for finite enumeration, structural recursion,
or executable traversal. Logical consistency, maximality, weakening, and
canonical-world membership should be stated for sets.

Consequently, infrastructure whose only purpose is to quotient list worlds by
order or repetition is omitted. This includes permutation lemmas and the
`*_STDWORLDS`/`*_STDREL` bridges used to manufacture a second set-world
countermodel. In Lean the primary canonical countermodel already has worlds
of type `Set Form`. Preserve a historical theorem name as a direct corollary
only when it is useful to downstream code.

## Modal notation

Modal notation is scoped in `HOLMS.ModalNotation`. The principal symbols are:

| Meaning | Lean notation |
|---|---|
| modal falsity and truth | `⊥ₘ`, `⊤ₘ` |
| negation | `¬p` |
| conjunction and disjunction | `p ⋏ q`, `p ⋎ q` |
| implication and equivalence | `p ⟶ q`, `p ⟷ q` |
| necessity and possibility | `□p`, `◇p` |
| derivability | `S ⊢ₘ[H] p` |

These symbols construct values of type `Form`; they are distinct from Lean's
logical connectives on `Prop`.

The glyph `¬` is also Lean's propositional negation. Parsing precedes type
inference, so an unparenthesized modal negation followed by a modal infix may
be parsed as propositional negation of a larger expression. Parenthesize modal
negations consistently:

```lean
(¬p) ⟶ q
(¬(p ⋏ q)) ⟷ ((¬p) ⋎ (¬q))
```

This avoids `Form.neg` in ordinary formulas without redefining Lean's global
propositional notation.

## Inductive definitions and proof interfaces

HOL Light's `new_inductive_definition` returns named rule, cases, and
induction theorems. Lean inductive propositions expose constructors and
automatically generate recursors. Do not create compatibility constants for
generated HOL Light artifacts unless downstream code genuinely needs a named
interface.

For `ModProves`, use constructors such as `ModProves.kaxiom`,
`ModProves.ax`, and `ModProves.hyp` directly. Preserve the source restriction
on necessitation: its premise is derivable from the empty hypothesis set even
when the conclusion is placed in another context.

Proofs should be idiomatic Lean proofs rather than line-by-line translations
of tactic scripts. Prefer:

- constructors and induction on the relevant datatype or derivation;
- named intermediate derivations when inference is ambiguous;
- set inclusion for weakening and context manipulation;
- the deduction theorem for natural-deduction-style arguments;
- reusable general results over duplicated system-specific proofs.

A HOL Light conjunction used only to bundle premises may become curried Lean
arguments. This changes the programming interface, not the proposition being
formalized.

## Naming and API stability

Preserve public HOLMS definition and theorem names where practical so the two
developments can be compared. Lean foundational declarations may use
idiomatic names such as `Form`, `KAxiom`, and `ModProves`. When a HOL Light
theorem name collides with a Lean definition, use a clear suffix such as
`_EQ` for the characterization theorem.

Keep declarations inside the `HOLMS` namespace and add docstrings to public
definitions and theorems. Retain historical aliases only when they support
comparison or downstream use; do not recreate representation-specific APIs
whose purpose disappeared in the set-based design.

Promote a private helper to a shared module only after more than one module
needs the same mathematical fact. Avoid abstractions that hide the distinct
canonical relations or accessibility arguments of individual modal systems.

## Completeness-based tactics

HOL Light completeness files commonly define both `*_TAC` and an OCaml
`*_RULE` wrapper. Lean exposes one tactic per modal system, named
`modal_<system>`: for example, `modal_k`, `modal_t`, and later `modal_k4` or
`modal_s5`.

There is no separate Lean `*_RULE`. Formula variables normally appear as
declaration binders; explicit Lean quantifiers can be introduced with the
ordinary `intro` tactic before invoking the modal tactic.

Each `modal_<system>` tactic follows the same visible pipeline:

1. apply the system-specific finite-frame completeness theorem;
2. use `simp only` to unfold semantic validity and exactly the frame
   properties for that system;
3. invoke `grind` on the resulting first-order goal.

Keep the simplification list explicit and system-specific. Translate active
HOL Light `*_RULE` examples as nearby Lean `example` declarations so they
serve as compile-time regression tests.

These tactics target closed derivability goals with empty hypotheses. They do
not replace the later certified decision procedures. Every successful tactic
execution must still produce a proof term checked by Lean.

## Computation and metaprogramming

Keep syntax as data, semantic validity and derivability as propositions, and
tactics as metaprograms. Computable operations such as substitution or
subformula enumeration are Lean functions; mathematical claims about them
remain theorems. Do not replace a theorem with an unchecked computation.

## Verification

A translation is complete only when Lean accepts it without `sorry`, `admit`,
new axioms, or weakened statements. For a focused change, first build the
relevant module from the `lean` directory:

```sh
lake build HOLMS/ModuleName.lean
```

After adding a public import or completing a substantial translation, run:

```sh
lake build
```

Successful compilation verifies the Lean development; it does not by itself
prove that the Lean and HOL Light encodings are formally isomorphic. Report
the commands actually run and any remaining unverified behavior.
