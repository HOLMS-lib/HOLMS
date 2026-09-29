# Translating HOLMS from HOL Light to Lean 4

This document records the main conceptual, stylistic, and technical choices
used in the Lean port of HOLMS. It is intended both as a guide for reading the
current translation and as a convention for translating later modules.

The HOL Light development remains the mathematical reference. A difference
listed here is an implementation choice, not a change to the intended modal
logic.

## Project and module structure

HOL Light source files are OCaml scripts evaluated inside a running HOL Light
session. Dependencies are declared with `needs`, and `make.ml` loads the
library in dependency order.

The Lean port is a Lake library:

- `HOLMS/Modal.lean` corresponds to `modal.ml`;
- `HOLMS/Calculus.lean` corresponds to `calculus.ml`;
- `HOLMS/ParametricCorrespondence.lean` corresponds to
  `parametric_correspondence.ml`;
- `HOLMS/AdHocCorrespondence.lean` corresponds to
  `ad_hoc_correspondence.ml`;
- `HOLMS.lean` is the root import module;
- imports replace `needs` and are checked by Lean's module system.

Consequently, OCaml initialization code, parser installation, printers, and
load-order commands are not translated as mathematical declarations.

HOL Light represents a Kripke frame in the correspondence modules as a pair
`(W,R)`. Lean reuses the structure `Frame W`, whose fields are `worlds` and
`rel`. Thus `FRAME`, `FINITE_FRAME`, `CHAR`, and `APPR` are sets of structured
frames rather than sets of pairs. This removes repeated pair decomposition
without changing their membership conditions. HOL Light finiteness becomes
`Set.Finite`, and validity over a frame class remains `Form.Valid`.

## Formulas

In HOL Light, modal formulas are introduced as a recursive HOL datatype named
`form`. In Lean they are represented by the inductive type `HOLMS.Form`:

```lean
inductive Form where
  | falsum
  | verum
  | atom : String → Form
  | neg : Form → Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | imp : Form → Form → Form
  | iff : Form → Form → Form
  | box : Form → Form
```

The constructors have the same mathematical meaning. Lean derives useful
instances such as `DecidableEq`, `Repr`, and `Countable` directly from the
datatype.

Definitions that HOL Light obtains from `new_recursive_definition` are normal
recursive Lean definitions. For example, the HOL Light constant `SUBST` is
implemented by `Form.subst`; `SUBST` is retained as a compatibility alias.

## Notation and concrete syntax

The original files install global HOL Light parser and printer extensions. In
Lean, notation is scoped inside `HOLMS.ModalNotation`. Clients must open that
scope when using the modal symbols.

The principal correspondences are:

| HOL Light         | Lean        |
|-------------------|-------------|
| `False`, `True` as modal formulas | `⊥ₘ`, `⊤ₘ` |
| `Not p`           | `¬p` in the modal notation scope |
| `p && q`          | `p ⋏ q`     |
| `p || q`          | `p ⋎ q`     |
| `p --> q`         | `p ⟶ q`     |
| `p <-> q`         | `p ⟷ q`     |
| `Box p`, `Diam p` | `□p`, `◇p`  |
| `[S . H \|~ p]`   | `S ⊢ₘ[H] p` |

The modal negation symbol is deliberately a scoped notation for `Form.neg`;
it is not Lean's logical negation on propositions. Similarly, `⊥ₘ` and `⊤ₘ`
are formula constructors rather than `False` and `True` in Lean's logic.

## Inductive predicates and generated principles

HOL Light's `new_inductive_definition` returns a collection of theorems such
as `KAXIOM_RULES`, `KAXIOM_INDUCT`, `MODPROVES_RULES`, and
`MODPROVES_INDUCT`. It may then derive an additional strong induction theorem.

Lean instead declares `KAxiom` and `ModProves` as inductive propositions.
Their constructors are the introduction rules, while Lean automatically
generates recursors and induction principles. Thus the HOL Light values
`KAXIOM_RULES`, `MODPROVES_RULES`, and `MODPROVES_INDUCT_STRONG` do not appear
as separate theorem constants in the port.

For example, the HOL Light rules

```text
KAXIOM p ==> [S . H |~ p]
p IN S   ==> [S . H |~ p]
p IN H   ==> [S . H |~ p]
```

correspond to the Lean constructors

```lean
ModProves.kaxiom
ModProves.ax
ModProves.hyp
```

The necessitation constructor preserves the important restriction from the
original calculus: its premise must be derivable from the empty hypothesis
set, although its conclusion may be placed in any hypothesis context.

## Sets and relations

HOL Light predicates such as `form->bool` are generally represented by
`Set Form`. Membership and inclusion therefore use Lean notation `p ∈ S` and
`S ⊆ S'`.

HOL Light set operations map directly to Mathlib operations:

| HOL Light | Lean |
|---|---|
| `{}` | `(∅ : Set Form)` |
| `p INSERT H` | `insert p H` |
| `H DELETE p` | `H \ {p}` |
| `IMAGE f H` | `f '' H` |
| `S SUBSET S'` | `S ⊆ S'` |

The Lean definitions of frames and models use structures with named fields.
Relations remain predicates rather than being converted to executable graph
representations.

## Proof style

HOL Light proofs in the original development frequently use tactic
combinators such as `MESON_TAC`, `REWRITE_TAC`, `MATCH_MP_TAC`, and
`SUBGOAL_THEN`. The Lean translation does not attempt to reproduce those
tactic scripts line by line.

Instead, it favors:

- direct constructor applications for primitive derivations;
- named intermediate derivations when formula inference would be ambiguous;
- induction directly on `Form`, `KAxiom`, or `ModProves`;
- Mathlib set lemmas for context manipulation;
- reuse of the deduction theorem to express natural-deduction-style
  arguments within the Hilbert calculus;
- curried Lean hypotheses in place of HOL conjunctions used only to bundle
  premises.

For example, a HOL Light theorem whose premise is written as

```text
[S . H |~ p --> q] /\ [S . H |~ p]
```

may be exposed in Lean as a theorem taking two arguments. This changes the
programming interface slightly but not the proposition represented by the
rule.

All results are still kernel-checked derivations of `ModProves`. No additional
axioms, `sorry`, `admit`, or unchecked proof-producing computations are used.

## The deduction theorem

The deduction theorem occurs near the end of `calculus.ml`, after most of the
derived propositional library. In the Lean module it is proved earlier and
then used to organize many later proofs:

```lean
(S ⊢ₘ[H] p ⟶ q) ↔ (S ⊢ₘ[insert p H] q)
```

This is a proof-engineering reordering only. Its statement and dependence on
necessitation from the empty hypothesis set are preserved.

## Uniform substitution

`Form.subst` recursively replaces atoms with formulas and commutes with every
formula constructor, including `box`. The corresponding preservation results
retain the original conditions:

- `KAXIOM_SUBST` proves closure of the primitive `K` schemata;
- `SUBST_IMP` requires the additional axiom set to be closed under the chosen
  substitution;
- hypotheses are mapped to `(Form.subst f) '' H`;
- `SUBST_IFF` proves congruence for pointwise provably equivalent
  substitutions.

Unlike an OCaml meta-level substitution function, `Form.subst` is an ordinary
Lean definition whose equations and uses are checked by the kernel.

## Naming

Public theorem names from `calculus.ml` are retained where practical so that
the two developments can be compared mechanically. This includes a few
historical names and spelling variants such as `MLK_box_moduspones` and
`MLK_and_rigth_true_th`.

Lean-specific foundational declarations use idiomatic names (`Form`,
`KAxiom`, `ModProves`, and `Form.subst`). Some theorems use curried arguments
or namespaces even when the corresponding HOL Light statement bundled the
same data differently.

## Semantics and computation

The original HOL Light project distinguishes OCaml meta-language values from
HOL terms and theorems. Lean makes a related distinction between ordinary
definitions in `Type`, propositions in `Prop`, and tactic or elaborator code.
The port keeps modal syntax as data and semantic validity or derivability as
propositions.

Computable syntax operations, such as collecting subformulas or performing a
substitution, are Lean functions. Mathematical claims about them remain
theorems. No theorem is replaced by a Boolean test or an unchecked external
calculation.

## Verification expectations

The Lean port is verified independently of the HOL Light loader. From the
`lean` directory, use:

```sh
lake build HOLMS/Modal.lean
lake build HOLMS/Calculus.lean
lake build
```

A translated result is considered complete only when these relevant modules
compile without proof placeholders. Successful compilation establishes that
Lean accepts the port; it does not by itself constitute a formal theorem that
the Lean and HOL Light encodings are isomorphic.
