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
- `HOLMS/SetConsistent.lean` corresponds to `setconsistent.ml`;
- `HOLMS/GenCompleteness.lean` is the staged translation of
  `gen_completeness.ml`;
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

## Consistency: sets rather than lists

The HOL Light development currently exposes two consistency predicates:

- `SETCONSISTENT S X`, from `setconsistent.ml`, where `X` is a set of
  formulas;
- `CONSISTENT S xs`, from `consistent.ml`, where `xs` is a list of formulas.

They do not express different mathematical notions. Their definitions are

```text
SETCONSISTENT S X  <=>  not (S proves False from X)
CONSISTENT S xs    <=>  not (S proves False from set_of_list xs)
```

and HOL Light proves this identification explicitly as
`CONSISTENT_IFF_SETCONSISTENT`. Consequently, list order and repeated
formulas carry no logical information for `CONSISTENT`; they are discarded by
`set_of_list`. The same duplication occurs at the maximal-consistency level:
`MAXIMAL_CONSISTENT` is the list presentation corresponding to
`MAXIMAL_SETCONSISTENT`, with an additional no-repetition condition needed
only because the carrier is a list.

Experience with the HOL Light library has shown that the set formulation is
the more useful interface. It matches the hypothesis parameter of
`ModProves`, makes weakening an ordinary subset argument, removes irrelevant
ordering and duplicate-management obligations, and avoids repeatedly moving
through `set_of_list`. The long-term intention for the HOL Light development
is therefore to retire `CONSISTENT` and retain `SETCONSISTENT` as the canonical
notion.

The Lean port will adopt that intended final design immediately:

- consistency will be defined only for `Set Form`, following
  `SETCONSISTENT`;
- maximal consistent collections will likewise be sets, following
  `MAXIMAL_SETCONSISTENT`;
- the future translation should start from `setconsistent.ml` and should not
  reproduce `CONSISTENT` or `MAXIMAL_CONSISTENT` as independent public
  definitions on `List Form`;
- results from `consistent.ml` that are still needed downstream should be
  reformulated and proved for sets, preferably by reusing the corresponding
  results already translated from `setconsistent.ml`;
- `List Form` may still be used locally for finite enumeration, structural
  induction, executable traversal, or an iterated conjunction such as
  `CONJLIST`, but such a list is converted to a set before consistency is
  stated;
- if interoperability with a list-based construction is genuinely needed, a
  bridge lemma about `xs.toFinset` or `{p | p ∈ xs}` may be provided. Such a
  lemma is an interface to the single set-based notion, not a second notion of
  consistency.

This is an intentional departure from a file-by-file mechanical port, but not
from the mathematics: it removes a representation-level duplication whose
equivalence is already proved in HOL Light. It should also simplify later
canonical-model and maximal-extension arguments by using the same carrier
type, `Set Form`, throughout.

## Translation plan for `gen_completeness.ml`

The translation of `gen_completeness.ml` is the first substantial consumer of
the decision to use sets for consistency. The HOL Light file constructs a
finite canonical model around a formula, proves a truth lemma, extracts
countermodels, and supplies the generic semantic argument used by the
completeness files for individual modal systems. Its Lean counterpart should
preserve these mathematical stages, but it should not preserve the original
list representation of canonical worlds.

### Intended module and dependencies

The new module will be `HOLMS/GenCompleteness.lean`. Its direct project
dependencies are expected to be:

- `HOLMS.SetConsistent`, for maximal consistent extensions and their closure
  properties;
- `HOLMS.ParametricCorrespondence`, for `APPR` and `FINITE_FRAME`;
- transitively, `HOLMS.Calculus` and `HOLMS.Modal`, for derivability,
  semantics, frames, models, and bisimulation.

The import must be added to `HOLMS.lean` only after the module compiles. The
corresponding entry in the module list in this document and in `README.md`
should likewise be added when the translation exists, not during the planning
stage.

### Canonical objects

Canonical worlds will be sets of formulas:

```lean
Set Form
```

Accordingly, the principal objects will have the following conceptual Lean
types:

| HOL Light object | Planned Lean representation |
|---|---|
| `PARAMETRIC_STD_WORLD S P p` | `Set (Set Form)` |
| `GEN_STANDARD_FRAME S p` | `Set (Frame (Set Form))` |
| `GEN_STANDARD_REL S p` | `Set Form → Set Form → Prop` |
| `GEN_STANDARD_MODEL S V p` | `Model (Set Form)` |

A world belongs to the canonical frame when it is maximally
`SETCONSISTENT` among the subsentences of the distinguished formula. The
canonical relation has the same mathematical definition as in HOL Light:
every formula whose box belongs to the source world belongs to the target
world. The canonical valuation makes an atom true exactly when that atom is a
member of the world.

This representation makes membership, equality, and inclusion extensional.
There is no ordering of formulas and there are no duplicate formulas to
manage.

### Results to preserve

The following groups form the public mathematical core of the source file and
should be translated, retaining the HOL Light names where they remain
appropriate.

1. **Standard frames and models.** Translate
   `PARAMETRIC_STD_WORLD`, `PARAMETRIC_STANDARD_FRAME_DEF`,
   `STD_FRAME_SCHEMA`, `GEN_STANDARD_WORLD_DEF`, `GEN_STANDARD_WORLD`,
   `GEN_STANDARD_FRAME`, `GEN_STANDARD_FRAME_DEF`,
   `IN_GEN_STANDARD_FRAME`, `GEN_STANDARD_MODEL_DEF`, `STANDARD_EVAL`,
   and `SET_STANDARD_EVAL` using structured Lean frames and models.

2. **Truth lemma.** Translate `GEN_TRUTH_LEMMA` by induction on the
   subsentence formula. The Boolean cases should use the closure theorems for
   maximal set-consistent collections already provided by
   `SetConsistent.lean`; the modal case should use the defining condition on
   standard frames. Preserve hypotheses that are part of the generic public
   interface even when the set-based proof needs them only indirectly.

3. **Standard relation and finiteness.** Translate `GEN_STANDARD_REL` and
   `GEN_FINITE_FRAME_MAXIMAL_CONSISTENT`. Finiteness should not be proved by
   enumerating no-repetition lists. Every canonical world is instead a subset
   of the finite set of subsentences, so `Set.Finite.finite_subsets` gives the
   natural proof. Nonemptiness follows from
   `NONEMPTY_MAXIMAL_SETCONSISTENT`.

4. **Accessibility lemma.** Reformulate
   `GEN_XK_FOR_ACCESSIBILITY_LEMMA` and `GEN_ACCESSIBILITY_LEMMA` with set
   inclusion in place of `SUBLIST`. Given a source world and a formula not
   forced by the relevant boxed assumptions, extend the set consisting of the
   unboxed box contents together with the negated target formula to a maximal
   set-consistent successor. This is the key existence argument used in the
   modal step of later completeness proofs.

5. **Countermodels and generic completeness.** Translate
   `GEN_COUNTERMODEL`, `GEN_COUNTERMODEL_ALT`, and
   `GEN_LEMMA_FOR_GEN_COMPLETENESS`. These results should construct a finite
   canonical countermodel and then transport validity between its world type
   and the arbitrary infinite world type occurring in `APPR`.

### List-specific material to replace

The block `MEM_FLATMAP_LEMMA` through `MEM_FLATMAP_LEMMA_6` is an encoding of
set comprehensions through list filtering and flattening. It should not be
ported literally. Introduce small set-based definitions only for the
collections actually used in proofs; the central example is the set of box
contents

```lean
{q | □q ∈ w}
```

and variants can be expressed with set comprehensions, intersections, images,
and preimages. System-specific variants needed by later completeness modules
should preferably be defined in those modules rather than accumulated in the
generic file.

Likewise, `XK_SUBLIST_XK4` should become an elementary subset lemma if the
generic accessibility proof needs it. If it is used only by the translation
of the K4 development, it belongs in that later module.

The generic accessibility proof will probably need one reusable proof-theoretic
helper: a derivation from a set of unboxed assumptions can be lifted under
`box` when the corresponding boxed assumptions belong to the current world.
This should first be proved locally in `GenCompleteness.lean`. It should be
moved to `Calculus.lean` only if it is genuinely independent of the canonical
model construction and reused elsewhere.

### Material made obsolete by set worlds

The source section on invariance under permutation is representation
infrastructure, not additional modal mathematics. The following results
should therefore not be reproduced in Lean:

- `SET_OF_LIST_EQ_IMP_MEM`;
- `SET_OF_LIST_EQ_CONJLIST` and `SET_OF_LIST_EQ_CONJLIST_EQ`;
- `MEM_EQ_CONJLIST_IMP` and `MEM_EQ_CONJLIST_EQ`;
- `SET_OF_LIST_EQ_CONSISTENT` and
  `SET_OF_LIST_EQ_MAXIMAL_CONSISTENT`;
- `SET_OF_LIST_EQ_STANDARD_REL` and
  `SET_OF_LIST_EQ_GEN_STANDARD_REL`.

Their role is to show that order and repetition in list worlds do not affect
the semantics. For `Set Form`, this invariance is already ordinary set
extensionality.

For the same reason, the auxiliary inductive predicates `GEN_STDWORLDS` and
`GEN_STDREL` should normally disappear. They bridge list worlds with their
set images in the HOL Light bisimulation argument. If a named interface is
needed downstream, it should be an ordinary predicate or definition on set
worlds rather than an inductive wrapper recreating the discarded
representation boundary.

### Validity transport and the main technical risk

The proof of `GEN_LEMMA_FOR_GEN_COMPLETENESS` requires special care. In HOL
Light, a countability argument embeds the list-based canonical world type into
the arbitrary infinite type used by `APPR`. In Lean, the full type `Set Form`
is not countable, so that argument cannot be copied.

Only the worlds of the particular canonical frame need to be embedded. That
set is finite by `GEN_FINITE_FRAME_MAXIMAL_CONSISTENT`; hence its subtype can
be injected into any infinite type. The planned proof is:

1. equip the finite subtype of canonical worlds with its finite instance;
2. choose an embedding of that subtype into the target infinite type;
3. transport the frame and valuation to the image of the embedding;
4. prove the original and transported models bisimilar;
5. use `Form.valid_of_bisimilar` to transfer validity.

This construction, and in particular the interaction between finite subtypes,
embeddings, and transported relations, is the largest technical uncertainty
in the translation. It should be prototyped before committing to the final
statement of the generic completeness theorem. No axiom or stronger
cardinality assumption should be introduced to bypass it.

### Implementation order and verification gates

The work should proceed in independently checkable stages:

1. define canonical worlds, frames, relations, valuations, and models;
2. prove their elementary characterization lemmas;
3. prove the truth lemma;
4. prove finiteness and nonemptiness of the canonical frame;
5. develop the set-based boxed-context helper and accessibility lemma;
6. derive the two countermodel theorems;
7. prototype and complete finite-world validity transport;
8. prove the generic completeness lemma;
9. add the module to `HOLMS.lean`, update the module documentation, and run
   the complete Lean build.

Each stage should compile without `sorry`, `admit`, new axioms, or weakened
statements. Before later system-specific completeness files are translated,
their uses of the discarded flat-map and permutation lemmas must be mapped to
the new set-based interfaces.

The first implementation stage is complete: `GenCompleteness.lean` contains
the canonical-world, standard-frame, standard-model, and canonical-valuation
definitions preceding `GEN_TRUTH_LEMMA`, together with their elementary
characterizations. The truth lemma and all subsequent results remain future
stages of this plan.

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
