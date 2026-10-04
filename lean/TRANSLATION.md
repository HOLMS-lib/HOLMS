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
- `HOLMS/GenCompleteness.lean` corresponds to `gen_completeness.ml`;
- `HOLMS/KCompleteness.lean` corresponds to `k_completeness.ml`;
- `HOLMS/TCompleteness.lean` currently translates the theoretical part of
  `t_completeness.ml`; its `T_TAC` and `T_RULE` utilities are a separate
  pending stage;
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

The Lean port adopts that intended final design:

- consistency is defined only for `Set Form`, following
  `SETCONSISTENT`;
- maximal consistent collections are likewise sets, following
  `MAXIMAL_SETCONSISTENT`;
- `SetConsistent.lean` translates `setconsistent.ml` and does not reproduce
  `CONSISTENT` or `MAXIMAL_CONSISTENT` as independent public definitions on
  `List Form`;
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
equivalence is already proved in HOL Light. It simplifies canonical-model and
maximal-extension arguments by using the same carrier type, `Set Form`,
throughout.

## Translation of `gen_completeness.ml`

The translation of `gen_completeness.ml` is the first substantial consumer of
the decision to use sets for consistency. The HOL Light file constructs a
finite canonical model around a formula, proves a truth lemma, extracts
countermodels, and supplies the generic semantic argument used by the
completeness files for individual modal systems. `GenCompleteness.lean`
preserves these mathematical stages while replacing the original list
representation of canonical worlds with sets.

### Module and dependencies

The translated module is `HOLMS/GenCompleteness.lean`. Its direct project
dependencies are:

- `HOLMS.SetConsistent`, for maximal consistent extensions and their closure
  properties;
- `HOLMS.ParametricCorrespondence`, for `APPR` and `FINITE_FRAME`;
- transitively, `HOLMS.Calculus` and `HOLMS.Modal`, for derivability,
  semantics, frames, models, and bisimulation.

After the module was verified independently, it was added to the root import
`HOLMS.lean` and to the module lists in this document and `README.md`.

### Canonical objects

Canonical worlds are sets of formulas:

```lean
Set Form
```

Accordingly, the principal objects have the following conceptual Lean types:

| HOL Light object | Lean representation |
|---|---|
| `PARAMETRIC_STD_WORLD S P p` | `Set (Set Form)` |
| `GEN_STANDARD_FRAME S p` | `Set (Frame (Set Form))` |
| `GEN_STANDARD_REL S p` | `Set Form → Set Form → Prop` |
| `GEN_STANDARD_MODEL S p (W,R) V` | `GEN_STANDARD_MODEL S p model` for `model : Model (Set Form)` |

A world belongs to the canonical frame when it is maximally
`SETCONSISTENT` among the subsentences of the distinguished formula. The
canonical relation has the same mathematical definition as in HOL Light:
every formula whose box belongs to the source world belongs to the target
world. The canonical valuation makes an atom true exactly when that atom is a
member of the world.

This representation makes membership, equality, and inclusion extensional.
There is no ordering of formulas and there are no duplicate formulas to
manage.

### Why the set-based development is shorter

Most of the simplification in `GenCompleteness.lean` comes from representing
canonical worlds by `Set Form`, not from an intrinsic difference between the
Lean and HOL Light provers. A set is the mathematical object that the
list-based HOL Light development repeatedly reconstructs through
`set_of_list`; choosing it as the carrier removes proof obligations about
order, repetition, enumeration, and conversion between list membership and
set membership.

This affects almost every part of the module:

- the truth lemma uses closure properties stated directly as membership
  equivalences, instead of passing through `CONJLIST` and derivability from an
  encoded list;
- finiteness follows because every world is a subset of the finite set of
  subsentences, rather than from finiteness of duplicate-free lists;
- box contents are set comprehensions, so the `MEM_FLATMAP_LEMMA` family is
  replaced by ordinary membership and inclusion reasoning;
- the accessibility construction extends a set of hypotheses directly and
  uses the boxed-derivation lifting principle, avoiding list concatenation,
  `SUBLIST`, and boxed iterated conjunctions;
- invariance under permutations and the auxiliary passage from list worlds to
  set worlds disappear entirely, since equality of worlds is already set
  extensionality;
- the standard and set-standard valuations coincide, and the countermodel
  theorems no longer need to move between two representations of a world.

There is one important tradeoff. The type `Set Form` itself is generally
uncountable, whereas `List Form` is countable. Consequently, the final
validity-transport proof cannot embed the whole Lean world type into an
arbitrary infinite domain. It instead embeds only the finite subtype of worlds
designated by the particular canonical frame. Thus the set representation
simplifies the canonical-model mathematics throughout the file, while making
the cardinality step more precise rather than eliminating it.

### Results preserved

The following groups form the public mathematical core preserved from the
source file, retaining the HOL Light names where they remain appropriate.

1. **Standard frames and models.** The translation retains
   `PARAMETRIC_STD_WORLD`, `PARAMETRIC_STANDARD_FRAME_DEF`,
   `STD_FRAME_SCHEMA`, `GEN_STANDARD_WORLD_DEF`, `GEN_STANDARD_WORLD`,
   `GEN_STANDARD_FRAME`, `GEN_STANDARD_FRAME_DEF`,
   `IN_GEN_STANDARD_FRAME`, `GEN_STANDARD_MODEL_DEF`, `STANDARD_EVAL`,
   and `SET_STANDARD_EVAL`, using structured Lean frames and models.

2. **Truth lemma.** `GEN_TRUTH_LEMMA` is proved by induction on the subformula.
   The Boolean cases use the closure theorems for maximal set-consistent
   collections from `SetConsistent.lean`; the modal case uses the defining
   condition on standard frames. The nonderivability hypothesis from the HOL
   Light interface is retained even though the structural induction does not
   use it directly.

   The resulting proof is substantially shorter than its HOL Light
   counterpart because its canonical worlds are sets, not because Lean proves
   the same statement more powerfully. In HOL Light, the propositional cases
   repeatedly pass through `CONJLIST`, derivability from the conjunction of a
   world, list membership, and auxiliary results insensitive to ordering and
   repetition. With a `Set Form` world, the closure theorems for
   `MAXIMAL_SETCONSISTENT` already state exactly the membership equivalences
   needed for negation, conjunction, disjunction, implication, and
   equivalence, so the induction hypotheses turn these cases into direct
   rewrites. The boxed case is similarly short: the standard-frame condition
   converts membership of `□q` into membership of `q` at every relational
   successor, the induction hypothesis converts membership into truth, and
   frame well-formedness ensures that every successor is a designated world.

3. **Standard relation and finiteness.** `GEN_STANDARD_REL` and
   `GEN_FINITE_FRAME_MAXIMAL_CONSISTENT` retain their mathematical content.
   Finiteness is not proved by enumerating no-repetition lists: every
   canonical world is a subset of the finite set of subsentences, so
   `Set.Finite.finite_subsets` gives the natural proof. Nonemptiness follows
   from `NONEMPTY_MAXIMAL_SETCONSISTENT`.

4. **Accessibility lemma.** `GEN_XK_FOR_ACCESSIBILITY_LEMMA` and
   `GEN_ACCESSIBILITY_LEMMA` use set inclusion in place of `SUBLIST`. Given a
   source world and a formula not forced by the relevant boxed assumptions,
   the proof extends the set consisting of the unboxed box contents together
   with the negated target formula to a maximal set-consistent successor. This
   is the key existence argument used in the modal step of later completeness
   proofs.

5. **Countermodels and generic completeness.** `GEN_COUNTERMODEL` and
   `GEN_COUNTERMODEL_ALT` extract a finite canonical countermodel.
   `GEN_LEMMA_FOR_GEN_COMPLETENESS` transports validity between its world type
   and the arbitrary infinite world type occurring in `APPR`.

### Replacement of list-specific material

The block `MEM_FLATMAP_LEMMA` through `MEM_FLATMAP_LEMMA_6` is an encoding of
set comprehensions through list filtering and flattening. It is not ported
literally. The Lean module introduces small set-based definitions only for the
collections actually used in generic proofs; the central example is the set
of box contents

```lean
{q | □q ∈ w}
```

and variants are expressed with set comprehensions, unions, images, and
preimages. System-specific variants needed by later completeness modules
should preferably be defined in those modules rather than accumulated in the
generic file.

Likewise, `XK_SUBLIST_XK4` is retained as an elementary subset lemma between
`GEN_BOX_CONTENT` and `GEN_BOX_CONTENT_K4`; despite its historical name, its
Lean statement contains no lists.

The generic accessibility proof uses a local proof-theoretic lifting
principle. If `S ⊢ₘ[Γ] p` and the current world `w` contains `□q` for every
`q ∈ Γ`, then `S ⊢ₘ[w] □p`. In `GenCompleteness.lean` this is the private
theorem `box_derivation_from_context`. Its proof is an induction on the given
derivation: primitive and additional axioms are boxed by necessitation; a
hypothesis is replaced by its boxed counterpart in `w`; modus ponens is lifted
with `MLK_box_modusponens`; and a necessitation conclusion is boxed again.
The final case relies essentially on the calculus restriction that
necessitation premises are derivable from the empty hypothesis set.

This principle replaces the HOL Light construction through `CONJLIST`, the
list of boxed hypotheses, and distributivity of `box` over the encoded finite
conjunction. It is used to show that inconsistency of
`insert (¬q) (GEN_BOX_CONTENT w)` would derive `□q` from `w`, contradicting
the assumed absence of `□q`. The theorem remains private for now because its
only current use is the canonical accessibility argument; it should move to
`Calculus.lean` if later translations reuse it independently.

### Material made obsolete by set worlds

The source section on invariance under permutation is representation
infrastructure, not additional modal mathematics. The following results are
therefore not reproduced in Lean:

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
`GEN_STDREL` are omitted. They bridge list worlds with their set images in the
HOL Light bisimulation argument. If a named interface becomes necessary in a
later module, it should be an ordinary predicate or definition on set worlds
rather than an inductive wrapper recreating the discarded representation
boundary.

### Validity transport and the main technical tradeoff

The proof of `GEN_LEMMA_FOR_GEN_COMPLETENESS` requires special care. In HOL
Light, a countability argument embeds the list-based canonical world type into
the arbitrary infinite type used by `APPR`. In Lean, the full type `Set Form`
is not countable, so that argument cannot be copied.

Only the worlds of the particular canonical frame need to be embedded. That
set is finite by membership in `APPR`; hence its subtype can be injected into
any infinite type. The implemented proof:

1. equip the finite subtype of canonical worlds with its finite instance;
2. choose an embedding of that subtype into the target infinite type;
3. transport the frame and valuation to the image of the embedding;
4. prove the original and transported models bisimilar;
5. use `Form.valid_of_bisimilar` to transfer validity.

This construction, and in particular the interaction between finite subtypes,
embeddings, and transported relations, is the principal technical complication
introduced by choosing set worlds. The Lean proof carries it out without a new
axiom or a stronger cardinality assumption.

### Implementation stages and verification

The work was completed in independently checkable stages:

1. canonical worlds, frames, relations, valuations, and models were defined;
2. their elementary characterization lemmas were proved;
3. the truth lemma was proved;
4. finiteness and nonemptiness of the canonical frame were established;
5. the set-based boxed-context helper and accessibility lemma were developed;
6. the two countermodel theorems were derived;
7. finite-world validity transport was prototyped and completed;
8. the generic completeness lemma was proved;
9. the module was added to `HOLMS.lean`, the documentation was updated, and
   the complete Lean build was run.

Each stage was compiled before proceeding to the next, and the completed
module passes the full Lean build without `sorry`, `admit`, new axioms, or
weakened statements. When later system-specific completeness files are
translated, their uses of the discarded flat-map and permutation lemmas must
be mapped to the new set-based interfaces.

The translation of the mathematical content of `gen_completeness.ml` is now
complete. `GenCompleteness.lean` contains the canonical-world,
standard-frame, standard-model, and canonical-valuation definitions; the
truth, finiteness, and accessibility lemmas; the generic countermodel
theorems; and finite-world validity transport. The original flat-map lemmas
have been replaced by set-based box-content definitions, while the
permutation, `set_of_list`, `GEN_STDWORLDS`, and `GEN_STDREL` sections have no
separate declarations because their sole purpose was to mediate between list
worlds and their underlying sets.

## Plan for the logic-specific completeness modules

The next group of source files specializes the generic construction to the
individual normal modal logics:

- `k_completeness.ml`;
- `t_completeness.ml`;
- `k4_completeness.ml`;
- `s4_completeness.ml`;
- `kb_completeness.ml`;
- `b_completeness.ml`;
- `s5_completeness.ml`;
- `gl_completeness.ml`;
- `d_completeness.ml`.

The source load order in `make.ml` is K, T, K4, S4, KB, B, S5, GL, and D.
That order must remain the reference when checking dependencies in the HOL
Light library, but it need not be copied mechanically in Lean. Most of these
files depend only on the generic completeness infrastructure and on the
correspondence theorems, rather than on one another.

The intended Lean modules are `KCompleteness.lean`, `TCompleteness.lean`,
`K4Completeness.lean`, `S4Completeness.lean`, `KBCompleteness.lean`,
`BCompleteness.lean`, `S5Completeness.lean`, `GLCompleteness.lean`, and
`DCompleteness.lean`. Each module should be added to `HOLMS.lean` only after it
compiles independently.

`KCompleteness.lean` has now been completed and establishes the common module
shape described below. Its main completeness theorem already uses worlds of
type `Set Form`; `K_COUNTERMODEL_FINITE_SETS` is therefore a direct corollary
of the generic countermodel construction rather than the endpoint of a second
list-to-set bisimulation. The theoretical part of `TCompleteness.lean` is also
complete; its rudimentary automation remains deliberately separate from the
mathematical translation. K4 is the next unstarted completeness module.

### Common mathematical pattern

Each source file follows essentially the same outer argument:

1. define the set of additional axiom instances and prove its elementary
   membership and derivability lemmas;
2. define the relevant class of frames and identify it with `CHAR` of the
   axiom set by the results in `AdHocCorrespondence.lean`;
3. identify the finite subclass with `APPR` and derive soundness and
   consistency;
4. specialize the generic standard frame, model, valuation, and truth lemma;
5. choose a canonical relation whose finite canonical frame has the required
   relational property;
6. prove the logic-specific accessibility lemma;
7. apply `GEN_COUNTERMODEL` or `GEN_COUNTERMODEL_ALT` to obtain a finite
   countermodel and hence completeness over canonical set worlds;
8. apply `GEN_LEMMA_FOR_GEN_COMPLETENESS` to transport the result to an
   arbitrary infinite world type.

The Lean translation should preserve this mathematical organization and the
principal public theorem names. Definitions and theorems that merely
specialize a generic declaration may be very short aliases or corollaries;
retaining those names is useful to later modules and to comparison with HOL
Light, even when no new proof is needed.

The axiom sets have direct set-based definitions:

| Logic | Lean axiom set | Frame condition |
|---|---|---|
| K | `∅` | arbitrary frames |
| T | `Set.range T_SCHEMA` | reflexive |
| K4 | `Set.range FOUR_SCHEMA` | transitive |
| S4 | `Set.range FOUR_SCHEMA ∪ Set.range T_SCHEMA` | reflexive and transitive |
| KB | `Set.range B_SCHEMA` | symmetric |
| B | `Set.range B_SCHEMA ∪ Set.range T_SCHEMA` | reflexive and symmetric |
| S5 | `Set.range FIVE_SCHEMA ∪ Set.range T_SCHEMA` | reflexive and Euclidean |
| GL | `Set.range LOB_SCHEMA` | transitive and conversely well-founded; finite approximation: irreflexive and transitive |
| D | `Set.range D_SCHEMA` | serial |

The corresponding unrestricted and finite frame classes should remain named
`REFL`/`RF`, `TRANS`/`TF`, `RTRANS`/`RTF`, `SYM`/`SYF`, `RSYM`/`RSF`,
`REUCL`/`REF`, `TRANSNT`/`ITF`, and `SER`/`SERF` where those historical names
are public. In Lean they are sets of `Frame W`, not sets of pairs. Their
characteristic-class proofs should reuse `MODAL_REFL`, `MODAL_TRANS`,
`MODAL_SYM`, `MODAL_EUCL`, `MODAL_TRANSNT`, and `MODAL_SER` rather than repeat
the semantic arguments.

### Consequences of using set worlds

The decision to make canonical worlds `Set Form` continues to simplify the
whole family of completeness proofs, not only the generic truth lemma. The
system-specific accessibility contexts can be stated directly as sets. For
example:

- K, T, and D use `insert (¬q) (GEN_BOX_CONTENT w)` for accessibility; D
  additionally extends `GEN_BOX_CONTENT w` without `¬q` to prove seriality;
- K4 and S4 use `insert (¬q) (GEN_BOX_CONTENT_K4 w)`, where both a boxed
  formula and its unboxed content are retained;
- GL additionally inserts `□q` to provide the strictness witness required by
  its canonical relation;
- KB and B add selected negated boxes recording the information needed for
  the reverse accessibility condition;
- S5 combines boxes already present at the source with its negated boxes.

These are ordinary set unions, images, preimages, and comprehensions. Their
finiteness follows from the finiteness of the canonical world and of the
subsentence set. There should be no new list-valued consistency predicate,
no reconstruction of these contexts with `FLATMAP`, and no duplication of
the `MEM_FLATMAP_LEMMA` family.

The final sections of every HOL Light file build `*_STDWORLDS` and
`*_STDREL`, prove invariance under `set_of_list`, and derive a second
`*_COUNTERMODEL_FINITE_SETS` theorem. They exist because the main HOL Light
canonical model uses lists. They are obsolete in the Lean representation:
the main countermodel already has worlds of type `Set Form`. If a downstream
file depends on a historical `*_COUNTERMODEL_FINITE_SETS` name, it may be
provided as a direct corollary or alias of the main countermodel theorem, but
the list-to-set bisimulation should not be recreated.

The OCaml values `K_TAC`, `T_TAC`, `K4_TAC`, and their analogues, together
with the `*_RULE` wrappers, are proof-producing meta-level utilities rather
than modal completeness theorems. They belong to the later translation of
the decision-procedure modules, not to this stage. The completeness modules
should expose the propositions from which future Lean tactics can be built,
without attempting to translate OCaml tactic code as logical declarations.

### Shared proof-theoretic infrastructure to review first

The generic proof already contains the useful local theorem
`box_derivation_from_context`: a derivation from `Γ` can be lifted under
`box` when the target context contains `□r` for every `r ∈ Γ`. It is currently
private because `GenCompleteness.lean` was its first user. K4, S4, GL, and D
need the same idea in their consistency arguments, and the symmetric and
Euclidean cases may also benefit from it.

Before duplicating any proof, the first logic-specific implementation should
determine the smallest public form of this theorem. If it is reused outside
the generic K accessibility proof, it should be moved or generalized under a
stable public name, preferably in `Calculus.lean` because it is a fact about
`ModProves`, not about canonical frames. This is the set-based replacement
for several HOL Light lemmas that box a `CONJLIST` of assumptions. The move
must be a focused API refactoring: `GenCompleteness.lean` should continue to
use the same theorem and its behavior must not change.

No larger abstraction should be introduced before completing K. K will show
which parts of the repeated countermodel argument are genuinely boilerplate.
Only after that prototype compiles should a common packaging theorem be
considered. Prematurely abstracting all nine canonical relations would make
the difficult accessibility proofs harder to state and debug.

### Per-logic analysis

#### K: completed baseline specialization

K was the first module translated. Its additional axiom set is empty and its
canonical relation is exactly `GEN_STANDARD_REL ∅ p`. The generic
accessibility lemma applies without strengthening the extension context.
Consequently, the module mostly consists of correspondence,
soundness, consistency, and thin specializations of the generic truth,
countermodel, and completeness results.

The completed translation settles naming, namespace use, theorem argument
order, and the standard shape of a logic-specific module without introducing
machinery tailored to harder systems. It preserves the public mathematical
theorem names, omits the OCaml tactic wrappers, and replaces the final
list-to-set construction with a direct theorem about the existing set-world
canonical frame.

#### T: theoretical translation completed; automation pending

T also uses the generic canonical relation. The additional obligation is to
show that it is reflexive. If `□B` belongs to a maximal T-consistent world,
the T axiom derives `B` from it; maximal-set closure then gives `B` as a
member of the same world. With set hypotheses this is a direct derivability
and membership argument, replacing the source proof through a singleton list
and `CONJLIST`.

This theoretical translation is complete and establishes a reusable pattern
for obtaining canonical relation properties from an axiom schema. It includes
the axiom set, reflexive frame classes, correspondence, soundness,
consistency, specialized standard models and truth lemma, accessibility,
finite countermodels, and both forms of completeness.

The HOL Light file additionally defines `T_TAC` by applying completeness and
then discharging the resulting finite reflexive-frame semantic goal with
`MESON_TAC`; `T_RULE` packages that tactic as a theorem-producing function.
These are meta-level automation rather than missing steps in the completeness
proof. Their Lean counterparts are intentionally reserved for a second stage,
where the appropriate interface (tactic macro, elaborator, or theorem-level
procedure) can be chosen and tested independently of the mathematical module.

#### K4: persistence under boxes

K4 strengthens the relation by requiring every boxed formula in the source
world to remain boxed in the target. Axiom 4 then gives this persistence, and
the strengthened relation is transitive.

The accessibility extension must contain both `B` and `□B` whenever `□B`
belongs to the source world. `GEN_BOX_CONTENT_K4` already represents exactly
this set. The principal proof obligation is its consistency together with
`¬q`; this is where the public boxed-context lifting theorem is likely to be
needed. The source proof's `CONJLIST_FLATMAP_DOT_BOX_LEMMA_K4` should become a
set-level derivation using the K4 theorem `□B ⟶ (□B ⋏ □□B)`, rather than a
literal translation of the flattened list.

#### S4: combination of T and K4

S4 combines T's reflexivity argument with K4's persistent relation,
transitivity proof, and strengthened accessibility context. It should be
translated only after both T and K4, reusing their proof patterns and any
general helper extracted while translating K4. The almost identical K4 and
S4 `CONJLIST_FLATMAP` proofs in HOL Light are evidence for sharing the
set-based lemma, not for copying both scripts.

#### D: seriality and a dependency boundary

The core D completeness argument uses the generic canonical relation. Its
extra task is seriality: for each canonical world, the unboxed contents of
its boxed formulas must form a consistent set and hence extend to a
successor. If that set were inconsistent, boxed lifting would yield `□⊥ₘ`;
the D axiom then contradicts maximal consistency. This should be proved
directly for `GEN_BOX_CONTENT w`.

There is a separate dependency problem at the beginning of
`d_completeness.ml`. The equivalences between `D_AX`, the single instance
`D_bot_AX`, and `D'_AX = {¬□⊥ₘ}` use `HOLMS_TAC`, so the whole source file
loads `k_decid.ml`. The Lean decision-procedure layer has not yet been
translated, but this dependency is not mathematically necessary for the core
serial-frame completeness theorem. The Lean work should therefore be split:

1. translate D's axiom set, correspondence, serial canonical frame,
   countermodel, and completeness without importing a decision procedure;
2. prove `D_EQ_D_bot` and `D_EQ_D'` later either by explicit Hilbert
   derivations from `Calculus.lean`, or after the relevant certified tactic
   infrastructure exists;
3. do not make `DCompleteness.lean` depend on a future `KDecid.lean` solely
   for these two ancillary equivalences.

If an explicit proof of the equivalences is found during the D translation,
it may be included immediately, but their temporary absence must be recorded
as a deliberate scoped deferral rather than hidden by weakening another
statement.

#### KB and B: symmetry and reverse information

KB augments the generic relation with the reverse condition
`□B ∈ x → B ∈ w`. Its characterization is symmetric, so the canonical frame
is symmetric by construction. B uses the same relation shape and adds T,
therefore also proves reflexivity.

The hard part is accessibility. In addition to `¬q` and the ordinary box
contents of `w`, the extension context contains selected formulas `¬□E`
whose unboxed negations `¬E` occur in `w` and whose boxes are relevant
subsentences. These formulas ensure the reverse half of the relation. The
Lean proof should give this finite set a named definition and prove its
finiteness, subsentence closure, and consistency separately. This will make
the use of axiom B visible, instead of burying it in a large flattened-list
calculation.

KB should be completed before B. The B module can then add the already known
T reflexivity argument to the symmetric construction rather than rederive
the whole accessibility proof.

#### GL: strict transitive accessibility

GL first derives axiom 4 from Löb's axiom. Its canonical relation contains
three ingredients: the generic forward condition, persistence of boxed
formulas, and a strictness witness `E` such that `□E` occurs in the target
while `¬□E` occurs in the source. The witness makes the relation irreflexive;
the forward and persistence clauses make it transitive.

For a missing `□q`, the extension context is conceptually
`{¬q, □q} ∪ GEN_BOX_CONTENT_K4 w`. The inserted `□q` supplies the strictness
witness, while Löb's axiom proves the context consistent. This consistency
argument is the main risk in GL and should be isolated as a named lemma before
constructing the maximal extension.

The source theorem `GL_MODPROVES_IFF_ITF_VALID` chooses the HOL Light type
`num` as an infinite carrier. Its Lean counterpart may use `Nat` and the
existing `Infinite Nat` instance; no separate translation of `num_INFINITE`
is needed.

#### S5: reflexive-Euclidean accessibility

S5 derives axiom 4 from T and 5. Its canonical relation requires the source
and target worlds to contain exactly the same boxed formulas. Reflexivity is
obtained as in T, while the equality of boxed fragments supports the
Euclidean property.

The accessibility context contains `¬q`, the boxed formulas already in `w`,
and the negated boxed formulas already in `w`. Its consistency proof combines
the derived axiom 4 with axiom 5 and is one of the longest proofs in the
source. It should be decomposed into named set lemmas for positive box
persistence, negative box persistence, subsentence closure, and consistency.
S5 should be attempted only after the K4/S4 persistence pattern and the KB/B
negative-information pattern are established.

### Recommended implementation order

A risk-directed Lean order, including current progress, is:

1. **K — completed:** the minimal end-to-end template required no change to
   the private boxed-context lifting lemma;
2. **T theory — completed:** reflexivity required only a direct set-based
   closure argument; translate its automation separately, as requested;
3. translate K4, establishing box persistence; review and expose the
   boxed-context lifting lemma when K4 first requires it outside the generic
   module;
4. translate S4 by combining the T and K4 patterns;
5. translate the core of D, keeping the alternative-axiom equivalences at the
   explicit dependency boundary described above;
6. translate KB and then B, developing the symmetric accessibility context;
7. translate GL, reusing the K4 context but adding Löb strictness;
8. translate S5 last, because it combines the greatest number of previously
   established techniques.

This differs from `make.ml` only to expose technical dependencies and reduce
risk; it does not assert new logical dependencies between the systems. If
maintaining source order is preferable while implementing, D may remain last,
provided its dependency on decision procedures is still separated.

Within every module, work should proceed through independently compilable
milestones:

1. axiom set and membership lemmas;
2. frame classes, characteristic-class equality, soundness, and consistency;
3. standard-frame/model aliases and the specialized truth lemma;
4. canonical relation and its relational properties;
5. the named extension context and accessibility lemma;
6. finite countermodel and completeness over `Set Form`;
7. completeness over an arbitrary infinite type;
8. documentation, root import, focused build, and full build.

### Risks and verification gates

The main risks are proof-theoretic rather than semantic:

- the stronger K4, GL, symmetric, and S5 extension contexts must be proved
  consistent without falling back to list encodings;
- subsentence closure for generated formulas such as `¬□E` must be stated
  explicitly enough for `EXTEND_MAXIMAL_SETCONSISTENT`;
- a helper generalized too early may acquire hypotheses tailored to one
  logic and become harder to reuse than the original proof;
- historical short names such as `REF` can collide conceptually with other
  identifiers, so all declarations should remain inside `HOLMS` and imports
  should avoid opening unnecessary namespaces;
- D's alternative axiomatisations must not force an accidental dependency on
  untranslated decision procedures;
- aliases preserving HOL Light theorem names must not conceal a change in
  quantification over world types or frame classes.

For each module, the relevant `lake build HOLMS/<Module>.lean` command must
pass without `sorry`, `admit`, or new axioms before the root import is changed.
After adding the import, run the full `lake build`. Before declaring a module
complete, compare its public declarations with the corresponding HOL Light
file and classify every omitted declaration as list-representation
infrastructure, meta-level tactic code, an exact generic specialization, or
an explicitly documented deferral such as the two D equivalence theorems.

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
