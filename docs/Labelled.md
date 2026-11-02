# Deep Embedding of Labelled Sequent Calculi

*Design notes and initial prototype — HOLMS (Lean 4)*

## 1. Motivation and scope

Labelled sequent calculi, as developed by Sara Negri and others, provide the
proof-theoretic framework for the proposed HOLMS extension. The aim is to
represent their syntax, inference rules, and derivations explicitly in Lean
and formalize their metatheory.

HOLMS already provides a deep embedding of propositional modal syntax,
Kripke semantics, and Hilbert-style proof systems with soundness and
completeness results. In HOL Light, it also contains a **shallow embedding
of labelled sequent calculi** in the form of automated modal proof tactics,
including `HOLMS_TAC` and the associated `HOLMS_RULE`. These implement proof
search through HOL Light goals and tactic operations: labelled sequents and
their inference steps are represented using the prover's existing logical
and proof infrastructure. See the
[automated theorem proving documentation](../README.md#automated-theorem-proving-and-countermodel-construction)
and the [generic decision-procedure infrastructure](../gen_decid.ml).

The proposed Lean extension introduces a **deep embedding of labelled
sequent calculi**. Labelled sequents, rule instances, and derivations would
be explicitly represented within Lean, so that derivations themselves can
be checked, transformed, and studied mathematically.

This representation is intended to support three complementary goals:

1. **Automated modal proof tactics in Lean**, corresponding to the tactics
   already available in HOL Light, with proof search producing certified
   derivations in the embedded calculus.
2. **External proof-search oracles** that generate derivations to be checked
   in Lean. An external tool would supply a proof certificate; acceptance
   would require a verified checker or reconstruction of a Lean proof, so
   correctness would not depend on trusting the external search procedure.
3. **Proof theory formalized in Lean**, including the metatheoretic results
   of Negri and others for the chosen calculi, such as soundness,
   completeness, structural admissibility, and cut elimination.

For now, implementation of this deep embedding is planned **in Lean 4 only**;
no corresponding HOL Light implementation is currently planned. This is new
work beyond the translation of the existing HOL Light library and builds on
the proof-search experience provided by its shallow embedding. Nevertheless,
the design should consider a possible future HOL Light port; the portability
discussion below is a design consideration, not a commitment to implement
that port now.

An initial prototype is implemented in
[`HOLMS.Labelled`](../lean/HOLMS/Labelled.lean); its
[implementation note](../lean/translation/Labelled.md) records the precise
scope. It provides raw trees, a common validity predicate, reusable rule
families, and generic certificate lemmas. The companion module
[`HOLMS.LabelledSoundness`](../lean/HOLMS/LabelledSoundness.lean), documented
in its [implementation note](../lean/translation/LabelledSoundness.md), proves
Kripke soundness for every primitive rule and provides compositional
soundness. Individual systems are isolated in
[`HOLMS.LabelledK`](../lean/HOLMS/LabelledK.lean),
[`HOLMS.LabelledT`](../lean/HOLMS/LabelledT.lean), and
[`HOLMS.LabelledB`](../lean/HOLMS/LabelledB.lean), each with its own
composition, certificates, soundness theorems, and
[implementation note](../lean/translation/README.md). Completeness and
structural metatheory remain future work. The sketches below are design
alternatives, not literal copies of the implemented API. The
[Lean work plan](../lean/FUTURE_WORK.md#labelled-sequent-calculi)
records its place in the project; the [documentation index](README.md)
links to the existing mathematical chapters.

The initial objective is to settle the mathematical representation of labelled sequents, inference rules, and derivations. The Lean 4 sketches below are illustrative rather than compilable declarations: `Form` denotes the existing `HOLMS.Form` type, and namespace/import details remain to be determined.

## 2. Basic syntactic objects

A labelled formula `x : A` associates a modal formula `A` with a label `x`. A relational atom `x R y` records an accessibility assertion. Both are **syntactic** objects: a label is not itself a Kripke world, although a semantic interpretation assigns a world to each label.

```lean
abbrev Label := Nat

structure LFormula where
  label   : Label
  formula : Form
  deriving DecidableEq

structure RelAtom where
  source : Label
  target : Label
  deriving DecidableEq
```

Natural-number labels provide a simple countable supply of fresh names; this is a design convenience rather than a mathematical requirement.

Keeping relational atoms separate from labelled formulas makes the difference between logical rules and frame-condition rules explicit.

## 3. Labelled sequents and contexts

We write a labelled sequent as

$$
\mathcal R\ ;\ \Gamma\ \Rightarrow\ \Delta,
$$

where $\mathcal R$ is a context of relational atoms, and $\Gamma$ and $\Delta$ are contexts of labelled formulas. This separates components that are often written together on the left of a sequent in paper presentations.

```lean
structure Sequent where
  relations : Multiset RelAtom
  left      : Multiset LFormula
  right     : Multiset LFormula
```

`Multiset` ignores order but preserves multiplicity, which is relevant when contraction is studied as an admissible rule. `Finset` identifies repeated occurrences; `List` retains ordering and may simplify proof-certificate generation. The choice should be evaluated against both metatheory and computation.

## 4. Representative modal rules

For the box modality, the two characteristic rules can be presented schematically as follows (commas denote multiset addition):

**BoxL**

$$
\frac{\mathcal R,xRy\ ;\ \Gamma,x:\Box A,y:A\Rightarrow\Delta}
     {\mathcal R,xRy\ ;\ \Gamma,x:\Box A\Rightarrow\Delta}
$$

**BoxR**

$$
\frac{\mathcal R,xRy\ ;\ \Gamma\Rightarrow\Delta,y:A}
     {\mathcal R\ ;\ \Gamma\Rightarrow\Delta,x:\Box A}
\quad (y\text{ fresh in the conclusion}).
$$

The eigenlabel condition in `BoxR` requires that `y` not occur anywhere in the conclusion, including its relational context. `BoxL` instead uses a relational atom already present in the conclusion. These examples also show why a representation of rule instances needs access to the full premise and conclusion sequents.

## 5. Two representations of derivability

**Option A: inductive derivability.** Declare a judgment `Derivable C S : Prop` whose constructors correspond to the inference rules of calculus `C`.

```lean
-- Schematic only: the rule constructors and the representation
-- of C must still be chosen.
inductive Derivable (C : Calculus) : Sequent → Prop where
  -- initial sequents and inference rules
```

This formulation directly supports induction on derivations and is a natural starting point for proof-theoretic metatheorems.

**Option B: explicit proof trees.** Represent the finite tree independently of whether its rule applications are correct.

```lean
inductive Derivation where
  | node : Sequent → Rule → List Derivation → Derivation

def conclusion : Derivation → Sequent :=
  -- Return the sequent stored at the root.
  sorry

-- Validity is checked separately from the tree datatype.
def Valid (C : Calculus) (d : Derivation) : Prop :=
  sorry
```

Here `sorry` marks a deliberately omitted definition, not an implementation proposal. A tree can have the wrong number of premises, an incorrectly instantiated rule, or an eigenlabel violating freshness. The validity predicate must reject all such trees.

The approaches are complementary. A valuable target theorem is

$$
\operatorname{Derivable}_C(S)
\quad\Longleftrightarrow\quad
\exists d,\ \operatorname{Valid}_C(d)\ \land\
\operatorname{conclusion}(d)=S.
$$

### 5.1. Explicit derivations for proof theory

Option B is useful for proof theory as well as for certificates. Explicit
trees support recursive definitions of height, size, cut rank, and label
support, together with transformations of derivations. This permits direct
statements about height-preserving admissibility, cut elimination as a
transformation, and bounds on the size or height of the resulting proof.

Option A also supports induction on derivations and proofs of soundness,
completeness, structural admissibility, and cut elimination. However, Lean's
`Prop` is proof-irrelevant, and elimination from inductive propositions into
data types is restricted. In general, one cannot define a function computing
the height or a transformed tree by inspecting a proof of `Derivable C S`.
See the [Lean reference on propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/).
An indexed predicate such as `DerivableWithin C h S : Prop` can still express
derivability within height `h` and support quantitative metatheorems.

With Option B, for example, a cut-elimination function on trees would need a
theorem stating that valid inputs produce valid, cut-free outputs with the
same conclusion. If the transformation is only defined on valid trees, its
interface may take a validity proof as an additional argument. Neither the
existence of the function nor its termination follows merely from choosing
explicit trees; these remain substantive proof obligations.

### 5.2. An alternative: intrinsically valid derivations in `Type`

Explicit derivations need not be raw trees. Another possibility is an
inductive family `Derivation (C : Calculus) : Sequent → Type`, with one
constructor per rule and validity conditions, including freshness, built
into the constructors. This combines induction and computation on proof
objects with a guarantee that each inhabitant represents a valid derivation
of its indexed conclusion. Propositional derivability can then be expressed
as `Nonempty (Derivation C S)`.

This representation avoids repeatedly establishing validity of raw trees,
but introduces dependent indices into proof transformations. Raw trees with
a separate validity predicate and intrinsically valid derivations are two
different ways to obtain explicit proof objects; their relative convenience
should be tested on renaming and a structural admissibility argument.

### 5.3. Possible translation to HOL Light

For maintaining parallel Lean and HOL Light developments, **raw trees with a
separate validity predicate are a promising common representation**. A tree
datatype, recursive operations on it, and a predicate `Valid C d` can be
expressed in HOL Light's simple type theory. HOL Light supports
[inductive datatypes](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/define_type.html)
and [inductively defined relations](https://hol-light.github.io/references/HTML/new_inductive_definition.html).
The dependent family `Derivation C S : Type` has no direct counterpart as a
type indexed by the term `S` in HOL Light; its information would normally be
expressed using an ordinary datatype and predicates instead.

Keeping validity separate would therefore allow both implementations to
share the mathematical shape of their definitions and theorems: operations
act on trees, and preservation theorems assert validity, preservation of the
conclusion, and any height or size bounds under explicit hypotheses. The
predicate must express both local rule correctness and validity of all
subderivations. Merely defining an inductive derivability predicate, as in
Option A, is also portable, but does not by itself provide explicit proof
objects for these operations.

This suggests using Option B as the common mathematical interface if
portability is a priority. Lean may additionally package a tree together
with its validity proof in a subtype, or provide an indexed interface, while
retaining the raw representation for external certificates and a possible
HOL Light port. Such wrappers need not dictate the representation in HOL
Light. Portability still requires compatible choices of contexts, rule
instances, and freshness conditions; it does not imply automatic translation
of Lean definitions or proofs.

## 6. Modularity across modal logics

The base system `G3K` may be extended with relational rules corresponding to frame properties such as reflexivity, transitivity, symmetry, seriality, and Euclideanness. The goal is to keep the underlying labelled syntax and proof-tree representation stable while varying the available rule schemas.

A calculus parameter might describe allowed named schemas, allowed concrete rule instances, or an inductively specified collection of rules. These options differ in how easily one can express side conditions, compare calculi, and construct executable rule checkers. Geometric rules introducing fresh labels require special care.

The intended scope includes all systems currently studied in HOLMS (K, T,
K4, S4, KB, B, S5, GL, D, and Grz), with room for further normal modal
logics. The design must also accommodate systems such as GL and Grz without
assuming that adding the usual geometric frame rules to `G3K` is sufficient.
The appropriate rules and their metatheory remain to be established for each
chosen calculus.

### 6.1. A common tree type and parameterized validity

Raw proof trees offer a further modularity advantage: the same datatype and
the same tree can be considered in different calculi. A tree valid in one
calculus need not be valid in another. The recursive definition of validity
can remain fixed; only the predicate describing allowed rule instances
changes.

For a fixed representation of rule identifiers and parameters, let

```lean
-- Schematic type of a calculus's local rule-instance relation.
Step : Rule → List Sequent → Sequent → Prop
```

Here `Step r premises conclusion` states that this particular inference is
allowed, including its arity, formula and context requirements, and side
conditions such as freshness. For a node storing conclusion `S`, rule data
`r`, and children `ds`, define validity schematically by

$$
\operatorname{Valid}(C,\operatorname{node}(S,r,ds))
\iff C(r,\operatorname{map}(\operatorname{conclusion},ds),S)
\land \forall d\in ds,\ \operatorname{Valid}(C,d).
$$

Initial sequents are zero-premise rule instances: a leaf is valid only if
its stored rule and conclusion satisfy `C r [] S`. There is no separate
blanket acceptance of leaves. This definition inspects the tree structure,
so height, size, and other purely syntactic operations are independent of
the selected calculus.

### 6.2. Composition at the level of inference steps

Define each rule family separately: for example, `IdentityStep`,
`BoxRightStep`, `ReflStep`, `SymmStep`, `TransStep`, or `SerialStep`, all with the common
schema interface. Associate each schema with its string name using a singleton
calculus, and combine calculi pointwise. The current prototype builds
`propositionalCalculus` from the fifteen propositional singleton calculi and
then builds `standardCalculus` by adding box-left and box-right. Each modal
system is placed in its own Lean module: K selects `standardCalculus`, T forms
`K ∪ reflCalculus`, and B forms `T ∪ symmCalculus`. A proposed S4 calculus
could use
`standardCalculus ∪ reflCalculus ∪ transCalculus`, while T uses
`standardCalculus ∪ reflCalculus`. Here “B” follows the existing HOLMS convention:
`B_AX` contains both the T and B schemas and therefore corresponds to
reflexive symmetric frames; KB will denote the merely symmetric system. The
additional rules and adequacy results for the other systems still need to be
specified and proved.

Composition must take place at the step level, not by disjoining validity
of whole trees. In general, `Valid (C₁ ∪ C₂) d` is not equivalent to
`Valid C₁ d ∨ Valid C₂ d`: a derivation may use rules from both components
at different nodes. By contrast, pointwise inclusion `C₁ ⊆ C₂` should give
the generic theorem `Valid C₁ d → Valid C₂ d`, by induction on the tree.
Thus extending a calculus can preserve the very same proof object.

The rule-data interface must itself allow extensions rather than use a closed
enumeration that must be redesigned for each new logic. The current prototype
uses a string name and a flat list of formula/label arguments. New families
therefore add predicates recognizing new names and argument patterns without
changing the rule or tree datatypes. Keeping this interface fixed gives
literally the same tree type across calculi.

### 6.3. Shared metatheory and its limits

Generic soundness is organized around a local soundness property for `C`:
each allowed step preserves semantic validity from its premises to its
conclusion. Soundness of a union then follows from the corresponding results
for its components. This organization is implemented for the current K, T, and B
calculi. Similarly, future generic renaming results can assume stability of
the step relation under the appropriate label transformations.

A label assignment maps syntactic labels to designated worlds of a Kripke
frame. It interprets `x : A` by evaluating `A` at the world assigned to `x`,
and interprets `x R y` by the accessibility relation of the frame. A sequent
has a counterexample when all its relational atoms and antecedent formulas
are true while every succedent formula is false. Semantic validity is the
absence of such a counterexample for every valuation and frame-respecting
label assignment.

All propositional rules and both box rules are sound on arbitrary Kripke
frames. The proof of box-right is the essential eigenlabel argument: if
`x : □A` is false, choose a designated successor where `A` is false and
assign that world to the fresh label. Freshness guarantees that changing this
one label does not change any old context entry. The reflexivity rule is sound
when the frame relation is reflexive on its designated worlds, because its
auxiliary self-edge is then true. The symmetry rule keeps a forward edge in
the conclusion and adds its reverse in the premise; symmetry of the frame
makes that reverse edge true.

At the calculus level, the empty calculus and sound singleton calculi are
sound, and pointwise unions preserve soundness. It follows compositionally
that K is sound on every Kripke frame, T is sound on every reflexive frame,
and B is sound on every reflexive symmetric frame. An induction over a valid
proof tree then proves semantic validity of its root sequent; the existential
definition of derivability gives the corresponding theorem for derivable
sequents.

Cut elimination and structural admissibility do not follow merely from
composing rule predicates: interactions between rule families require
additional hypotheses and proofs. A local step interface directly covers
finitary rules whose side conditions depend on their recorded data and
premise/conclusion sequents. Calculi with global proof conditions would
require a richer validity specification. The common tree representation
therefore supports modularity without assuming a uniform metatheory for all
normal modal logics.

### 6.4. Lean classes as an interface to rule availability

Lean type classes can organize the hypotheses of generic results without
determining the underlying tree representation. A class is a record whose
instances Lean can search for automatically; its fields may contain data or
proofs. A parameter `[HasRefl C]` requests an instance certifying that the
calculus `C` includes the reflexivity rule family. Each instance must supply
the required proof: instance synthesis does not introduce an assumption or
prove arbitrary inclusions on its own. See the
[Lean introduction to type classes](https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/).

A possible design separates the explicit calculus data from classes
certifying inclusion of rule families:

```lean
-- Schematic design only; Rule, Sequent, and ReflStep are not defined here.
def Calculus := String → List RuleArgument → List Sequent → Sequent → Prop

class HasRefl (C : Calculus) : Prop where
  included : reflCalculus.Included C
```

The implemented interface also has `HasSymm C`, independently certifying
inclusion of `symmCalculus`. Consequently B receives `HasCore`, `HasRefl`, and
`HasSymm` instances from its explicit definition as `T ∪ symmCalculus`.

The parameter `C`, used directly as a step relation in Sections 6.1–6.3,
is itself the composable map. `C.step` applies it to the name and
arguments stored in a raw rule, so `Valid C d` still uses the same recursive
definition.

The prototype separates `HasPropositionalCore C`, `HasBoxLeft C`, and
`HasBoxRight C`. `HasCore C` bundles these standard capabilities for ordinary
extensions, while `HasRefl C` and `HasSymm C` record reflexivity and symmetry
independently. Future classes could record `HasTrans C` and `HasSerial C` as well. For S4,
instances of `HasCore S4`, `HasRefl S4`, and `HasTrans S4` would be proved
from its explicit definition.

Generic lemmas should request only the capabilities they use. For example,
the prototype's T-axiom certificate requires `HasPropositionalCore C`,
`HasBoxLeft C`, and `HasRefl C`, but not `HasBoxRight C`. This permits reuse
in a calculus that omits or replaces standard box-right. Initial sequents
and purely propositional certificates require only the propositional
capability. Instances can also propagate rule
availability along suitable calculus extensions, provided the necessary
inclusions have been proved and the search is organized to avoid loops and
unnecessary competing candidates.

These classes certify map inclusion, and therefore availability of every rule
instance registered in the relevant map. This
is stronger than admissibility, which may require replacing a rule
application by an entire derivation. Admissibility and height-preserving
admissibility should have distinct specifications; they must not silently
be substituted for primitive rule availability.

The open rule-data structure records what can be represented, not what each
calculus must permit. Neither `Valid C d` nor the tree datatype requires a
full-core instance. A calculus's explicit step relation can therefore filter
out old rules and admit replacements while preserving the raw tree
representation. A separate predicate asserting that a tree uses only selected
rules can be useful for metatheory, but is not required in addition
to validity in an appropriately restricted calculus. Changing the rules
does not automatically preserve semantic or proof-theoretic results.

The composition of calculi should remain explicit. Registering multiple
instances that each provide a different `step` relation for the same
calculus does not cause Lean to union those relations: instance synthesis
searches for a suitable instance rather than combining the fields of all
available instances. See the
[instance synthesis reference](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/).
Use pointwise union to define the calculus, and classes to certify its rule
inclusions or metatheoretic properties. Availability of rule families alone
does not establish soundness or cut elimination; the current K/T/B soundness
theorems discharge the separate semantic obligations for their components.

This keeps the mathematical core portable to HOL Light: trees, step
relations, and validity remain explicit, while class witnesses translate
into ordinary hypotheses or inclusion theorems. Classes are a Lean
interface convenience, not a required feature of the object calculus.
The implemented experiments now cover the core, reflexivity, and symmetry
families, including an explicit seven-node certificate for `A → □◇A` in B.
Transitivity and the remaining relational families are later extensions of
the same interface.

## 7. Labels, renaming, and structural metatheory

Define the finite set of labels occurring in a relational atom, a labelled formula, a sequent, and a derivation. Freshness can then be expressed using non-membership in this support.

For instance, if `labels : Sequent → Finset Label`, the side condition of `BoxR` has the schematic form:

```lean
y ∉ labels conclusionSequent
```

Uniform substitution or renaming of labels should also be defined early. These operations underpin eigenlabel arguments, invariance under renaming, and proofs about weakening, contraction, and cut. Renaming a derivation is subtler than mapping its node labels: a renaming must preserve the side conditions of all rule instances, possibly after choosing fresh eigenlabels.

## 8. Questions for the design discussion

The following decisions are interconnected. Each question concerns not only convenience in Lean 4 but also which mathematical results HOLMS should make easy to state and prove.

### 8.1. What should the first calculus include?

**Choice:** implement only `G3K`, or include some frame rules from the outset.

Starting with `G3K` isolates the propositional rules and the essential modal mechanisms, especially the eigenlabel condition of `BoxR`. It provides a small test case for induction, rule-instance validation, and the correspondence with Kripke semantics. However, designing exclusively for `G3K` risks hard-coding assumptions that make geometric extensions awkward.

**Proposed direction:** prove initial results for `G3K`, but test the *interfaces* against at least one rule with a nontrivial relational premise (such as transitivity) and one with a fresh label (such as a seriality rule). This is a design test, not necessarily a commitment to formalize those extensions immediately.

### 8.2. Is derivability a proposition, a proof object, or both?

An inductive predicate `Derivable C S : Prop` expresses the mathematical judgment directly. In Lean, proofs of propositions are not normally treated as persistent, inspectable certificate data. An explicit `Derivation` datatype, by contrast, is an ordinary inductive data structure that can be traversed, transformed, serialized, and checked.

These representations answer different questions:

- **Inductive derivability:** Can we prove that a sequent is derivable, and reason by induction on a derivation?
- **Explicit tree:** Can we store a concrete derivation, replay it, inspect its rule applications, or receive it from a proof-search procedure?
- **Validity predicate:** Does a given raw tree satisfy the rules and side conditions of a chosen calculus?

A raw tree should not be confused with a certified proof. Its constructor guarantees only the shape of a tree; `Valid C d` guarantees that every node is a legitimate rule application. If both representations are implemented, their equivalence should be proved, rather than assumed.

**Proposed direction:** prioritize explicit derivations for proof theory and
certificates. Evaluate raw trees with separate validity as the common
interface for a possible HOL Light port, and compare an intrinsically valid
Lean interface on small examples. Keep propositional derivability available
as an abstract judgment, with a proved correspondence to the explicit
representation. Section 5 discusses the tradeoffs; no final representation
is fixed yet.

### 8.3. Which data structure should represent contexts?

The principal candidates are `List`, `Multiset`, and `Finset`.

| Representation | Advantage | Main cost |
| --- | --- | --- |
| `List` | Simple recursion and executable manipulation | Order is artificial; exchange needs attention |
| `Multiset` | Matches unordered contexts while retaining occurrences | Some algorithms and proofs require quotient-aware operations |
| `Finset` | Convenient membership and finite support | Duplicate occurrences disappear, changing how contraction is represented |

This choice affects the *statement* of structural results. With `Finset`, contraction is effectively built into context equality; with `Multiset`, removing duplicate occurrences is a genuine operation. With `List`, one must either explicitly account for permutations or establish an exchange-invariance result.

**Proposed direction:** use `Multiset` as the mathematical baseline; assess whether a list-based executable representation with a proved correspondence would be useful for proof search. Relational and formula contexts need not necessarily make the same choice.

### 8.4. What is a rule, and what is a rule instance?

A name such as `BoxR` identifies a **rule schema**. A concrete application additionally specifies the principal formula, relevant labels, contexts, premises, conclusion, and any side conditions. These must not be conflated.

One design uses a small datatype of rule names and a relation:

```lean
-- Schematic interface, not a completed definition.
RuleInstance : Calculus → Rule → List Sequent → Sequent → Prop
```

Another design gives rule-specific constructors carrying parameters, for example the principal formula and eigenlabel. This can make rule checking and proof transformations more explicit, at the cost of a larger rule datatype and more dependencies on the selected calculus.

A third possibility is to define derivability directly through inductive constructors, without first defining a standalone `Rule` datatype.

**Discussion point:** should a proof node record only the rule name and surrounding sequents, leaving parameters to be inferred, or should it record the full rule-instance data? The answer may differ for proof certificates and for abstract metatheory.

### 8.5. How should eigenlabels and freshness be handled?

The `BoxR` rule has a side condition: its eigenlabel must be absent from the conclusion. Such conditions are not optional implementation checks; they are part of the inference rule itself.

There are at least three approaches:

1. Store an explicit eigenlabel in the rule application and check freshness.
2. Use an inductive constructor with freshness as a premise.
3. Introduce a more abstract treatment of labels and binding/renaming.

For a first implementation, explicit natural-number labels and a finite-support predicate are likely sufficient. Nevertheless, structural proofs may require replacing an eigenlabel by a fresh one before applying a substitution. In particular, an arbitrary non-injective substitution can destroy freshness, so preservation of derivability cannot be established by naively mapping every label through the same function without considering eigenlabels.

**Proposed direction:** represent eigenlabels explicitly, centralize support and freshness operations, and prove suitable renaming lemmas early. Distinguish unrestricted substitution on *syntax* from admissible transformations of *derivations*.

### 8.6. How should a calculus be parameterized?

A calculus can be represented as a collection of **named rule schemas**, or extensionally as a predicate on concrete inference steps:

```lean
-- A possible extensional interface.
abbrev Step := List Sequent → Sequent → Prop
```

The extensional approach is flexible: adding a rule amounts to enlarging the collection of allowed steps. It also makes monotonicity statements natural: if every step of calculus `C₁` is allowed in `C₂`, then derivability in `C₁` should imply derivability in `C₂`.

Named schemas provide more information about the proof itself and support human-readable certificates, rule-specific transformations, and executable checking. A predicate on arbitrary steps alone may lose the name and parameters of the applied rule.

**Proposed direction:** distinguish a mathematical *rule-instance relation* from an optional *rule identifier* used by explicit proof trees. This can support both modular metatheory and inspectable certificates.

Section 6 gives a candidate interface that retains rule data, defines tree
validity uniformly, and composes calculi by union of their local step
relations. It also distinguishes extension of a rule predicate from extension
of the datatype used to record rule instances.

### 8.7. What must be executable?

Lean 4 distinguishes between a mathematical specification in `Prop` and executable data or procedures. A `Valid C d : Prop` definition is sufficient for proving correctness properties, but an external proof-search tool may need a computable checker, such as a Boolean function or a decidable validity test.

Executable checking requires more than a decidable equality on labels and formulas: the chosen representation of rule schemas and side conditions must also support effective checking. A generic, unrestricted predicate describing a calculus need not be decidable.

**Discussion point:** is the initial goal solely metatheory, or should HOLMS also accept independently generated proof certificates? If certificates are a near-term goal, decidable rule checking should influence the architecture now.

### 8.8. Which results should validate the design?

A datatype is useful only if it supports the intended theorems without excessive bookkeeping. Suggested early tests are:

- Correct formation of initial sequents and the propositional rules.
- A faithful formulation of `BoxL` and `BoxR`, including freshness.
- Existence of fresh labels for finite sequents.
- Invariance of derivability under suitable label renaming.
- A first structural admissibility result (for example, weakening).
- If both proof representations exist, agreement between `Derivable` and valid explicit trees.
- A small extension by a relational frame rule without changing the core syntax.

These tests should be used to revise the representation before expanding to a large family of modal systems.

## 9. Suggested first milestone

Implement labelled syntax and sequents in Lean on top of the existing `HOLMS.Form` type. Specify the propositional G3 rules and the two box rules. Define finite label support and freshness. Establish basic renaming properties and one structural admissibility theorem. If explicit proof trees are introduced, formulate and prove their correspondence with inductive derivability.

The first milestone should prioritize **clarity of the mathematical interfaces** over an optimized proof-search implementation. Executable certificates and additional frame conditions can follow once the core representation has been tested.

## Reference points

- Sara Negri, “Proof Analysis in Modal Logic,” *Journal of Philosophical Logic* **34** (2005), 507–544. The exact conventions and rule formulations should be checked against the chosen presentation before formalizing them.
- HOLMS project: <https://holms-lib.github.io/>
