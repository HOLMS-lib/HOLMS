# Deep Embedding of Labelled Sequent Calculi

*Design notes for discussion — HOLMS (Lean 4)*

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
the proof-search experience provided by its shallow embedding.

These are design notes for a planned development, not documentation of an
implemented calculus. The [Lean work plan](../lean/FUTURE_WORK.md#labelled-sequent-calculi)
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

An explicit tree is particularly useful for external proof search, proof certificates, serialization, and proof transformations; inductive derivability is particularly convenient for mathematical reasoning.

## 6. Modularity across modal logics

The base system `G3K` may be extended with relational rules corresponding to frame properties such as reflexivity, transitivity, symmetry, seriality, and Euclideanness. The goal is to keep the underlying labelled syntax and proof-tree representation stable while varying the available rule schemas.

A calculus parameter might describe allowed named schemas, allowed concrete rule instances, or an inductively specified collection of rules. These options differ in how easily one can express side conditions, compare calculi, and construct executable rule checkers. Geometric rules introducing fresh labels require special care.

The intended scope includes all systems currently studied in HOLMS (K, T,
K4, S4, KB, B, S5, GL, D, and Grz), with room for further normal modal
logics. The design must also accommodate systems such as GL and Grz without
assuming that adding the usual geometric frame rules to `G3K` is sufficient.
The appropriate rules and their metatheory remain to be established for each
chosen calculus.

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

**Proposed direction:** keep both options open. Start with whichever makes the first metatheorems simpler, but avoid an API that prevents adding explicit certificates later.

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
