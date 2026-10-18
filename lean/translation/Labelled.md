# `HOLMS.Labelled`

Lean module: [`../HOLMS/Labelled.lean`](../HOLMS/Labelled.lean)

This is a new Lean development, not a translation of an existing HOL Light
deep embedding. The shallow automated procedures in
[`gen_decid.ml`](../../gen_decid.ml), [`k_decid.ml`](../../k_decid.ml), and
[`t_decid.ml`](../../t_decid.ml) provide context, not declaration-by-declaration
counterparts. The [design discussion](../../docs/Labelled.md) describes the
longer-term goals. Shared conventions are in
[`CONVENTIONS.md`](../CONVENTIONS.md).

## Implemented prototype

All declarations are in `HOLMS.Labelled`. The only project dependency is
`HOLMS.Modal`; formulas are the existing `HOLMS.Form`.

- Labels are natural numbers. `LFormula` and `RelAtom` distinguish labelled
  formulas from syntactic accessibility assertions.
- `Sequent` has three multiset contexts. Order is ignored, occurrences are
  retained, and no structural admissibility result is built into validity.
- `Sequent.labels` collects labels in every context. `Sequent.fresh` gives a
  proved fresh label; box-right checks freshness in the entire conclusion.
- `CoreRule` records rule names and their principal formulas/labels.
  `CoreStep` gives their precise local instances, including premise arity.
- The classical two-sided core covers every `Form` constructor: initial
  sequents, truth/falsity, negation, conjunction, disjunction, implication,
  biconditional, and box. Identity is generalized to all formulas. The
  context-sharing implication-left rule does not retain its principal
  formula in the premises. This is a prototype classical calculus, not a
  claim that all rules reproduce a particular G3 presentation verbatim.
- Box-left retains the principal box and the chosen edge. Box-right adds a
  fresh target and an edge in its premise. Reflexivity removes a self-edge
  from the premise to the conclusion.
- `Rule E` distinguishes core tags from extension payloads. `Calculus E`
  contains the local step relation; `Calculus.withCore` combines the shared
  core with an independent extension relation. `Calculus.union` composes
  local relations pointwise, with inclusion lemmas for both components.
- `K` and `T` both use extension payload type `Label`, interpreted as the
  label of a reflexivity step. K rejects all extension-tagged nodes; T
  admits exactly `ReflStep` there. Thus the two calculi have literally the
  same raw certificate type. More general extension languages can use a
  different payload type, with an explicit tree embedding where needed.
- `HasPropositionalCore`, `HasBoxLeft`, and `HasBoxRight` separately certify
  primitive inclusion of the propositional family and the two standard box
  rules. `CoreRule.IsPropositional` selects every core tag except the box
  rules; it does not exclude boxed subformulas from propositional rules.
  `HasCore` bundles these three capabilities and exposes them to instance
  search. The theorem `HasCore.admitted` retains the full-core inclusion
  interface, and `withCore`, K, and T still provide the bundle.
  `HasRefl` separately certifies primitive reflexivity inclusion.
  `HasRefl` is currently specialized to the reflexivity payload interface;
  a larger extension language will need a corresponding injection or class.
- `ProofTree E` stores a conclusion, rule payload, and ordered child list.
  Its height and node count are functions on raw data.
- `Valid` is a single inductive predicate parameterized by the calculus.
  Its node constructor requires a permitted local step and validity of
  every child. The inversion theorem `valid_node_iff` exposes that recursive
  characterization; no arbitrary leaf is accepted.
- `Derivable` means existence of a valid raw tree with the specified root;
  it is not a second independent inductive derivability relation.

## Verified certificate examples and generic results

The module proves validity monotonicity under local step inclusion and
specializes it to K-to-T inclusion, preserving the same raw tree. Existential
derivability is monotone as well.
`identity_valid` and the modal certificate lemmas use rule-availability
classes rather than hard-coding a system name.

Certificate lemmas require only the appropriate capability groups:

| Lemma | Required capabilities |
|---|---|
| `identity_valid`, `conjunctionTree_valid` | `HasPropositionalCore` |
| `boxUseTree_valid` | `HasPropositionalCore`, `HasBoxLeft` |
| `boxedIdentityTree_valid` | `HasPropositionalCore`, `HasBoxLeft`, `HasBoxRight` |
| `reflexiveBoxTree_valid`, `tAxiomTree_valid` | `HasPropositionalCore`, `HasBoxLeft`, `HasRefl` |

The tree datatype and validity definition do not impose `HasCore`. A
calculus can omit or replace selected core rules through its explicit
`step` relation; `withCore` remains a convenience constructor for the usual
full-core extensions. Finer propositional fragments can likewise be
specified by `step`, but need their own weaker inclusion hypotheses rather
than `HasPropositionalCore`.

`boxedIdentityTree` uses box-right, box-left, and identity. Its validity
requires distinct source/eigenlabels, and the same concrete tree is accepted
in K and T. `tAxiomTree` uses implication-right, reflexivity, box-left, and
identity to derive the labelled formula `□A → A` in T. The module proves
that this particular tree is invalid in K. This is rejection of a certificate,
not a theorem that the formula has no other K derivation.

Further negative checks show that a box-right leaf is invalid in K and that
any correct core box-right instance has an eigenlabel distinct from its
source. `conjunctionTree` verifies a binary conjunction-right step with both
identity leaves. Examples also check the concrete height and size of the T
tree.

A private regression calculus removes box-right from T while retaining
propositional rules, box-left, and reflexivity. Lean verifies the
propositional and T-axiom certificates in this calculus and rejects the
boxed-identity certificate because its root uses the missing rule. This
checks that the granular interfaces work without a full-core instance.

## Scope and remaining obligations

Validity is currently a mathematical predicate, not an executable certificate
checker; no `Decidable` instance or Boolean validation algorithm is supplied.
There is no new proof-search tactic. No semantic soundness, completeness,
Hilbert correspondence, general identity expansion, weakening, contraction,
renaming preservation, or cut-elimination result is claimed. In particular,
acceptance by `Valid` only certifies adherence to the specified calculus;
semantic adequacy of that calculus remains a separate proof obligation.

Raw syntax and separate validity were chosen to keep a possible future HOL
Light deep embedding straightforward. No such port is implemented or promised.

## Verification

From `lean/`, build this module with `lake build HOLMS.Labelled`, then use
`lake build` to verify the public aggregate. The examples are kernel-checked
proofs and contain no proof placeholders or added axioms.
