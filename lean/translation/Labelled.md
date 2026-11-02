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

- Labels are natural numbers (`Nat`), chosen to simplify both computation and
  proof of freshness: one more than the maximum label in a sequent is fresh.
  `LFormula` and `RelAtom` distinguish labelled formulas from syntactic
  accessibility assertions.
- `Sequent` has three multiset contexts. Order is ignored, occurrences are
  retained, and no structural admissibility result is built into validity.
- `Sequent.labels` collects labels in every context. `Sequent.fresh` gives a
  proved fresh label by adding one to the maximum label in the support;
  box-right checks freshness in the entire conclusion.
- `Rule` is the single open rule-data format used by proof trees. Each
  rule has a string name and a flat list of formula/label arguments. Separate
  `*Step` relations give the precise local instances, including premise
  arity and side conditions.
- The classical two-sided core covers every `Form` constructor: initial
  sequents, truth/falsity, negation, conjunction, disjunction, implication,
  biconditional, and box. Identity is generalized to all formulas. The
  context-sharing implication-left rule does not retain its principal
  formula in the premises. This is a prototype classical calculus, not a
  claim that all rules reproduce a particular G3 presentation verbatim.
- Box-left retains the principal box and the chosen edge. Box-right adds a
  fresh target and an edge in its premise. Reflexivity removes a self-edge
  from the premise to the conclusion. Symmetry removes an auxiliary reverse
  edge while retaining the forward edge.
- `Calculus` is directly the function from rule names to schemas;
  `Calculus.step` passes a raw rule's flat arguments to the selected schema.
  `Calculus.union` composes calculi pointwise.
- This module deliberately does not define an individual modal system.
  [`HOLMS.LabelledK`](../HOLMS/LabelledK.lean),
  [`HOLMS.LabelledT`](../HOLMS/LabelledT.lean), and
  [`HOLMS.LabelledB`](../HOLMS/LabelledB.lean) compose the reusable singleton
  calculi into systems. Every system still uses literally the same raw
  certificate type and no tree embedding is required.
- `HasPropositionalCore`, `HasBoxLeft`, and `HasBoxRight` separately certify
  inclusion for the propositional family and the two standard box calculi.
  `HasCore` certifies inclusion of `standardCalculus` and supplies the granular
  capabilities by transitivity. `HasRefl` and `HasSymm` independently certify
  inclusion of `reflCalculus` and `symmCalculus`.
- `ProofTree` stores a conclusion, a `Rule`, and an ordered child list.
  It has no extension type parameter. Its height and node count are functions
  on raw data.
- `Valid` is a single inductive predicate parameterized by the calculus.
  Its node constructor requires a permitted local step and validity of
  every child. The inversion theorem `valid_node_iff` exposes that recursive
  characterization; no arbitrary leaf is accepted.
- `Derivable` means existence of a valid raw tree with the specified root;
  it is not a second independent inductive derivability relation.

## Flat named rule infrastructure

`HOLMS.Labelled` supplies one rule representation and one compositional
calculus interface used by `ProofTree` and `Valid`:

- `RuleArgument` has exactly two constructors:
  `formula : Form → RuleArgument` and `label : Label → RuleArgument`.
  It is no longer recursive, so Lean derives `DecidableEq` and `Repr`
  directly.
- The previous `RuleArgument.View` abstraction and all generic
  encoding/decoding, coercion, list, pair, `LFormula`, and `RelAtom` instances
  have been removed. Rule arguments are written explicitly and their meaning
  is determined by the step relation that accepts them.
- `Rule` has fields `name : String` and
  `arguments : List RuleArgument`. The list supplies ordering and arity at the
  rule level without adding a recursive list constructor to `RuleArgument`.
  The structure itself remains open: an arbitrary string and argument list is
  raw data until a step relation recognizes it.
- Every one of the 17 core step relations, `ReflStep`, and `SymmStep` has the
  uniform type
  `List RuleArgument → List Sequent → Sequent → Prop`. Its constructor fixes
  the exact flat argument pattern but does not repeat the string name.
- Only principal rule data occurs in `Rule.arguments`. Relational, antecedent,
  and succedent contexts are already present in the premises and conclusion,
  so they are not duplicated in the rule value. This removes list
  presentations of multisets, nested encodings, and dependence on the order
  chosen to enumerate a context.
- `RuleSchema` is the common type of these relations. `Calculus` is the map
  from a string to a `RuleSchema`; `empty`, `singleton`, `union`, and `unions`
  supply its compositional API. If two calculi contain the same name, their schemas are
  alternatives combined by disjunction rather than one silently replacing
  the other.
- Each primitive relation has a singleton calculus such as `identityCalculus`,
  `boxRightCalculus`, `reflCalculus`, or `symmCalculus`. `propositionalCalculus` is the
  composition of fifteen singleton calculi, and `standardCalculus` composes it
  with the two box calculi. There are no `PropositionalStep` or `StandardStep`
  datatypes.
- `Calculus.Included` is extensional inclusion of accepted instances. Its
  reflexivity, transitivity, component-to-union, and member-to-`unions`
  theorems drive calculus inclusion and the capability classes.
- `IdentityStep.exists_arguments` and `FalsumLeftStep.exists_arguments` show
  that the corresponding sequents determine accepted flat argument lists for
  arbitrary multiset contexts. Negative examples check rejection of missing
  or wrongly typed arguments.

For example, within `HOLMS.Labelled`, an identity rule is ordinary flat
data:

```lean
(⟨"identity", [.label 2, .formula (.atom "p")]⟩ : Rule)
```

The former `Micro` namespace, `RuleMap`, `CoreRule`, `CoreStep`,
`PropositionalStep`, `StandardStep`, parameterized `Rule E`, and
extension-parameterized tree types have been removed. The existing certificate
theorems now use composed calculi and flat named rules directly. Examples check
rejection of a box-right leaf and of a step whose premise introduces no new
label. Semantic soundness is deliberately kept out of this foundational
syntax module and is proved generically in
[`HOLMS.LabelledSoundness`](../HOLMS/LabelledSoundness.lean), then specialized
by the individual system modules.

## Verified certificate examples and generic results

The module proves validity monotonicity under local step inclusion; the system
modules use it for inclusions such as K-to-T and T-to-B while preserving the
same raw tree. Existential derivability is monotone as well. `identity_valid`
and the generic certificate lemmas use rule-availability classes rather than
hard-coding a system name.

Certificate lemmas require only the appropriate capability groups:

| Lemma | Required capabilities |
|---|---|
| `identity_valid`, `conjunctionTree_valid` | `HasPropositionalCore` |
| `boxUseTree_valid` | `HasPropositionalCore`, `HasBoxLeft` |
| `boxedIdentityTree_valid` | `HasPropositionalCore`, `HasBoxLeft`, `HasBoxRight` |

The tree datatype and validity definition do not impose `HasCore`. A
calculus can omit or replace selected standard rules through its explicit
definition. Finer propositional fragments can be assembled from singleton calculi,
but need their own weaker inclusion hypotheses rather than
`HasPropositionalCore`.

`boxedIdentityTree` uses box-right, box-left, and identity; its validity only
requires distinct source and eigenlabels. `conjunctionTree` verifies a binary
conjunction-right step with both identity leaves. T- and B-specific
certificates, rejection examples, and structural computations now live with
their systems rather than in the common infrastructure.

## Scope and remaining obligations

Validity is currently a mathematical predicate, not an executable certificate
checker; no `Decidable` instance or Boolean validation algorithm is supplied.
There is no new proof-search tactic. Completeness, Hilbert correspondence,
general identity expansion, weakening, contraction, renaming preservation,
and cut elimination remain open. Acceptance by `Valid` in this module only
certifies adherence to the specified calculus; the separate
[`LabelledSoundness` implementation note](LabelledSoundness.md) documents the
generic semantic implication. The K, T, and B notes document the corresponding
system-level specializations.

Raw syntax and separate validity were chosen to keep a possible future HOL
Light deep embedding straightforward. No such port is implemented or promised.

## Verification

From `lean/`, build this module with `lake build HOLMS.Labelled`, then use
`lake build` to verify the public aggregate. The examples are kernel-checked
proofs and contain no proof placeholders or added axioms.
