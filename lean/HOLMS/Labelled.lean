import HOLMS.Modal

/-!
# Labelled sequents and raw proof trees

A prototype classical labelled calculus with explicit proof trees, a shared
validity predicate, and K/T/B rule relations. No semantic adequacy or structural
admissibility theorem is asserted by this module.

This module is a Lean-specific deep embedding with no direct counterpart in
HOL Light. The HOL Light library implements labelled proof search through
shallow tactics rather than explicit sequent and proof-tree datatypes; this
applies to all declarations below.
-/

namespace HOLMS.Labelled

/-- Syntactic names for worlds.
Natural numbers make freshness easy to compute and prove: adding one to the
maximum label in a sequent gives a label absent from all its contexts. -/
abbrev Label := Nat

/-- A modal formula annotated with a syntactic world label. -/
structure LFormula where
  -- Syntactic world label.
  label : Label
  -- Modal formula.
  formula : Form
  deriving DecidableEq, Repr

/-- A syntactic accessibility assertion. -/
structure RelAtom where
  -- Source label of a relational atom.
  source : Label
  -- Target label of a relational atom.
  target : Label
  deriving DecidableEq, Repr

/-- A two-sided labelled sequent with a separate relational context. -/
structure Sequent where
  -- Finite multiset of relational atoms.
  relations : Multiset RelAtom
  -- Antecedent occurrences.
  left : Multiset LFormula
  -- Succedent occurrences.
  right : Multiset LFormula
  deriving DecidableEq

/-- The finite support of all three contexts of a sequent. -/
def Sequent.labels (s : Sequent) : Finset Label :=
  (s.relations.toFinset.biUnion fun a => {a.source, a.target}) ∪
  (s.left.toFinset.image LFormula.label) ∪
  (s.right.toFinset.image LFormula.label)

/-- A canonical choice of a label absent from the sequent. -/
def Sequent.fresh (s : Sequent) : Label := s.labels.sup id + 1

/-- The canonical fresh label does not occur in any context. -/
theorem Sequent.fresh_not_mem (s : Sequent) : s.fresh ∉ s.labels := by
  intro h
  have hle : s.fresh ≤ s.labels.sup id := Finset.le_sup (f := id) h
  exact Nat.not_succ_le_self _ hle

/-!
Each rule has an independent inductive step relation specifying premises,
conclusions, and side conditions. `Rule` provides a shared open encoding of
rule names and arguments, without a separate datatype for each rule.
-/

/-- Atomic payloads for rule instances. -/
inductive RuleArgument where
  -- Formula argument.
  | formula (value : Form)
  -- World-label argument.
  | label (value : Label)
  deriving DecidableEq, Repr

/-- A rule instance identified by a string and a flat list of atomic arguments. -/
structure Rule where
  /-- String identifying the rule family. -/
  name : String
  /-- Ordered principal labels and formulas. -/
  arguments : List RuleArgument
  deriving DecidableEq, Repr

-- Rule equality compares both the string name and the flat argument list.
example : (⟨"identity", [.label 0, .formula (.atom "p")]⟩ : Rule) ≠
    ⟨"identity", [.label 1, .formula (.atom "p")]⟩ := by decide +kernel

/-- Identity instances indexed by the principal label and formula. -/
inductive IdentityStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Identity with arbitrary side contexts.
  | identity (r g d) (x a) :
      IdentityStep
        [.label x, .formula a]
        []
        ⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩

/-- Every identity sequent determines its flat rule value. -/
theorem IdentityStep.exists_arguments (r : Multiset RelAtom) (g d : Multiset LFormula)
    (x : Label) (a : Form) :
    ∃ args, IdentityStep args [] ⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩ :=
  ⟨[.label x, .formula a], .identity r g d x a⟩

-- Missing the formula argument cannot describe an identity instance.
example (s : Sequent) :
    ¬IdentityStep [.label 0] [] s := by
  intro h
  cases h

-- Empty side contexts do not occur in the rule arguments.
example (x : Label) (a : Form) :
    IdentityStep [.label x, .formula a]
      [] ⟨0, {⟨x, a⟩}, {⟨x, a⟩}⟩ := by
  exact .identity 0 0 0 x a

/-- Falsity-left instances indexed by their principal label. -/
inductive FalsumLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Falsity initial sequent with arbitrary side contexts.
  | falsumLeft (r g d) (x) :
      FalsumLeftStep
        [.label x]
        []
        ⟨r, ⟨x, .falsum⟩ ::ₘ g, d⟩

/-- Every falsity-left sequent determines its flat rule value. -/
theorem FalsumLeftStep.exists_arguments (r : Multiset RelAtom) (g d : Multiset LFormula)
    (x : Label) :
    ∃ args, FalsumLeftStep args [] ⟨r, ⟨x, .falsum⟩ ::ₘ g, d⟩ :=
  ⟨[.label x], .falsumLeft r g d x⟩

-- The principal argument is a label rather than a formula.
example (a : Form) (s : Sequent) :
    ¬FalsumLeftStep [.formula a] [] s := by
  intro h
  cases h

/-- Local instances of `verumRight`, including contexts and side conditions. -/
inductive VerumRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Truth initial sequent.
  | verumRight (r g d) (x) : VerumRightStep [.label x] []
      ⟨r, g, ⟨x, .verum⟩ ::ₘ d⟩

/-- Local instances of `verumLeft`, including contexts and side conditions. -/
inductive VerumLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Truth-left instance.
  | verumLeft (r g d) (x) : VerumLeftStep [.label x]
      [⟨r, g, d⟩] ⟨r, ⟨x, .verum⟩ ::ₘ g, d⟩

/-- Local instances of `falsumRight`, including contexts and side conditions. -/
inductive FalsumRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Falsity-right instance.
  | falsumRight (r g d) (x) : FalsumRightStep [.label x]
      [⟨r, g, d⟩] ⟨r, g, ⟨x, .falsum⟩ ::ₘ d⟩

/-- Local instances of `negLeft`, including contexts and side conditions. -/
inductive NegLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Negation-left instance.
  | negLeft (r g d) (x a) : NegLeftStep [.label x, .formula a]
      [⟨r, g, ⟨x, a⟩ ::ₘ d⟩] ⟨r, ⟨x, .neg a⟩ ::ₘ g, d⟩

/-- Local instances of `negRight`, including contexts and side conditions. -/
inductive NegRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Negation-right instance.
  | negRight (r g d) (x a) : NegRightStep [.label x, .formula a]
      [⟨r, ⟨x, a⟩ ::ₘ g, d⟩] ⟨r, g, ⟨x, .neg a⟩ ::ₘ d⟩

/-- Local instances of `conjLeft`, including contexts and side conditions. -/
inductive ConjLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Conjunction-left instance.
  | conjLeft (r g d) (x a b) : ConjLeftStep
      [.label x, .formula a, .formula b]
      [⟨r, ⟨x, a⟩ ::ₘ ⟨x, b⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .conj a b⟩ ::ₘ g, d⟩

/-- Local instances of `conjRight`, including contexts and side conditions. -/
inductive ConjRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Conjunction-right instance.
  | conjRight (r g d) (x a b) : ConjRightStep
      [.label x, .formula a, .formula b]
      [⟨r, g, ⟨x, a⟩ ::ₘ d⟩, ⟨r, g, ⟨x, b⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .conj a b⟩ ::ₘ d⟩

/-- Local instances of `disjLeft`, including contexts and side conditions. -/
inductive DisjLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Disjunction-left instance.
  | disjLeft (r g d) (x a b) : DisjLeftStep
      [.label x, .formula a, .formula b]
      [⟨r, ⟨x, a⟩ ::ₘ g, d⟩, ⟨r, ⟨x, b⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .disj a b⟩ ::ₘ g, d⟩

/-- Local instances of `disjRight`, including contexts and side conditions. -/
inductive DisjRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Disjunction-right instance.
  | disjRight (r g d) (x a b) : DisjRightStep
      [.label x, .formula a, .formula b]
      [⟨r, g, ⟨x, a⟩ ::ₘ ⟨x, b⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .disj a b⟩ ::ₘ d⟩

/-- Local instances of `impLeft`, including contexts and side conditions. -/
inductive ImpLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Context-sharing classical implication-left instance.
  | impLeft (r g d) (x a b) : ImpLeftStep
      [.label x, .formula a, .formula b]
      [⟨r, g, ⟨x, a⟩ ::ₘ d⟩, ⟨r, ⟨x, b⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .imp a b⟩ ::ₘ g, d⟩

/-- Local instances of `impRight`, including contexts and side conditions. -/
inductive ImpRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Implication-right instance.
  | impRight (r g d) (x a b) : ImpRightStep
      [.label x, .formula a, .formula b]
      [⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, b⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .imp a b⟩ ::ₘ d⟩

/-- Local instances of `iffLeft`, including contexts and side conditions. -/
inductive IffLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Biconditional-left instance via both implications.
  | iffLeft (r g d) (x a b) : IffLeftStep
      [.label x, .formula a, .formula b]
      [⟨r, ⟨x, .imp a b⟩ ::ₘ ⟨x, .imp b a⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .iff a b⟩ ::ₘ g, d⟩

/-- Local instances of `iffRight`, including contexts and side conditions. -/
inductive IffRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Biconditional-right instance.
  | iffRight (r g d) (x a b) : IffRightStep
      [.label x, .formula a, .formula b]
      [⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, b⟩ ::ₘ d⟩,
       ⟨r, ⟨x, b⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .iff a b⟩ ::ₘ d⟩

/-- Local instances of `boxLeft`, including contexts and side conditions. -/
inductive BoxLeftStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Box-left retains the principal box and accessibility atom.
  | boxLeft (r g d) (x y a) : BoxLeftStep
      [.label x, .label y, .formula a]
      [⟨⟨x, y⟩ ::ₘ r, ⟨y, a⟩ ::ₘ ⟨x, .box a⟩ ::ₘ g, d⟩]
      ⟨⟨x, y⟩ ::ₘ r, ⟨x, .box a⟩ ::ₘ g, d⟩

/-- Local instances of `boxRight`, including contexts and side conditions. -/
inductive BoxRightStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Eigenlabel is fresh in all three conclusion contexts.
  | boxRight (r g d) (x y a)
      (fresh : y ∉ (Sequent.mk r g (⟨x, .box a⟩ ::ₘ d)).labels) :
      BoxRightStep
        [.label x, .label y, .formula a]
        [⟨⟨x, y⟩ ::ₘ r, g, ⟨y, a⟩ ::ₘ d⟩]
        ⟨r, g, ⟨x, .box a⟩ ::ₘ d⟩

/-- Reflexivity removes an auxiliary self-edge from the premise. -/
inductive ReflStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- Independent reflexivity step with arbitrary side contexts.
  | refl (r g d) (x) : ReflStep [.label x]
      [⟨⟨x, x⟩ ::ₘ r, g, d⟩] ⟨r, g, d⟩

/-- Symmetry removes an auxiliary reverse edge from the premise. -/
-- HOL: no direct labelled counterpart; deep-embedding rule corresponding to
-- `SYMMETRIC` and the B schema used in `b_completeness.ml`.
inductive SymmStep : List RuleArgument → List Sequent → Sequent → Prop where
  -- The forward edge remains in both premise and conclusion.
  -- HOL: no direct labelled counterpart; rule induced by `SYMMETRIC`.
  | symm (r g d) (x y) : SymmStep [.label x, .label y]
      [⟨⟨y, x⟩ ::ₘ ⟨x, y⟩ ::ₘ r, g, d⟩]
      ⟨⟨x, y⟩ ::ₘ r, g, d⟩

/-- The local schema stored under one rule name. -/
abbrev RuleSchema := List RuleArgument → List Sequent → Sequent → Prop

/-- A calculus is an extensible map from rule names to local inference schemas. -/
def Calculus := String → RuleSchema

namespace Calculus

/-- The calculus accepting no rule instances. -/
def empty : Calculus := fun _ _ _ _ => False

/-- A calculus with one named rule schema. -/
def singleton (name : String) (schema : RuleSchema) : Calculus :=
  fun candidate args ps s => candidate = name ∧ schema args ps s

/-- Pointwise composition of calculi. Duplicate names denote alternative schemas. -/
def union (left right : Calculus) : Calculus :=
  fun name args ps s => left name args ps s ∨ right name args ps s

/-- Compose a finite list of calculi. -/
def unions : List Calculus → Calculus
  | [] => empty
  | rules :: rest => rules.union (unions rest)

/-- Extensional inclusion of the rule instances accepted by two calculi. -/
def Included (left right : Calculus) : Prop :=
  ∀ name args ps s, left name args ps s → right name args ps s

/-- Calculus inclusion is reflexive. -/
theorem Included.refl (rules : Calculus) : rules.Included rules :=
  fun _ _ _ _ h => h

/-- Calculus inclusion is transitive. -/
theorem Included.trans {first second third : Calculus}
    (h₁ : first.Included second) (h₂ : second.Included third) :
    first.Included third := fun _ _ _ _ h => h₂ _ _ _ _ (h₁ _ _ _ _ h)

/-- The left component is included in a pointwise union. -/
theorem included_union_left (left right : Calculus) :
    left.Included (left.union right) := fun _ _ _ _ h => Or.inl h

/-- The right component is included in a pointwise union. -/
theorem included_union_right (left right : Calculus) :
    right.Included (left.union right) := fun _ _ _ _ h => Or.inr h

/-- Every member of a finite family is included in its composed calculus. -/
theorem included_unions_of_mem {rules : Calculus} {family : List Calculus}
    (h : rules ∈ family) : rules.Included (unions family) := by
  induction family with
  | nil => simp at h
  | cons first rest ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact included_union_left _ _
    · exact (ih h).trans (included_union_right _ _)

/-- Apply a calculus to the name and arguments stored in a raw rule. -/
def step (rules : Calculus) (rule : Rule) (ps : List Sequent) (s : Sequent) : Prop :=
  rules rule.name rule.arguments ps s

end Calculus

abbrev identityCalculus : Calculus := Calculus.singleton "identity" IdentityStep
abbrev falsumLeftCalculus : Calculus := Calculus.singleton "falsumLeft" FalsumLeftStep
abbrev verumRightCalculus : Calculus := Calculus.singleton "verumRight" VerumRightStep
abbrev verumLeftCalculus : Calculus := Calculus.singleton "verumLeft" VerumLeftStep
abbrev falsumRightCalculus : Calculus := Calculus.singleton "falsumRight" FalsumRightStep
abbrev negLeftCalculus : Calculus := Calculus.singleton "negLeft" NegLeftStep
abbrev negRightCalculus : Calculus := Calculus.singleton "negRight" NegRightStep
abbrev conjLeftCalculus : Calculus := Calculus.singleton "conjLeft" ConjLeftStep
abbrev conjRightCalculus : Calculus := Calculus.singleton "conjRight" ConjRightStep
abbrev disjLeftCalculus : Calculus := Calculus.singleton "disjLeft" DisjLeftStep
abbrev disjRightCalculus : Calculus := Calculus.singleton "disjRight" DisjRightStep
abbrev impLeftCalculus : Calculus := Calculus.singleton "impLeft" ImpLeftStep
abbrev impRightCalculus : Calculus := Calculus.singleton "impRight" ImpRightStep
abbrev iffLeftCalculus : Calculus := Calculus.singleton "iffLeft" IffLeftStep
abbrev iffRightCalculus : Calculus := Calculus.singleton "iffRight" IffRightStep
abbrev boxLeftCalculus : Calculus := Calculus.singleton "boxLeft" BoxLeftStep
abbrev boxRightCalculus : Calculus := Calculus.singleton "boxRight" BoxRightStep
abbrev reflCalculus : Calculus := Calculus.singleton "refl" ReflStep
/-- The singleton calculus containing the symmetry rule. -/
-- HOL: no direct labelled counterpart; singleton map for the symmetry rule.
abbrev symmCalculus : Calculus := Calculus.singleton "symm" SymmStep

/-- The composition of all standard propositional calculi. -/
def propositionalCalculus : Calculus := Calculus.unions
  [identityCalculus, falsumLeftCalculus, verumRightCalculus, verumLeftCalculus,
   falsumRightCalculus, negLeftCalculus, negRightCalculus, conjLeftCalculus,
   conjRightCalculus, disjLeftCalculus, disjRightCalculus, impLeftCalculus,
   impRightCalculus, iffLeftCalculus, iffRightCalculus]

/-- The standard K calculus: propositional rules plus both box rules. -/
def standardCalculus : Calculus := Calculus.unions
  [propositionalCalculus, boxLeftCalculus, boxRightCalculus]


-- A zero-premise box-right step is rejected.
example (args : List RuleArgument) (s : Sequent) : ¬BoxRightStep args [] s := by
  intro h
  cases h

-- Box-right requires a genuinely new label in its premise.
example {args : List RuleArgument} {ps : List Sequent} {s : Sequent}
    (support : ∀ p ∈ ps, p.labels ⊆ s.labels) : ¬BoxRightStep args ps s := by
  intro h
  cases h with
  | boxRight r g d x y a fresh =>
    apply fresh
    apply support ⟨⟨x, y⟩ ::ₘ r, g, ⟨y, a⟩ ::ₘ d⟩ (by simp)
    simp [Sequent.labels]

/-- A certificate that a calculus includes the propositional core instances. -/
class HasPropositionalCore (C : Calculus) : Prop where
  /-- Availability of every propositional core instance. -/
  included : propositionalCalculus.Included C

/-- A certificate that a calculus includes the standard box-left instances. -/
class HasBoxLeft (C : Calculus) : Prop where
  /-- Availability of every standard box-left instance. -/
  included : boxLeftCalculus.Included C

/-- A certificate that a calculus includes the standard box-right instances. -/
class HasBoxRight (C : Calculus) : Prop where
  /-- Availability of every standard box-right instance, with its freshness condition. -/
  included : boxRightCalculus.Included C

/-- Bundle all three standard core capabilities for ordinary extensions. -/
class HasCore (C : Calculus) : Prop where
  /-- Availability of the complete standard K calculus. -/
  included : standardCalculus.Included C

/-- The propositional component is included in the standard map. -/
theorem propositional_included_standard :
    propositionalCalculus.Included standardCalculus :=
  Calculus.included_unions_of_mem (by simp)

/-- The box-left component is included in the standard map. -/
theorem boxLeft_included_standard :
    boxLeftCalculus.Included standardCalculus :=
  Calculus.included_unions_of_mem (by simp)

/-- The box-right component is included in the standard map. -/
theorem boxRight_included_standard :
    boxRightCalculus.Included standardCalculus :=
  Calculus.included_unions_of_mem (by simp)

-- Extract granular capabilities automatically from inclusion of the standard map.
instance {C : Calculus} [HasCore C] : HasPropositionalCore C where
  included := propositional_included_standard.trans HasCore.included

instance {C : Calculus} [HasCore C] : HasBoxLeft C where
  included := boxLeft_included_standard.trans HasCore.included

instance {C : Calculus} [HasCore C] : HasBoxRight C where
  included := boxRight_included_standard.trans HasCore.included

/-- A certificate that a calculus permits the primitive reflexivity rule. -/
class HasRefl (C : Calculus) : Prop where
  /-- Availability of primitive reflexivity steps, rather than an admissibility result. -/
  included : reflCalculus.Included C

/-- A certificate that a calculus permits the primitive symmetry rule. -/
-- HOL: no direct labelled counterpart; rule availability for the B extension.
class HasSymm (C : Calculus) : Prop where
  /-- Availability of primitive symmetry steps, rather than an admissibility result. -/
  -- HOL: no direct labelled counterpart; inclusion field for the B extension.
  included : symmCalculus.Included C

/-- Use a propositional rule-map entry in a calculus that contains that map. -/
theorem HasPropositionalCore.admitted {C : Calculus} [HasPropositionalCore C]
    {rule ps s} (h : propositionalCalculus.step rule ps s) :
    C.step rule ps s :=
  HasPropositionalCore.included rule.name rule.arguments ps s h

/-- Use a box-left rule-map entry in a calculus that contains that map. -/
theorem HasBoxLeft.admitted {C : Calculus} [HasBoxLeft C]
    {rule ps s} (h : boxLeftCalculus.step rule ps s) :
    C.step rule ps s :=
  HasBoxLeft.included rule.name rule.arguments ps s h

/-- Use a box-right rule-map entry in a calculus that contains that map. -/
theorem HasBoxRight.admitted {C : Calculus} [HasBoxRight C]
    {rule ps s} (h : boxRightCalculus.step rule ps s) :
    C.step rule ps s :=
  HasBoxRight.included rule.name rule.arguments ps s h

/-- Use a reflexivity rule-map entry in a calculus that contains that map. -/
theorem HasRefl.admitted {C : Calculus} [HasRefl C]
    {rule ps s} (h : reflCalculus.step rule ps s) :
    C.step rule ps s :=
  HasRefl.included rule.name rule.arguments ps s h

/-- Use a symmetry rule-map entry in a calculus that contains that map. -/
-- HOL: no direct labelled counterpart; introduction interface for symmetry steps.
theorem HasSymm.admitted {C : Calculus} [HasSymm C]
    {rule ps s} (h : symmCalculus.step rule ps s) :
    C.step rule ps s :=
  HasSymm.included rule.name rule.arguments ps s h

/-- K contains exactly the standard propositional and modal rule families. -/
def K : Calculus := standardCalculus

/-- T extends the core by the reflexivity rule family. -/
def T : Calculus := standardCalculus.union reflCalculus

/-- B extends T by the symmetry rule family.

This follows HOLMS terminology: `B_AX` contains both the T and B schemas, so
its frames are reflexive and symmetric. The merely symmetric logic is KB. -/
-- HOL: labelled counterpart of the system generated by `B_AX` (`b_completeness.ml`).
def B : Calculus := T.union symmCalculus

/-- K includes the shared core. -/
instance : HasCore K := ⟨Calculus.Included.refl _⟩

/-- T includes the shared core. -/
instance : HasCore T := ⟨Calculus.included_union_left _ _⟩

/-- The reflexivity family is available in T. -/
instance : HasRefl T := ⟨Calculus.included_union_right _ _⟩

/-- B includes the shared core through its T component. -/
-- HOL: no direct labelled counterpart; core availability for `B_AX`.
instance : HasCore B :=
  ⟨(Calculus.included_union_left standardCalculus reflCalculus).trans
    (Calculus.included_union_left T symmCalculus)⟩

/-- The reflexivity family is available in B through its T component. -/
-- HOL: no direct labelled counterpart; T-rule availability for `B_AX`.
instance : HasRefl B :=
  ⟨(Calculus.included_union_right standardCalculus reflCalculus).trans
    (Calculus.included_union_left T symmCalculus)⟩

/-- The symmetry family is available in B. -/
-- HOL: no direct labelled counterpart; B-rule availability for `B_AX`.
instance : HasSymm B := ⟨Calculus.included_union_right _ _⟩

/-- Raw finite trees; arity and rule correctness are checked separately. -/
inductive ProofTree where
  -- Node records a conclusion, rule data, and ordered premises.
  | node (conclusion : Sequent) (rule : Rule) (children : List ProofTree)

/-- Read the root sequent without assuming correctness of the tree. -/
def ProofTree.conclusion : ProofTree → Sequent
  | .node s _ _ => s

/-- Height of a raw tree, with leaves at height one. -/
def ProofTree.height : ProofTree → Nat
  | .node _ _ ds => 1 + (ds.map ProofTree.height).foldr max 0

/-- Number of nodes of a raw tree. -/
def ProofTree.nodes : ProofTree → Nat
  | .node _ _ ds => 1 + (ds.map ProofTree.nodes).sum

/-- Every node is an allowed local step and all its children are valid. -/
inductive Valid (C : Calculus) : ProofTree → Prop where
  -- Validity includes both local correctness and every subtree.
  | node {s r ds} (step : C.step r (ds.map ProofTree.conclusion) s)
      (children : ∀ d ∈ ds, Valid C d) : Valid C (.node s r ds)

/-- Validity is characterized by the root step and all child validities. -/
theorem valid_node_iff {C : Calculus} {s r ds} :
    Valid C (.node s r ds) ↔
      C.step r (ds.map ProofTree.conclusion) s ∧ ∀ d ∈ ds, Valid C d := by
  constructor
  · intro h; cases h with | node hs hc => exact ⟨hs, hc⟩
  · rintro ⟨hs, hc⟩; exact .node hs hc

/-- Enlarging the step relation preserves the same raw certificate. -/
theorem Valid.mono {C D : Calculus} (inc : C.Included D)
    {d : ProofTree} (h : Valid C d) : Valid D d := by
  induction h with
  | node hs _ ih => exact .node (inc _ _ _ _ hs) ih

/-- Every K step is also a T step. -/
theorem k_included_t : K.Included T := by
  exact Calculus.included_union_left _ _

/-- A K-valid tree remains valid in T without changing the tree. -/
theorem Valid.k_to_t {d : ProofTree} (h : Valid K d) : Valid T d :=
  h.mono k_included_t

/-- Every T step is also a B step. -/
-- HOL: no direct labelled counterpart; inclusion induced by the definition of `B_AX`.
theorem t_included_b : T.Included B := by
  exact Calculus.included_union_left _ _

/-- A T-valid tree remains valid in B without changing the tree. -/
-- HOL: no direct labelled counterpart; certificate monotonicity from T to B.
theorem Valid.t_to_b {d : ProofTree} (h : Valid T d) : Valid B d :=
  h.mono t_included_b

/-- Derivability means existence of a valid explicit tree with this root. -/
def Derivable (C : Calculus) (s : Sequent) : Prop :=
  ∃ d : ProofTree, Valid C d ∧ d.conclusion = s

/-- Derivability is monotone under inclusion of local rule instances. -/
theorem Derivable.mono {C D : Calculus} (inc : C.Included D)
    {s : Sequent} (h : Derivable C s) : Derivable D s := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd.mono inc, hs⟩

/-- Assemble a valid leaf only from a permitted zero-premise step. -/
theorem Valid.leaf {C : Calculus} {r s} (h : C.step r [] s) :
    Valid C (.node s r []) := .node h (by simp)

/-- Assemble a valid unary node from its local step and child certificate. -/
theorem Valid.unary {C : Calculus} {r s d}
    (h : C.step r [ProofTree.conclusion d] s) (hd : Valid C d) :
    Valid C (.node s r [d]) := .node h (by simpa using hd)

/-- Assemble a valid binary node from its step and both child certificates. -/
theorem Valid.binary {C : Calculus} {r s d₁ d₂}
    (h : C.step r [ProofTree.conclusion d₁, ProofTree.conclusion d₂] s)
    (h₁ : Valid C d₁) (h₂ : Valid C d₂) :
    Valid C (.node s r [d₁, d₂]) := .node h (by simp_all)

/-- Generalized identity needs only the propositional core. -/
theorem identity_valid (C : Calculus) [HasPropositionalCore C]
    (r g d) (x : Label) (a : Form) :
    Valid C (.node ⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩
      ⟨"identity", [.label x, .formula a]⟩ []) :=
  .leaf (HasPropositionalCore.admitted (by
    simpa [Calculus.step, propositionalCalculus, Calculus.unions,
      Calculus.union, Calculus.singleton, Calculus.empty] using
        IdentityStep.identity r g d x a))

/-- K never accepts a node carrying the reflexivity rule. -/
theorem not_valid_k_refl (s : Sequent) (x : Label) (ds : List ProofTree) :
    ¬Valid K (.node s ⟨"refl", [.label x]⟩ ds) := by
  intro h
  have hs := (valid_node_iff.mp h).1
  simp [Calculus.step, K, standardCalculus, propositionalCalculus,
    Calculus.unions, Calculus.union, Calculus.singleton, Calculus.empty] at hs

/-- T never accepts a node carrying the primitive symmetry rule. -/
-- HOL: no direct labelled counterpart; separates the T and B certificate languages.
theorem not_valid_t_symm (s : Sequent) (x y : Label) (ds : List ProofTree) :
    ¬Valid T (.node s ⟨"symm", [.label x, .label y]⟩ ds) := by
  intro h
  have hs := (valid_node_iff.mp h).1
  simp [Calculus.step, T, standardCalculus, propositionalCalculus,
    Calculus.unions, Calculus.union, Calculus.singleton, Calculus.empty] at hs

/-- A box-right rule cannot reuse its source as its eigenlabel. -/
theorem boxRight_source_ne {x y : Label} {a : Form} {ps s}
    (h : BoxRightStep
      [.label x, .label y, .formula a] ps s) : y ≠ x := by
  cases h with
  | boxRight r g d x y a fresh =>
    intro heq
    subst y
    apply fresh
    simp [Sequent.labels]


/-- Use an existing edge to expose the content of a boxed assumption. -/
def boxUseTree (r : Multiset RelAtom) (x y : Label) (a : Form) : ProofTree :=
  .node ⟨⟨x, y⟩ ::ₘ r, {⟨x, .box a⟩}, {⟨y, a⟩}⟩
    ⟨"boxLeft", [.label x, .label y, .formula a]⟩
    [.node ⟨⟨x, y⟩ ::ₘ r, ⟨y, a⟩ ::ₘ {⟨x, .box a⟩}, {⟨y, a⟩}⟩
      ⟨"identity", [.label y, .formula a]⟩ []]

/-- The box-left certificate needs propositional rules and box-left, but not box-right. -/
theorem boxUseTree_valid (C : Calculus)
    [HasPropositionalCore C] [HasBoxLeft C]
    (r : Multiset RelAtom) (x y : Label) (a : Form) :
    Valid C (boxUseTree r x y a) := by
  apply Valid.unary
  · apply HasBoxLeft.admitted
    simpa [Calculus.step, Calculus.singleton,
      ProofTree.conclusion, Multiset.cons_zero] using
        BoxLeftStep.boxLeft r 0 {⟨y, a⟩} x y a
  · exact identity_valid C (⟨x, y⟩ ::ₘ r) {⟨x, .box a⟩} 0 y a

/-- A box-right certificate for boxed identity, sharing the same raw syntax in K/T. -/
def boxedIdentityTree (x y : Label) (a : Form) : ProofTree :=
  .node ⟨0, {⟨x, .box a⟩}, {⟨x, .box a⟩}⟩
    ⟨"boxRight", [.label x, .label y, .formula a]⟩
    [boxUseTree 0 x y a]

/-- Boxed identity is valid when the eigenlabel differs from the source. -/
theorem boxedIdentityTree_valid (C : Calculus)
    [HasPropositionalCore C] [HasBoxLeft C] [HasBoxRight C]
    (x y : Label) (a : Form) (fresh : y ≠ x) :
    Valid C (boxedIdentityTree x y a) := by
  apply Valid.unary
  · apply HasBoxRight.admitted
    simpa [Calculus.step, Calculus.singleton, boxUseTree,
      ProofTree.conclusion, Multiset.cons_zero] using
      BoxRightStep.boxRight 0 {⟨x, .box a⟩} 0 x y a (by
        simpa [Sequent.labels] using fresh)
  · exact boxUseTree_valid C 0 x y a

/-- A certificate for 0 : □a ⊢ x : a`, using box-left and reflexivity. -/
def reflexiveBoxTree (x : Label) (a : Form) : ProofTree :=
  .node ⟨0, {⟨x, .box a⟩}, {⟨x, a⟩}⟩
    ⟨"refl", [.label x]⟩ [boxUseTree 0 x x a]

/-- The reflexive box certificate needs propositional rules, box-left, and reflexivity. -/
theorem reflexiveBoxTree_valid (C : Calculus)
    [HasPropositionalCore C] [HasBoxLeft C] [HasRefl C]
    (x : Label) (a : Form) : Valid C (reflexiveBoxTree x a) := by
  apply Valid.unary
  · apply HasRefl.admitted
    simpa [Calculus.step, Calculus.singleton,
      boxUseTree, ProofTree.conclusion] using
      ReflStep.refl 0 {⟨x, .box a⟩} {⟨x, a⟩} x
  · exact boxUseTree_valid C 0 x x a

/-- An explicit derivation of `□a → a` at a label. -/
def tAxiomTree (x : Label) (a : Form) : ProofTree :=
  .node ⟨0, 0, {⟨x, .imp (.box a) a⟩}⟩
    ⟨"impRight", [.label x, .formula (.box a), .formula a]⟩
    [reflexiveBoxTree x a]

/-- The T-axiom tree needs no box-right capability. -/
theorem tAxiomTree_valid (C : Calculus)
    [HasPropositionalCore C] [HasBoxLeft C] [HasRefl C]
    (x : Label) (a : Form) : Valid C (tAxiomTree x a) := by
  apply Valid.unary
  · apply HasPropositionalCore.admitted
    simpa [Calculus.step, propositionalCalculus, Calculus.unions,
      Calculus.union, Calculus.singleton, Calculus.empty,
      reflexiveBoxTree, ProofTree.conclusion] using
        ImpRightStep.impRight 0 0 0 x (.box a) a
  · exact reflexiveBoxTree_valid C x a

/-- This T-axiom certificate is invalid in K because it uses reflexivity.
This rejects this particular tree; it does not assert nonderivability in K. -/
theorem tAxiomTree_not_valid_k (x : Label) (a : Form) :
    ¬Valid K (tAxiomTree x a) := by
  intro h
  have hc := (valid_node_iff.mp h).2 (reflexiveBoxTree x a) (by simp)
  exact not_valid_k_refl _ _ _ hc

/-- The central symmetry subderivation for the B axiom.

From `x R y`, `x : a`, and `y : □¬a`, symmetry supplies `y R x`;
box-left and negation-left then close by identity at `x : a`. -/
-- HOL: no direct labelled counterpart; certificate form of the B-schema argument
-- used semantically by `MODAL_SYM` (`ad_hoc_correspondence.ml`).
def symmetricContradictionTree (x y : Label) (a : Form) : ProofTree :=
  .node ⟨{⟨x, y⟩}, ⟨y, .box (.neg a)⟩ ::ₘ {⟨x, a⟩}, 0⟩
    ⟨"symm", [.label x, .label y]⟩
    [.node ⟨⟨y, x⟩ ::ₘ {⟨x, y⟩},
        ⟨y, .box (.neg a)⟩ ::ₘ {⟨x, a⟩}, 0⟩
      ⟨"boxLeft", [.label y, .label x, .formula (.neg a)]⟩
      [.node ⟨⟨y, x⟩ ::ₘ {⟨x, y⟩},
          ⟨x, .neg a⟩ ::ₘ ⟨y, .box (.neg a)⟩ ::ₘ {⟨x, a⟩}, 0⟩
        ⟨"negLeft", [.label x, .formula a]⟩
        [.node ⟨⟨y, x⟩ ::ₘ {⟨x, y⟩},
            ⟨x, a⟩ ::ₘ {⟨y, .box (.neg a)⟩}, {⟨x, a⟩}⟩
          ⟨"identity", [.label x, .formula a]⟩ []]]]

/-- The symmetry subderivation is accepted by every calculus containing the
propositional, box-left, and symmetry families. -/
-- HOL: no direct labelled counterpart; validity of `symmetricContradictionTree`.
theorem symmetricContradictionTree_valid (C : Calculus)
    [HasPropositionalCore C] [HasBoxLeft C] [HasSymm C]
    (x y : Label) (a : Form) : Valid C (symmetricContradictionTree x y a) := by
  unfold symmetricContradictionTree
  apply Valid.unary
  · apply HasSymm.admitted
    simpa [Calculus.step, Calculus.singleton, ProofTree.conclusion,
      Multiset.cons_zero] using
      SymmStep.symm 0 (⟨y, .box (.neg a)⟩ ::ₘ {⟨x, a⟩}) 0 x y
  · apply Valid.unary
    · apply HasBoxLeft.admitted
      simpa [Calculus.step, Calculus.singleton, ProofTree.conclusion,
        Multiset.cons_zero] using
        BoxLeftStep.boxLeft {⟨x, y⟩} {⟨x, a⟩} 0 y x (.neg a)
    · apply Valid.unary
      · apply HasPropositionalCore.admitted
        have hswap :
            (⟨y, .box (.neg a)⟩ ::ₘ {⟨x, a⟩} : Multiset LFormula) =
              ⟨x, a⟩ ::ₘ {⟨y, .box (.neg a)⟩} := by
          simpa using Multiset.cons_swap
            (⟨y, .box (.neg a)⟩ : LFormula) ⟨x, a⟩ 0
        simpa [Calculus.step, propositionalCalculus, Calculus.unions,
          Calculus.union, Calculus.singleton, Calculus.empty,
          ProofTree.conclusion, hswap] using
          NegLeftStep.negLeft (⟨y, x⟩ ::ₘ {⟨x, y⟩})
            (⟨y, .box (.neg a)⟩ ::ₘ {⟨x, a⟩}) 0 x a
      · exact identity_valid C (⟨y, x⟩ ::ₘ {⟨x, y⟩})
          {⟨y, .box (.neg a)⟩} 0 x a

/-- The negation-right stage deriving `y : ◇a` from the symmetry
subderivation. -/
-- HOL: no direct labelled counterpart; internal certificate stage for `B_AX_B`.
def bDiamondTree (x y : Label) (a : Form) : ProofTree :=
  .node ⟨{⟨x, y⟩}, {⟨x, a⟩}, {⟨y, Form.diam a⟩}⟩
    ⟨"negRight", [.label y, .formula (.box (.neg a))]⟩
    [symmetricContradictionTree x y a]

/-- The box-right stage deriving `x : □◇a` from a fresh eigenlabel. -/
-- HOL: no direct labelled counterpart; internal certificate stage for `B_AX_B`.
def bBoxTree (x y : Label) (a : Form) : ProofTree :=
  .node ⟨0, {⟨x, a⟩}, {⟨x, .box (Form.diam a)⟩}⟩
    ⟨"boxRight", [.label x, .label y, .formula (Form.diam a)]⟩
    [bDiamondTree x y a]

/-- An explicit derivation of the B schema `a → □◇a` at a label. -/
-- HOL: labelled certificate counterpart of `B_AX_B` (`b_completeness.ml`).
def bAxiomTree (x y : Label) (a : Form) : ProofTree :=
  .node ⟨0, 0, {⟨x, .imp a (.box (Form.diam a))⟩}⟩
    ⟨"impRight", [.label x, .formula a, .formula (.box (Form.diam a))]⟩
    [bBoxTree x y a]

/-- The B-axiom certificate is valid when box-right receives a fresh label. -/
-- HOL: labelled certificate counterpart of `B_AX_B` (`b_completeness.ml`).
theorem bAxiomTree_valid (C : Calculus)
    [HasPropositionalCore C] [HasBoxRight C] [HasBoxLeft C] [HasSymm C]
    (x y : Label) (a : Form) (fresh : y ≠ x) :
    Valid C (bAxiomTree x y a) := by
  unfold bAxiomTree bBoxTree bDiamondTree
  apply Valid.unary
  · apply HasPropositionalCore.admitted
    simpa [Calculus.step, propositionalCalculus, Calculus.unions,
      Calculus.union, Calculus.singleton, Calculus.empty,
      ProofTree.conclusion] using
      ImpRightStep.impRight 0 0 0 x a (.box (Form.diam a))
  · apply Valid.unary
    · apply HasBoxRight.admitted
      simpa [Calculus.step, Calculus.singleton, ProofTree.conclusion,
        Form.diam] using
        BoxRightStep.boxRight 0 {⟨x, a⟩} 0 x y (Form.diam a) (by
          simpa [Sequent.labels] using fresh)
    · apply Valid.unary
      · apply HasPropositionalCore.admitted
        simpa [Calculus.step, propositionalCalculus, Calculus.unions,
          Calculus.union, Calculus.singleton, Calculus.empty,
          symmetricContradictionTree, ProofTree.conclusion, Form.diam] using
          NegRightStep.negRight {⟨x, y⟩} {⟨x, a⟩} 0 y (.box (.neg a))
      · exact symmetricContradictionTree_valid C x y a

/-- This B-axiom certificate is invalid in T because it uses symmetry.
This rejects this particular tree; it does not assert nonderivability in T. -/
-- HOL: no direct labelled counterpart; certificate-level separation of T and B.
theorem bAxiomTree_not_valid_t (x y : Label) (a : Form) :
    ¬Valid T (bAxiomTree x y a) := by
  intro h
  have hbox := (valid_node_iff.mp h).2 (bBoxTree x y a) (by simp)
  have hneg := (valid_node_iff.mp hbox).2 (bDiamondTree x y a) (by simp)
  have hsymm := (valid_node_iff.mp hneg).2 (symmetricContradictionTree x y a)
    (by simp)
  exact not_valid_t_symm _ _ _ _ hsymm

/-- A box-right node with no premise cannot be a valid K certificate. -/
theorem boxRight_leaf_not_valid_k (s : Sequent) (x y : Label) (a : Form) :
    ¬Valid K (.node s
      ⟨"boxRight", [.label x, .label y, .formula a]⟩ []) := by
  intro h
  have hs := (valid_node_iff.mp h).1
  have hbox : BoxRightStep [.label x, .label y, .formula a] [] s := by
    simpa [Calculus.step, K, standardCalculus, propositionalCalculus,
      Calculus.unions, Calculus.union, Calculus.singleton, Calculus.empty] using hs
  cases hbox

/-- Conjunction-right combines two identity certificates using shared contexts. -/
def conjunctionTree (x : Label) (a : Form) : ProofTree :=
  .node ⟨0, {⟨x, a⟩}, {⟨x, .conj a a⟩}⟩
    ⟨"conjRight", [.label x, .formula a, .formula a]⟩
    [.node ⟨0, {⟨x, a⟩}, {⟨x, a⟩}⟩
      ⟨"identity", [.label x, .formula a]⟩ [],
     .node ⟨0, {⟨x, a⟩}, {⟨x, a⟩}⟩
      ⟨"identity", [.label x, .formula a]⟩ []]

/-- Both conjunction branches need only propositional rule availability. -/
theorem conjunctionTree_valid (C : Calculus) [HasPropositionalCore C]
    (x : Label) (a : Form) : Valid C (conjunctionTree x a) := by
  apply Valid.binary
  · apply HasPropositionalCore.admitted
    simpa [Calculus.step, propositionalCalculus, Calculus.unions,
      Calculus.union, Calculus.singleton, Calculus.empty,
      ProofTree.conclusion, Multiset.cons_zero] using
      ConjRightStep.conjRight 0 {⟨x, a⟩} 0 x a a
  · exact identity_valid C 0 0 0 x a
  · exact identity_valid C 0 0 0 x a

-- Branching example checks conjunction-right and both identity leaves.
example : Valid K (conjunctionTree 0 (.atom "p")) := conjunctionTree_valid K 0 _

-- Concrete K certificate exercising both modal rules and freshness.
example : Valid K (boxedIdentityTree 0 1 (.atom "p")) :=
  boxedIdentityTree_valid K 0 1 _ (by decide)

-- The identical raw K certificate is accepted in T by monotonicity.
example : Valid T (boxedIdentityTree 0 1 (.atom "p")) :=
  (boxedIdentityTree_valid K 0 1 _ (by decide)).k_to_t

-- Class-based validation of a concrete T-axiom certificate.
example : Valid T (tAxiomTree 0 (.atom "p")) := tAxiomTree_valid T 0 _

-- B retains T's reflexivity certificate without changing the raw tree.
-- HOL: no direct labelled counterpart; regression example for `T ⊆ B`.
example : Valid B (tAxiomTree 0 (.atom "p")) :=
  (tAxiomTree_valid T 0 _).t_to_b

-- Concrete B-schema certificate exercising the symmetry rule.
-- HOL: labelled certificate counterpart of the `B_AX_B` example.
example : Valid B (bAxiomTree 0 1 (.atom "p")) :=
  bAxiomTree_valid B 0 1 _ (by decide)

-- The same T-axiom certificate is rejected in K.
example : ¬Valid K (tAxiomTree 0 (.atom "p")) := tAxiomTree_not_valid_k 0 _

-- The B-schema certificate is rejected by T because the tree contains symmetry.
-- HOL: no direct labelled counterpart; regression example separating T from B.
example : ¬Valid T (bAxiomTree 0 1 (.atom "p")) :=
  bAxiomTree_not_valid_t 0 1 _

-- Structural measures compute on data without validity proofs.
example : (tAxiomTree 0 (.atom "p")).height = 4 ∧
    (tAxiomTree 0 (.atom "p")).nodes = 4 := by
  norm_num [tAxiomTree, reflexiveBoxTree, boxUseTree, ProofTree.height, ProofTree.nodes]

-- The B-schema certificate has one node for each of its seven inference steps.
-- HOL: no direct labelled counterpart; computation on the explicit B certificate.
example : (bAxiomTree 0 1 (.atom "p")).height = 7 ∧
    (bAxiomTree 0 1 (.atom "p")).nodes = 7 := by
  norm_num [bAxiomTree, bBoxTree, bDiamondTree, symmetricContradictionTree,
    ProofTree.height, ProofTree.nodes]


section CapabilityRegression

/-- A test calculus retaining T's rules except for standard box-right. -/
private def noBoxRight : Calculus := Calculus.unions
  [propositionalCalculus, boxLeftCalculus, reflCalculus]

-- The test calculus has propositional rules despite missing box-right.
local instance : HasPropositionalCore noBoxRight where
  included := Calculus.included_unions_of_mem (by simp)

-- Standard box-left remains available in the restricted test calculus.
local instance : HasBoxLeft noBoxRight where
  included := Calculus.included_unions_of_mem (by simp)

-- Reflexivity remains available independently of box-right.
local instance : HasRefl noBoxRight where
  included := Calculus.included_unions_of_mem (by simp)

-- The propositional certificate works without full-core availability.
example : Valid noBoxRight (conjunctionTree 0 (.atom "p")) :=
  conjunctionTree_valid noBoxRight 0 _

-- T's axiom certificate does not require the missing box-right rule.
example : Valid noBoxRight (tAxiomTree 0 (.atom "p")) :=
  tAxiomTree_valid noBoxRight 0 _

-- The restricted calculus rejects the certificate that uses standard box-right.
example : ¬Valid noBoxRight (boxedIdentityTree 0 1 (.atom "p")) := by
  intro h
  have hs := (valid_node_iff.mp h).1
  simp [Calculus.step, noBoxRight, propositionalCalculus, Calculus.unions,
    Calculus.union, Calculus.singleton, Calculus.empty] at hs

end CapabilityRegression

end HOLMS.Labelled
