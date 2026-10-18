import HOLMS.Modal

/-!
# Labelled sequents and raw proof trees

A prototype classical labelled calculus with explicit proof trees, a shared
validity predicate, and K/T rule relations. No semantic adequacy or structural
admissibility theorem is asserted by this module.

There is no corresponding deep embedding in HOL Light. HOLMS in HOL Light
provides only a shallow embedding of labelled sequent calculi through its
automated modal proof tactics. This file therefore has no HOL Light source
module with which it can be compared directly, declaration by declaration.
-/

namespace HOLMS.Labelled

/-- Syntactic names for worlds. -/
abbrev Label := Nat

/-- A modal formula annotated with a syntactic world label. -/
structure LFormula where
  -- Syntactic world label.
  label : Label
  -- Modal formula.
  formula : Form
  -- Generated equality and printing for labelled syntax.
  deriving DecidableEq, Repr

/-- A syntactic accessibility assertion. -/
structure RelAtom where
  -- Source label of a relational atom.
  source : Label
  -- Target label of a relational atom.
  target : Label
  -- Generated equality and printing for relational syntax.
  deriving DecidableEq, Repr

/-- A two-sided labelled sequent with a separate relational context. -/
structure Sequent where
  -- Finite multiset of relational atoms.
  relations : Multiset RelAtom
  -- Antecedent occurrences.
  left : Multiset LFormula
  -- Succedent occurrences.
  right : Multiset LFormula
  -- Generated decidable equality on sequents.
  deriving DecidableEq

/-- The finite support of all three contexts of a sequent. -/
-- Explicit label support for eigenlabel conditions.
def Sequent.labels (s : Sequent) : Finset Label :=
  (s.relations.toFinset.biUnion fun a => {a.source, a.target}) ∪
  (s.left.toFinset.image LFormula.label) ∪
  (s.right.toFinset.image LFormula.label)

/-- A canonical choice of a label absent from the sequent. -/
-- Constructive supply of fresh syntactic names.
def Sequent.fresh (s : Sequent) : Label := s.labels.sup id + 1

/-- The canonical fresh label does not occur in any context. -/
-- Freshness witness for the deep embedding.
theorem Sequent.fresh_not_mem (s : Sequent) : s.fresh ∉ s.labels := by
  intro h
  have hle : s.fresh ≤ s.labels.sup id := Finset.le_sup (f := id) h
  exact Nat.not_succ_le_self _ hle

/-- Names and principal data of the propositional and modal core rules. -/
inductive CoreRule where
  -- Generalized identity initial sequent.
  | identity (x : Label) (a : Form)
  -- Falsity in the antecedent.
  | falsumLeft (x : Label)
  -- Truth in the succedent.
  | verumRight (x : Label)
  -- Removal of truth from the antecedent.
  | verumLeft (x : Label)
  -- Removal of falsity from the succedent.
  | falsumRight (x : Label)
  -- Negation introduction on the left.
  | negLeft (x : Label) (a : Form)
  -- Negation introduction on the right.
  | negRight (x : Label) (a : Form)
  -- Conjunction introduction on the left.
  | conjLeft (x : Label) (a b : Form)
  -- Conjunction introduction on the right.
  | conjRight (x : Label) (a b : Form)
  -- Disjunction introduction on the left.
  | disjLeft (x : Label) (a b : Form)
  -- Disjunction introduction on the right.
  | disjRight (x : Label) (a b : Form)
  -- Implication introduction on the left.
  | impLeft (x : Label) (a b : Form)
  -- Implication introduction on the right.
  | impRight (x : Label) (a b : Form)
  -- Biconditional introduction on the left.
  | iffLeft (x : Label) (a b : Form)
  -- Biconditional introduction on the right.
  | iffRight (x : Label) (a b : Form)
  -- Box introduction on the left.
  | boxLeft (x y : Label) (a : Form)
  -- Box introduction on the right.
  | boxRight (x y : Label) (a : Form)
  -- Generated equality and printing for core rule data.
  deriving DecidableEq, Repr

/-- Select the propositional rules, including initial sequents, but neither box rule. -/
-- HOL: no deep counterpart; syntactic rule-family selector.
def CoreRule.IsPropositional : CoreRule → Prop
  | .boxLeft .. | .boxRight .. => False
  | _ => True

/-- Correct core rule instances, including their contexts and side conditions. -/
inductive CoreStep : CoreRule → List Sequent → Sequent → Prop where
  -- Identity with arbitrary side contexts.
  | identity (r g d) (x a) : CoreStep (.identity x a) []
      ⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩
  -- Falsity initial sequent.
  | falsumLeft (r g d) (x) : CoreStep (.falsumLeft x) []
      ⟨r, ⟨x, .falsum⟩ ::ₘ g, d⟩
  -- Truth initial sequent.
  | verumRight (r g d) (x) : CoreStep (.verumRight x) []
      ⟨r, g, ⟨x, .verum⟩ ::ₘ d⟩
  -- Truth-left instance.
  | verumLeft (r g d) (x) : CoreStep (.verumLeft x)
      [⟨r, g, d⟩] ⟨r, ⟨x, .verum⟩ ::ₘ g, d⟩
  -- Falsity-right instance.
  | falsumRight (r g d) (x) : CoreStep (.falsumRight x)
      [⟨r, g, d⟩] ⟨r, g, ⟨x, .falsum⟩ ::ₘ d⟩
  -- Negation-left instance.
  | negLeft (r g d) (x a) : CoreStep (.negLeft x a)
      [⟨r, g, ⟨x, a⟩ ::ₘ d⟩] ⟨r, ⟨x, .neg a⟩ ::ₘ g, d⟩
  -- Negation-right instance.
  | negRight (r g d) (x a) : CoreStep (.negRight x a)
      [⟨r, ⟨x, a⟩ ::ₘ g, d⟩] ⟨r, g, ⟨x, .neg a⟩ ::ₘ d⟩
  -- Conjunction-left instance.
  | conjLeft (r g d) (x a b) : CoreStep (.conjLeft x a b)
      [⟨r, ⟨x, a⟩ ::ₘ ⟨x, b⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .conj a b⟩ ::ₘ g, d⟩
  -- Conjunction-right instance.
  | conjRight (r g d) (x a b) : CoreStep (.conjRight x a b)
      [⟨r, g, ⟨x, a⟩ ::ₘ d⟩, ⟨r, g, ⟨x, b⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .conj a b⟩ ::ₘ d⟩
  -- Disjunction-left instance.
  | disjLeft (r g d) (x a b) : CoreStep (.disjLeft x a b)
      [⟨r, ⟨x, a⟩ ::ₘ g, d⟩, ⟨r, ⟨x, b⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .disj a b⟩ ::ₘ g, d⟩
  -- Disjunction-right instance.
  | disjRight (r g d) (x a b) : CoreStep (.disjRight x a b)
      [⟨r, g, ⟨x, a⟩ ::ₘ ⟨x, b⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .disj a b⟩ ::ₘ d⟩
  -- Context-sharing classical implication-left instance.
  | impLeft (r g d) (x a b) : CoreStep (.impLeft x a b)
      [⟨r, g, ⟨x, a⟩ ::ₘ d⟩, ⟨r, ⟨x, b⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .imp a b⟩ ::ₘ g, d⟩
  -- Implication-right instance.
  | impRight (r g d) (x a b) : CoreStep (.impRight x a b)
      [⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, b⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .imp a b⟩ ::ₘ d⟩
  -- Biconditional-left instance via both implications.
  | iffLeft (r g d) (x a b) : CoreStep (.iffLeft x a b)
      [⟨r, ⟨x, .imp a b⟩ ::ₘ ⟨x, .imp b a⟩ ::ₘ g, d⟩]
      ⟨r, ⟨x, .iff a b⟩ ::ₘ g, d⟩
  -- Biconditional-right instance.
  | iffRight (r g d) (x a b) : CoreStep (.iffRight x a b)
      [⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, b⟩ ::ₘ d⟩,
       ⟨r, ⟨x, b⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩]
      ⟨r, g, ⟨x, .iff a b⟩ ::ₘ d⟩
  -- Box-left retains the principal box and accessibility atom.
  | boxLeft (r g d) (x y a) : CoreStep (.boxLeft x y a)
      [⟨⟨x, y⟩ ::ₘ r, ⟨y, a⟩ ::ₘ ⟨x, .box a⟩ ::ₘ g, d⟩]
      ⟨⟨x, y⟩ ::ₘ r, ⟨x, .box a⟩ ::ₘ g, d⟩
  -- Eigenlabel is fresh in all three conclusion contexts.
  | boxRight (r g d) (x y a)
      (fresh : y ∉ (Sequent.mk r g (⟨x, .box a⟩ ::ₘ d)).labels) :
      CoreStep (.boxRight x y a)
        [⟨⟨x, y⟩ ::ₘ r, g, ⟨y, a⟩ ::ₘ d⟩]
        ⟨r, g, ⟨x, .box a⟩ ::ₘ d⟩

/-- Core rule data or data from a user-chosen extension language. -/
-- Parameterized rule tags for a portable deep embedding.
inductive Rule (Extension : Type) where
  -- Shared propositional/modal core tag.
  | core (rule : CoreRule)
  -- Extensible additional-rule payload.
  | extension (rule : Extension)
  -- Generated equality and printing, conditional on the payload.
  deriving DecidableEq, Repr

/-- A calculus explicitly specifies its permitted local inference steps. -/
-- Shallow tactics do not define an object-level calculus record.
structure Calculus (Extension : Type) where
  -- Local rule instances including arity and side conditions.
  step : Rule Extension → List Sequent → Sequent → Prop

/-- Extend the shared core with an independently specified rule family. -/
-- Explicit pointwise union of local rule families.
def Calculus.withCore {E : Type} (extra : E → List Sequent → Sequent → Prop) :
    Calculus E where
  step rule ps s := match rule with
    | .core r => CoreStep r ps s
    | .extension r => extra r ps s

/-- A certificate that a calculus includes the propositional core instances. -/
-- HOL: no deep counterpart; explicit inclusion restricted to propositional rule tags.
class HasPropositionalCore {E : Type} (C : Calculus E) : Prop where
  -- HOL: no counterpart; primitive propositional-rule availability.
  admitted : ∀ {r ps s}, r.IsPropositional → CoreStep r ps s → C.step (.core r) ps s

/-- A certificate that a calculus includes the standard box-left instances. -/
-- HOL: no deep counterpart; inclusion of one modal rule family.
class HasBoxLeft {E : Type} (C : Calculus E) : Prop where
  -- HOL: no counterpart; primitive box-left availability.
  admitted : ∀ {x y a ps s}, CoreStep (.boxLeft x y a) ps s →
    C.step (.core (.boxLeft x y a)) ps s

/-- A certificate that a calculus includes the standard box-right instances. -/
-- HOL: no deep counterpart; inclusion of one modal rule family, including freshness.
class HasBoxRight {E : Type} (C : Calculus E) : Prop where
  -- HOL: no counterpart; primitive box-right availability.
  admitted : ∀ {x y a ps s}, CoreStep (.boxRight x y a) ps s →
    C.step (.core (.boxRight x y a)) ps s

/-- Bundle all three standard core capabilities for ordinary extensions. -/
-- HOL: no deep counterpart; Lean convenience grouping of primitive rule inclusions.
class HasCore {E : Type} (C : Calculus E) : Prop where
  /-- Availability of the propositional family. -/
  -- HOL: no counterpart; first component of the standard core bundle.
  toHasPropositionalCore : HasPropositionalCore C
  /-- Availability of the standard box-left rule. -/
  -- HOL: no counterpart; second component of the standard core bundle.
  toHasBoxLeft : HasBoxLeft C
  /-- Availability of the standard box-right rule. -/
  -- HOL: no counterpart; third component of the standard core bundle.
  toHasBoxRight : HasBoxRight C

-- HOL: no counterpart; extract granular capabilities automatically from the bundle.
attribute [instance] HasCore.toHasPropositionalCore HasCore.toHasBoxLeft HasCore.toHasBoxRight

/-- The bundled capabilities include every standard core instance. -/
-- HOL: no counterpart; compatibility interface for full-core availability.
theorem HasCore.admitted {E : Type} {C : Calculus E} [HasCore C]
    {r ps s} (h : CoreStep r ps s) : C.step (.core r) ps s := by
  cases r <;> first
    | exact HasBoxLeft.admitted h
    | exact HasBoxRight.admitted h
    | exact HasPropositionalCore.admitted (by trivial) h

/-- Every explicitly core-extended calculus includes all three standard families. -/
-- HOL: no counterpart; bundled inclusion instance for the ordinary extension constructor.
instance {E : Type} (extra : E → List Sequent → Sequent → Prop) :
    HasCore (Calculus.withCore extra) where
  toHasPropositionalCore := ⟨fun _ h => h⟩
  toHasBoxLeft := ⟨fun h => h⟩
  toHasBoxRight := ⟨fun h => h⟩

/-- Reflexivity removes an auxiliary self-edge from the premise. -/
-- HOL: no deep counterpart; reflexivity is used by the shallow T tactics (`t_decid.ml`).
inductive ReflStep : Label → List Sequent → Sequent → Prop where
  -- The reflexive frame rule as an explicit step.
  | intro (r g d) (x) : ReflStep x [⟨⟨x, x⟩ ::ₘ r, g, d⟩] ⟨r, g, d⟩

/-- A certificate that a calculus permits the primitive reflexivity rule. -/
-- Inclusion hypothesis, distinct from admissibility.
class HasRefl (C : Calculus Label) : Prop where
  -- witness of reflexivity-step availability.
  admitted : ∀ {x ps s}, ReflStep x ps s → C.step (.extension x) ps s

/-- K has no extension steps, but shares T's raw rule-data type. -/
-- HOL: no deep counterpart; system K is treated by shallow tactics in `k_decid.ml`.
def K : Calculus Label := Calculus.withCore fun _ _ _ => False

/-- T extends the core by the reflexivity rule family. -/
-- HOL: no deep counterpart; system T is treated by shallow tactics in `t_decid.ml`.
def T : Calculus Label := Calculus.withCore ReflStep

/-- K includes the shared core. -/
-- Explicit instance avoids unfolding a calculus during class search.
instance : HasCore K :=
  inferInstanceAs (HasCore (Calculus.withCore (fun (_ : Label) _ _ => False)))

/-- T includes the shared core. -/
-- Explicit inclusion instance for T.
instance : HasCore T := inferInstanceAs (HasCore (Calculus.withCore ReflStep))

/-- The reflexivity family is available in T. -/
-- Primitive inclusion instance for T.
instance : HasRefl T where
  admitted h := h

/-- Raw finite trees; arity and rule correctness are checked separately. -/
-- Proposed object-level certificate datatype.
inductive ProofTree (Extension : Type) where
  -- Node records a conclusion, rule data, and ordered premises.
  | node (conclusion : Sequent) (rule : Rule Extension) (children : List (ProofTree Extension))

/-- Read the root sequent without assuming correctness of the tree. -/
-- Root projection on raw certificates.
def ProofTree.conclusion {E : Type} : ProofTree E → Sequent
  | .node s _ _ => s

/-- Height of a raw tree, with leaves at height one. -/
-- Proof-theoretic measure on explicit certificates.
def ProofTree.height {E : Type} : ProofTree E → Nat
  | .node _ _ ds => 1 + (ds.map ProofTree.height).foldr max 0

/-- Number of nodes of a raw tree. -/
-- Proof-theoretic size measure.
def ProofTree.nodes {E : Type} : ProofTree E → Nat
  | .node _ _ ds => 1 + (ds.map ProofTree.nodes).sum

/-- Every node is an allowed local step and all its children are valid. -/
-- Uniform object-level validity predicate.
inductive Valid {E : Type} (C : Calculus E) : ProofTree E → Prop where
  -- Validity includes both local correctness and every subtree.
  | node {s r ds} (step : C.step r (ds.map ProofTree.conclusion) s)
      (children : ∀ d ∈ ds, Valid C d) : Valid C (.node s r ds)

/-- Validity is characterized by the root step and all child validities. -/
-- Inversion lemma for the raw-tree validator.
theorem valid_node_iff {E : Type} {C : Calculus E} {s r ds} :
    Valid C (.node s r ds) ↔
      C.step r (ds.map ProofTree.conclusion) s ∧ ∀ d ∈ ds, Valid C d := by
  constructor
  · intro h; cases h with | node hs hc => exact ⟨hs, hc⟩
  · rintro ⟨hs, hc⟩; exact .node hs hc

/-- Local inclusion between two calculi's step relations. -/
-- Pointwise relation inclusion for modular extensions.
def Calculus.Included {E : Type} (C D : Calculus E) : Prop :=
  ∀ r ps s, C.step r ps s → D.step r ps s

/-- Compose calculi by permitting steps from either component. -/
-- Explicit union of local rule-instance relations.
def Calculus.union {E : Type} (C D : Calculus E) : Calculus E where
  step r ps s := C.step r ps s ∨ D.step r ps s

/-- The first component's steps are included in the union. -/
-- Local inclusion for modular composition.
theorem Calculus.included_union_left {E : Type} (C D : Calculus E) :
    C.Included (C.union D) := fun _ _ _ h => Or.inl h

/-- The second component's steps are included in the union. -/
-- Local inclusion for modular composition.
theorem Calculus.included_union_right {E : Type} (C D : Calculus E) :
    D.Included (C.union D) := fun _ _ _ h => Or.inr h

/-- Enlarging the step relation preserves the same raw certificate. -/
-- Generic monotonicity of tree validity.
theorem Valid.mono {E : Type} {C D : Calculus E} (inc : C.Included D)
    {d : ProofTree E} (h : Valid C d) : Valid D d := by
  induction h with
  | node hs _ ih => exact .node (inc _ _ _ hs) ih

/-- Every K step is also a T step. -/
-- Explicit inclusion of the two prototype rule relations.
theorem k_included_t : K.Included T := by
  intro r ps s h
  cases r with
  | core r => exact h
  | extension r => exact False.elim h

/-- A K-valid tree remains valid in T without changing the tree. -/
-- Specialization of validity monotonicity.
theorem Valid.k_to_t {d : ProofTree Label} (h : Valid K d) : Valid T d :=
  h.mono k_included_t

/-- Derivability means existence of a valid explicit tree with this root. -/
-- Existential judgment over object-level labelled trees.
def Derivable {E : Type} (C : Calculus E) (s : Sequent) : Prop :=
  ∃ d : ProofTree E, Valid C d ∧ d.conclusion = s

/-- Derivability is monotone under inclusion of local rule instances. -/
-- Existential consequence of raw-certificate monotonicity.
theorem Derivable.mono {E : Type} {C D : Calculus E} (inc : C.Included D)
    {s : Sequent} (h : Derivable C s) : Derivable D s := by
  obtain ⟨d, hd, hs⟩ := h
  exact ⟨d, hd.mono inc, hs⟩

/-- Assemble a valid leaf only from a permitted zero-premise step. -/
-- Certified raw-tree construction helper.
theorem Valid.leaf {E : Type} {C : Calculus E} {r s} (h : C.step r [] s) :
    Valid C (.node s r []) := .node h (by simp)

/-- Assemble a valid unary node from its local step and child certificate. -/
-- Certified unary construction helper.
theorem Valid.unary {E : Type} {C : Calculus E} {r s d}
    (h : C.step r [ProofTree.conclusion d] s) (hd : Valid C d) :
    Valid C (.node s r [d]) := .node h (by simpa using hd)

/-- Assemble a valid binary node from its step and both child certificates. -/
-- Explicit two-premise validity helper.
theorem Valid.binary {E : Type} {C : Calculus E} {r s d₁ d₂}
    (h : C.step r [ProofTree.conclusion d₁, ProofTree.conclusion d₂] s)
    (h₁ : Valid C d₁) (h₂ : Valid C d₂) :
    Valid C (.node s r [d₁, d₂]) := .node h (by simp_all)

/-- Generalized identity needs only the propositional core. -/
-- Generic class-based use of primitive rule inclusion.
theorem identity_valid {E : Type} (C : Calculus E) [HasPropositionalCore C]
    (r g d) (x : Label) (a : Form) :
    Valid C (.node ⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩
      (.core (.identity x a)) []) :=
  .leaf (HasPropositionalCore.admitted (by trivial) (.identity r g d x a))

/-- K never accepts a node tagged as an extension rule. -/
-- Negative certificate validation property.
theorem not_valid_k_extension (s : Sequent) (x : Label) (ds : List (ProofTree Label)) :
    ¬Valid K (.node s (.extension x) ds) := by
  intro h
  exact (valid_node_iff.mp h).1

/-- A box-right rule cannot reuse its source as its eigenlabel. -/
-- Rejection of an invalid eigenlabel instance.
theorem boxRight_source_ne {x y : Label} {a : Form} {ps s}
    (h : CoreStep (.boxRight x y a) ps s) : y ≠ x := by
  cases h with
  | boxRight r g d x y a fresh =>
    intro heq
    subst y
    apply fresh
    simp [Sequent.labels]


/-- Use an existing edge to expose the content of a boxed assumption. -/
-- Concrete box-left certificate with an identity leaf.
def boxUseTree {E : Type} (r : Multiset RelAtom) (x y : Label) (a : Form) :
    ProofTree E :=
  .node ⟨⟨x, y⟩ ::ₘ r, {⟨x, .box a⟩}, {⟨y, a⟩}⟩ (.core (.boxLeft x y a))
    [.node ⟨⟨x, y⟩ ::ₘ r, ⟨y, a⟩ ::ₘ {⟨x, .box a⟩}, {⟨y, a⟩}⟩
      (.core (.identity y a)) []]

/-- The box-left certificate needs propositional rules and box-left, but not box-right. -/
-- Class-polymorphic validation of an explicit modal tree.
theorem boxUseTree_valid {E : Type} (C : Calculus E)
    [HasPropositionalCore C] [HasBoxLeft C]
    (r : Multiset RelAtom) (x y : Label) (a : Form) :
    Valid C (boxUseTree r x y a) := by
  apply Valid.unary
  · apply HasBoxLeft.admitted
    simpa only [ProofTree.conclusion, Multiset.cons_zero] using
      CoreStep.boxLeft r 0 {⟨y, a⟩} x y a
  · exact identity_valid C (⟨x, y⟩ ::ₘ r) {⟨x, .box a⟩} 0 y a

/-- A box-right certificate for boxed identity, sharing the same raw syntax in K/T. -/
-- Explicit two-modal-step certificate.
def boxedIdentityTree {E : Type} (x y : Label) (a : Form) : ProofTree E :=
  .node ⟨0, {⟨x, .box a⟩}, {⟨x, .box a⟩}⟩ (.core (.boxRight x y a))
    [boxUseTree 0 x y a]

/-- Boxed identity is valid when the eigenlabel differs from the source. -/
-- Verifies box-right freshness in both formula contexts.
theorem boxedIdentityTree_valid {E : Type} (C : Calculus E)
    [HasPropositionalCore C] [HasBoxLeft C] [HasBoxRight C]
    (x y : Label) (a : Form) (fresh : y ≠ x) :
    Valid C (boxedIdentityTree x y a) := by
  apply Valid.unary
  · apply HasBoxRight.admitted
    apply CoreStep.boxRight
    simpa [Sequent.labels] using fresh
  · exact boxUseTree_valid C 0 x y a

/-- A reflexivity step turns box-left into a certificate for the T sequent. -/
-- Explicit reflexivity certificate over the common K/T tree type.
def reflexiveBoxTree (x : Label) (a : Form) : ProofTree Label :=
  .node ⟨0, {⟨x, .box a⟩}, {⟨x, a⟩}⟩ (.extension x) [boxUseTree 0 x x a]

/-- A generic use of propositional, box-left, and reflexivity availability. -/
-- Class-based validation of the reflexive box certificate.
theorem reflexiveBoxTree_valid (C : Calculus Label)
    [HasPropositionalCore C] [HasBoxLeft C] [HasRefl C]
    (x : Label) (a : Form) : Valid C (reflexiveBoxTree x a) := by
  apply Valid.unary
  · apply HasRefl.admitted
    simpa only [boxUseTree, ProofTree.conclusion] using
      ReflStep.intro 0 {⟨x, .box a⟩} {⟨x, a⟩} x
  · exact boxUseTree_valid C 0 x x a

/-- An explicit derivation of the T axiom at a label. -/
-- Raw labelled derivation of `□a → a`.
def tAxiomTree (x : Label) (a : Form) : ProofTree Label :=
  .node ⟨0, 0, {⟨x, .imp (.box a) a⟩}⟩ (.core (.impRight x (.box a) a))
    [reflexiveBoxTree x a]

/-- The T-axiom tree needs no box-right capability. -/
-- Generic certificate validation with rule-availability classes.
theorem tAxiomTree_valid (C : Calculus Label)
    [HasPropositionalCore C] [HasBoxLeft C] [HasRefl C]
    (x : Label) (a : Form) : Valid C (tAxiomTree x a) := by
  apply Valid.unary
  · exact HasPropositionalCore.admitted (by trivial) (.impRight 0 0 0 x (.box a) a)
  · exact reflexiveBoxTree_valid C x a

/-- This particular T-axiom certificate is invalid in K because it uses reflexivity. -/
-- Rejection of a certificate, not a K nonderivability theorem.
theorem tAxiomTree_not_valid_k (x : Label) (a : Form) :
    ¬Valid K (tAxiomTree x a) := by
  intro h
  have hc := (valid_node_iff.mp h).2 (reflexiveBoxTree x a) (by simp)
  exact not_valid_k_extension _ _ _ hc

/-- A box-right node with no premise cannot be a valid K certificate. -/
-- malformed arity is rejected by local rule validation.
theorem boxRight_leaf_not_valid_k (s : Sequent) (x y : Label) (a : Form) :
    ¬Valid K (.node s (.core (.boxRight x y a)) []) := by
  intro h
  have hs : CoreStep (.boxRight x y a) [] s := (valid_node_iff.mp h).1
  cases hs

/-- Conjunction-right combines two identity certificates using shared contexts. -/
-- Binary branching certificate in the shared propositional core.
def conjunctionTree {E : Type} (x : Label) (a : Form) : ProofTree E :=
  .node ⟨0, {⟨x, a⟩}, {⟨x, .conj a a⟩}⟩ (.core (.conjRight x a a))
    [.node ⟨0, {⟨x, a⟩}, {⟨x, a⟩}⟩ (.core (.identity x a)) [],
     .node ⟨0, {⟨x, a⟩}, {⟨x, a⟩}⟩ (.core (.identity x a)) []]

/-- Both conjunction branches need only propositional rule availability. -/
-- Verifies a genuine binary rule application.
theorem conjunctionTree_valid {E : Type} (C : Calculus E) [HasPropositionalCore C]
    (x : Label) (a : Form) : Valid C (conjunctionTree x a) := by
  apply Valid.binary
  · apply HasPropositionalCore.admitted (by trivial)
    simpa only [ProofTree.conclusion, Multiset.cons_zero] using
      CoreStep.conjRight 0 {⟨x, a⟩} 0 x a a
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

-- The same T-axiom certificate is rejected in K.
example : ¬Valid K (tAxiomTree 0 (.atom "p")) := tAxiomTree_not_valid_k 0 _

-- Structural measures compute on data without validity proofs.
example : (tAxiomTree 0 (.atom "p")).height = 4 ∧
    (tAxiomTree 0 (.atom "p")).nodes = 4 := by
  norm_num [tAxiomTree, reflexiveBoxTree, boxUseTree, ProofTree.height, ProofTree.nodes]


section CapabilityRegression

/-- A test calculus retaining T's rules except for standard box-right. -/
-- HOL: no counterpart; regression fixture for independence of the modal capabilities.
private def noBoxRight : Calculus Label where
  step rule ps s := match rule with
    | .core (.boxRight ..) => False
    | .core r => CoreStep r ps s
    | .extension x => ReflStep x ps s

-- HOL: no counterpart; the test calculus has propositional rules despite missing box-right.
local instance : HasPropositionalCore noBoxRight where
  admitted {r ps s} hp h := by
    cases r <;> first | exact h | exact False.elim hp

-- HOL: no counterpart; standard box-left remains available in the restricted test calculus.
local instance : HasBoxLeft noBoxRight where
  admitted h := h

-- HOL: no counterpart; reflexivity remains available independently of box-right.
local instance : HasRefl noBoxRight where
  admitted h := h

-- HOL: no counterpart; the propositional certificate works without full-core availability.
example : Valid noBoxRight (conjunctionTree 0 (.atom "p")) :=
  conjunctionTree_valid noBoxRight 0 _

-- HOL: no counterpart; T's axiom certificate does not require the missing box-right rule.
example : Valid noBoxRight (tAxiomTree 0 (.atom "p")) :=
  tAxiomTree_valid noBoxRight 0 _

-- HOL: no counterpart; the same calculus genuinely rejects use of standard box-right.
example : ¬Valid noBoxRight (boxedIdentityTree 0 1 (.atom "p")) := by
  intro h
  exact (valid_node_iff.mp h).1

end CapabilityRegression

end HOLMS.Labelled
