import Mathlib

/-!
# Syntax and semantics of modal logic

This module defines modal formulas, Kripke semantics, subformulas, and
bisimulations.
-/

namespace HOLMS

noncomputable local instance : Countable Char :=
  Function.Injective.countable (f := Char.val) fun _ _ h => Char.ext h

noncomputable local instance : Countable String :=
  Function.Injective.countable (f := fun s : String => s.toList) fun _ _ h =>
    String.toList_injective h

/-- Formulas of propositional modal logic. -/
inductive Form where
  | falsum : Form
  | verum : Form
  | atom : String → Form
  | neg : Form → Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form
  | imp : Form → Form → Form
  | iff : Form → Form → Form
  | box : Form → Form
  deriving DecidableEq, Repr, Countable

namespace Form

/-- Possibility, defined as `¬□¬p`. -/
def diam (p : Form) : Form := neg (box (neg p))

/-- The conjunction `□p ∧ p`. -/
def dotbox (p : Form) : Form := conj (box p) p

/-- Return the argument of a negation, when there is one. -/
def unneg? : Form → Option Form
  | neg p => some p
  | _ => none

/-- Return the argument of a box, when there is one. -/
def unbox? : Form → Option Form
  | box p => some p
  | _ => none

/-- The terminal constituents of a formula (`False`, `True`, and atoms). -/
def atomicals : Form → Finset Form
  | falsum => {falsum}
  | verum => {verum}
  | atom a => {atom a}
  | neg p | box p => atomicals p
  | conj p q | disj p q | imp p q | iff p q => atomicals p ∪ atomicals q

/-- The depth of a formula's syntax tree. -/
def depth : Form → ℕ
  | falsum | verum | atom _ => 0
  | neg p | box p => depth p + 1
  | conj p q | disj p q | imp p q | iff p q => max (depth p) (depth q) + 1

/-- The type of modal formulas is countable. -/
theorem countable : Countable Form := inferInstance

/-- `Minor p q` means that `p` is an immediate constituent of `q`. -/
inductive Minor : Form → Form → Prop where
  | neg (p : Form) : Minor p (.neg p)
  | conjLeft (p q : Form) : Minor p (.conj p q)
  | conjRight (p q : Form) : Minor q (.conj p q)
  | disjLeft (p q : Form) : Minor p (.disj p q)
  | disjRight (p q : Form) : Minor q (.disj p q)
  | impLeft (p q : Form) : Minor p (.imp p q)
  | impRight (p q : Form) : Minor q (.imp p q)
  | iffLeft (p q : Form) : Minor p (.iff p q)
  | iffRight (p q : Form) : Minor q (.iff p q)
  | box (p : Form) : Minor p (.box p)

/-- `Subformula p q` is the reflexive-transitive closure of `Minor`. -/
inductive Subformula : Form → Form → Prop where
  | refl (p : Form) : Subformula p p
  | tail {p q r : Form} : Subformula p q → Minor q r → Subformula p r

@[simp] theorem not_minor_falsum {p : Form} : ¬Minor p falsum := by
  intro h
  cases h

@[simp] theorem not_minor_verum {p : Form} : ¬Minor p verum := by
  intro h
  cases h

@[simp] theorem not_minor_atom {p : Form} {a : String} : ¬Minor p (atom a) := by
  intro h
  cases h

@[simp] theorem minor_neg_iff {p q : Form} : Minor p (neg q) ↔ p = q := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .neg _

@[simp] theorem minor_conj_iff {p q r : Form} :
    Minor p (conj q r) ↔ p = q ∨ p = r := by
  constructor
  · intro h
    cases h with
    | conjLeft => exact Or.inl rfl
    | conjRight => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact .conjLeft _ _
    · exact .conjRight _ _

@[simp] theorem minor_disj_iff {p q r : Form} :
    Minor p (disj q r) ↔ p = q ∨ p = r := by
  constructor
  · intro h
    cases h with
    | disjLeft => exact Or.inl rfl
    | disjRight => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact .disjLeft _ _
    · exact .disjRight _ _

@[simp] theorem minor_imp_iff {p q r : Form} :
    Minor p (imp q r) ↔ p = q ∨ p = r := by
  constructor
  · intro h
    cases h with
    | impLeft => exact Or.inl rfl
    | impRight => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact .impLeft _ _
    · exact .impRight _ _

@[simp] theorem minor_iff_iff {p q r : Form} :
    Minor p (iff q r) ↔ p = q ∨ p = r := by
  constructor
  · intro h
    cases h with
    | iffLeft => exact Or.inl rfl
    | iffRight => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact .iffLeft _ _
    · exact .iffRight _ _

@[simp] theorem minor_box_iff {p q : Form} : Minor p (box q) ↔ p = q := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .box _

/-- Every immediate constituent is a subformula. -/
theorem Minor.subformula {p q : Form} (h : Minor p q) : Subformula p q :=
  .tail (.refl p) h

/-- Transitivity of the subformula relation. -/
theorem Subformula.trans {p q r : Form} (hpq : Subformula p q)
    (hqr : Subformula q r) : Subformula p r := by
  induction hqr with
  | refl => exact hpq
  | tail _ hminor ih => exact .tail ih hminor

/-- Append one immediate-constituent step to a subformula derivation. -/
theorem Subformula.trans_minor {p q r : Form} (hpq : Subformula p q)
    (hqr : Minor q r) : Subformula p r := .tail hpq hqr

/-- Prepend one immediate-constituent step to a subformula derivation. -/
theorem Minor.trans_subformula {p q r : Form} (hpq : Minor p q)
    (hqr : Subformula q r) : Subformula p r := hpq.subformula.trans hqr

/-- A subformula is the formula itself or reaches an immediate constituent. -/
theorem subformula_cases_tail_iff {p q : Form} :
    Subformula p q ↔ p = q ∨ ∃ r, Subformula p r ∧ Minor r q := by
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | tail hp hr => exact Or.inr ⟨_, hp, hr⟩
  · rintro (rfl | ⟨r, hpr, hrq⟩)
    · exact .refl _
    · exact .tail hpr hrq

/-- A nontrivial subformula derivation begins with an immediate constituent. -/
theorem subformula_cases_head_iff {p q : Form} :
    Subformula p q ↔ p = q ∨ ∃ r, Minor p r ∧ Subformula r q := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail q r hp hqr ih =>
        rcases ih with hpq | ⟨s, hps, hsq⟩
        · subst q
          exact Or.inr ⟨r, hqr, .refl r⟩
        · exact Or.inr ⟨s, hps, .tail hsq hqr⟩
  · rintro (rfl | ⟨r, hpr, hrq⟩)
    · exact .refl _
    · exact hpr.trans_subformula hrq

@[simp] theorem subformula_falsum_iff {p : Form} :
    Subformula p falsum ↔ p = falsum := by
  rw [subformula_cases_tail_iff]
  simp

@[simp] theorem subformula_verum_iff {p : Form} :
    Subformula p verum ↔ p = verum := by
  rw [subformula_cases_tail_iff]
  simp

@[simp] theorem subformula_atom_iff {p : Form} {a : String} :
    Subformula p (atom a) ↔ p = atom a := by
  rw [subformula_cases_tail_iff]
  simp

@[simp] theorem subformula_neg_iff {p q : Form} :
    Subformula p (neg q) ↔ p = neg q ∨ Subformula p q := by
  rw [subformula_cases_tail_iff]
  simp

@[simp] theorem subformula_conj_iff {p q r : Form} :
    Subformula p (conj q r) ↔
      p = conj q r ∨ Subformula p q ∨ Subformula p r := by
  rw [subformula_cases_tail_iff]
  simp only [minor_conj_iff]
  aesop

@[simp] theorem subformula_disj_iff {p q r : Form} :
    Subformula p (disj q r) ↔
      p = disj q r ∨ Subformula p q ∨ Subformula p r := by
  rw [subformula_cases_tail_iff]
  simp only [minor_disj_iff]
  aesop

@[simp] theorem subformula_imp_iff {p q r : Form} :
    Subformula p (imp q r) ↔
      p = imp q r ∨ Subformula p q ∨ Subformula p r := by
  rw [subformula_cases_tail_iff]
  simp only [minor_imp_iff]
  aesop

@[simp] theorem subformula_iff_iff {p q r : Form} :
    Subformula p (iff q r) ↔
      p = iff q r ∨ Subformula p q ∨ Subformula p r := by
  rw [subformula_cases_tail_iff]
  simp only [minor_iff_iff]
  aesop

@[simp] theorem subformula_box_iff {p q : Form} :
    Subformula p (box q) ↔ p = box q ∨ Subformula p q := by
  rw [subformula_cases_tail_iff]
  simp

theorem of_subformula_neg {p q : Form} (h : Subformula (neg p) q) :
    Subformula p q := (Minor.neg p).trans_subformula h

theorem of_subformula_conj_left {p₁ p₂ q : Form}
    (h : Subformula (conj p₁ p₂) q) : Subformula p₁ q :=
  (Minor.conjLeft p₁ p₂).trans_subformula h

theorem of_subformula_conj_right {p₁ p₂ q : Form}
    (h : Subformula (conj p₁ p₂) q) : Subformula p₂ q :=
  (Minor.conjRight p₁ p₂).trans_subformula h

theorem of_subformula_disj_left {p₁ p₂ q : Form}
    (h : Subformula (disj p₁ p₂) q) : Subformula p₁ q :=
  (Minor.disjLeft p₁ p₂).trans_subformula h

theorem of_subformula_disj_right {p₁ p₂ q : Form}
    (h : Subformula (disj p₁ p₂) q) : Subformula p₂ q :=
  (Minor.disjRight p₁ p₂).trans_subformula h

theorem of_subformula_imp_left {p₁ p₂ q : Form}
    (h : Subformula (imp p₁ p₂) q) : Subformula p₁ q :=
  (Minor.impLeft p₁ p₂).trans_subformula h

theorem of_subformula_imp_right {p₁ p₂ q : Form}
    (h : Subformula (imp p₁ p₂) q) : Subformula p₂ q :=
  (Minor.impRight p₁ p₂).trans_subformula h

theorem of_subformula_iff_left {p₁ p₂ q : Form}
    (h : Subformula (iff p₁ p₂) q) : Subformula p₁ q :=
  (Minor.iffLeft p₁ p₂).trans_subformula h

theorem of_subformula_iff_right {p₁ p₂ q : Form}
    (h : Subformula (iff p₁ p₂) q) : Subformula p₂ q :=
  (Minor.iffRight p₁ p₂).trans_subformula h

theorem of_subformula_box {p q : Form} (h : Subformula (box p) q) :
    Subformula p q := (Minor.box p).trans_subformula h

/-- The finite set of all subformulas of a formula. -/
def subformulas : Form → Finset Form
  | falsum => {falsum}
  | verum => {verum}
  | atom a => {atom a}
  | neg p => insert (neg p) p.subformulas
  | conj p q => insert (conj p q) (p.subformulas ∪ q.subformulas)
  | disj p q => insert (disj p q) (p.subformulas ∪ q.subformulas)
  | imp p q => insert (imp p q) (p.subformulas ∪ q.subformulas)
  | iff p q => insert (iff p q) (p.subformulas ∪ q.subformulas)
  | box p => insert (box p) p.subformulas

@[simp] theorem mem_subformulas_iff {p q : Form} :
    q ∈ p.subformulas ↔ Subformula q p := by
  induction p with
  | falsum => simp [subformulas]
  | verum => simp [subformulas]
  | atom => simp [subformulas]
  | neg p ih => simp [subformulas, ih]
  | conj p q ihp ihq => simp [subformulas, ihp, ihq]
  | disj p q ihp ihq => simp [subformulas, ihp, ihq]
  | imp p q ihp ihq => simp [subformulas, ihp, ihq]
  | iff p q ihp ihq => simp [subformulas, ihp, ihq]
  | box p ih => simp [subformulas, ih]

/-- Every formula has only finitely many subformulas. -/
theorem finite_subformulas (p : Form) : Set.Finite {q | Subformula q p} := by
  have h : {q | Subformula q p} = (p.subformulas : Set Form) := by
    ext q
    simp
  rw [h]
  exact p.subformulas.finite_toSet

/-- The subsets of the subformulas and their negations form a finite set. -/
theorem finite_subsets_subformulas (p : Form) :
    Set.Finite {A : Set Form |
      A ⊆ {q | Subformula q p} ∪ neg '' {q | Subformula q p}} := by
  apply Set.Finite.finite_subsets
  exact (finite_subformulas p).union ((finite_subformulas p).image neg)

/-- A duplicate-free list enumerating exactly the subformulas of `p`. -/
theorem subformula_list (p : Form) :
    ∃ xs : List Form, xs.Nodup ∧ ∀ q, q ∈ xs ↔ Subformula q p := by
  refine ⟨p.subformulas.toList, p.subformulas.nodup_toList, ?_⟩
  intro q
  simp

end Form

/-- A Kripke frame over a type of worlds. -/
structure Frame (W : Type*) where
  worlds : Set W
  rel : W → W → Prop

/-- A valuation assigns to each atom the worlds where it holds. -/
abbrev Valuation (W : Type*) := String → W → Prop

/-- A Kripke model is a frame equipped with a valuation. -/
structure Model (W : Type*) where
  frame : Frame W
  valuation : Valuation W

namespace Form

/-- Kripke satisfaction of a modal formula at a world. -/
def holds {W : Type*} (frame : Frame W) (valuation : Valuation W) :
    Form → W → Prop
  | falsum, _ => False
  | verum, _ => True
  | atom a, w => valuation a w
  | neg p, w => ¬holds frame valuation p w
  | conj p q, w => holds frame valuation p w ∧ holds frame valuation q w
  | disj p q, w => holds frame valuation p w ∨ holds frame valuation q w
  | imp p q, w => holds frame valuation p w → holds frame valuation q w
  | iff p q, w => holds frame valuation p w ↔ holds frame valuation q w
  | box p, w => ∀ w', w' ∈ frame.worlds → frame.rel w w' →
      holds frame valuation p w'

/-- Satisfaction of a formula in every model and world based on a frame. -/
def holdsIn {W : Type*} (frame : Frame W) (p : Form) : Prop :=
  ∀ valuation w, w ∈ frame.worlds → holds frame valuation p w

/-- Validity of a formula in a class of frames. -/
def Valid {W : Type*} (frames : Set (Frame W)) (p : Form) : Prop :=
  ∀ frame, frame ∈ frames → holdsIn frame p

/-- `holdsIn` expressed through the public frame projections. -/
theorem holdsIn_iff {W : Type*} (frame : Frame W) (p : Form) :
    holdsIn frame p ↔
      ∀ valuation w, w ∈ frame.worlds → holds frame valuation p w := Iff.rfl

/-- Formula interpretations range over all predicates on the worlds. -/
theorem holds_forall_iff {W : Type*} (frame : Frame W)
    (P : (W → Prop) → Prop) :
    (∀ p valuation, P (holds frame valuation p)) ↔ ∀ U, P U := by
  constructor
  · intro h U
    simpa [holds] using h (atom "") (fun _ => U)
  · intro h p valuation
    exact h (holds frame valuation p)

end Form

namespace ModalNotation

scoped notation "⊥ₘ" => Form.falsum
scoped notation "⊤ₘ" => Form.verum
scoped prefix:max "¬ " => Form.neg
scoped prefix:max "□ " => Form.box
scoped prefix:max "◇ " => Form.diam
scoped prefix:max "⊡ " => Form.dotbox
scoped infixr:70 " ⋏ " => Form.conj
scoped infixr:65 " ⋎ " => Form.disj
scoped infixr:60 " ⟶ " => Form.imp
scoped infixr:55 " ⟷ " => Form.iff
scoped infix:50 " ⊑ " => Form.Subformula
scoped infix:45 " ⊧ₘ " => Form.Valid

end ModalNotation

/-- The local clauses that a relation must satisfy at related worlds. -/
structure BisimulationAt {W₁ W₂ : Type*} (M₁ : Model W₁) (M₂ : Model W₂)
    (Z : W₁ → W₂ → Prop) (w₁ : W₁) (w₂ : W₂) : Prop where
  world₁ : w₁ ∈ M₁.frame.worlds
  world₂ : w₂ ∈ M₂.frame.worlds
  atoms : ∀ a, M₁.valuation a w₁ ↔ M₂.valuation a w₂
  forth : ∀ {w₁'}, M₁.frame.rel w₁ w₁' →
    ∃ w₂', w₂' ∈ M₂.frame.worlds ∧ Z w₁' w₂' ∧ M₂.frame.rel w₂ w₂'
  back : ∀ {w₂'}, M₂.frame.rel w₂ w₂' →
    ∃ w₁', w₁' ∈ M₁.frame.worlds ∧ Z w₁' w₂' ∧ M₁.frame.rel w₁ w₁'

/-- A bisimulation between two Kripke models. -/
def Bisimulation {W₁ W₂ : Type*} (M₁ : Model W₁) (M₂ : Model W₂)
    (Z : W₁ → W₂ → Prop) : Prop :=
  ∀ ⦃w₁ w₂⦄, Z w₁ w₂ → BisimulationAt M₁ M₂ Z w₁ w₂

namespace Bisimulation

/-- Bisimulations preserve truth of every modal formula. -/
theorem holds_iff {W₁ W₂ : Type*} {M₁ : Model W₁} {M₂ : Model W₂}
    {Z : W₁ → W₂ → Prop} (hZ : Bisimulation M₁ M₂ Z) {p : Form}
    {w₁ : W₁} {w₂ : W₂} (hz : Z w₁ w₂) :
    p.holds M₁.frame M₁.valuation w₁ ↔
      p.holds M₂.frame M₂.valuation w₂ := by
  induction p generalizing w₁ w₂ with
  | falsum => simp [Form.holds]
  | verum => simp [Form.holds]
  | atom a => exact (hZ hz).atoms a
  | neg p ih => simp only [Form.holds, ih hz]
  | conj p q ihp ihq => simp only [Form.holds, ihp hz, ihq hz]
  | disj p q ihp ihq => simp only [Form.holds, ihp hz, ihq hz]
  | imp p q ihp ihq => simp only [Form.holds, ihp hz, ihq hz]
  | iff p q ihp ihq => simp only [Form.holds, ihp hz, ihq hz]
  | box p ih =>
      constructor
      · intro hp w₂' hw₂' hr₂
        obtain ⟨w₁', hw₁', hz', hr₁⟩ := (hZ hz).back hr₂
        exact (ih hz').mp (hp w₁' hw₁' hr₁)
      · intro hp w₁' hw₁' hr₁
        obtain ⟨w₂', hw₂', hz', hr₂⟩ := (hZ hz).forth hr₁
        exact (ih hz').mpr (hp w₂' hw₂' hr₂)

end Bisimulation

/-- Two pointed models are bisimilar when some bisimulation relates them. -/
def Bisimilar {W₁ W₂ : Type*} (M₁ : Model W₁) (M₂ : Model W₂)
    (w₁ : W₁) (w₂ : W₂) : Prop :=
  ∃ Z, Bisimulation M₁ M₂ Z ∧ Z w₁ w₂

namespace Bisimilar

theorem mem_worlds {W₁ W₂ : Type*} {M₁ : Model W₁} {M₂ : Model W₂}
    {w₁ : W₁} {w₂ : W₂} (h : Bisimilar M₁ M₂ w₁ w₂) :
    w₁ ∈ M₁.frame.worlds ∧ w₂ ∈ M₂.frame.worlds := by
  obtain ⟨Z, hZ, hz⟩ := h
  exact ⟨(hZ hz).world₁, (hZ hz).world₂⟩

theorem holds_iff {W₁ W₂ : Type*} {M₁ : Model W₁} {M₂ : Model W₂}
    {w₁ : W₁} {w₂ : W₂} (h : Bisimilar M₁ M₂ w₁ w₂) (p : Form) :
    p.holds M₁.frame M₁.valuation w₁ ↔
      p.holds M₂.frame M₂.valuation w₂ := by
  obtain ⟨Z, hZ, hz⟩ := h
  exact hZ.holds_iff hz

end Bisimilar

/-- Frame validity transfers backwards along pointwise bisimilar models. -/
theorem Form.holdsIn_of_bisimilar {W₁ W₂ : Type*} {f₁ : Frame W₁}
    {f₂ : Frame W₂}
    (h : ∀ V₁ w₁, ∃ V₂ w₂,
      Bisimilar ⟨f₁, V₁⟩ ⟨f₂, V₂⟩ w₁ w₂)
    {p : Form} (hp : p.holdsIn f₂) : p.holdsIn f₁ := by
  intro V₁ w₁ _
  obtain ⟨V₂, w₂, hbis⟩ := h V₁ w₁
  exact (hbis.holds_iff p).mpr (hp V₂ w₂ hbis.mem_worlds.2)

/-- Class validity transfers along pointwise bisimilar models. -/
theorem Form.valid_of_bisimilar {W₁ W₂ : Type*} {L₁ : Set (Frame W₁)}
    {L₂ : Set (Frame W₂)}
    (h : ∀ f₁, f₁ ∈ L₁ → ∀ V₁ w₁, w₁ ∈ f₁.worlds →
      ∃ f₂, f₂ ∈ L₂ ∧ ∃ V₂ w₂,
        Bisimilar ⟨f₁, V₁⟩ ⟨f₂, V₂⟩ w₁ w₂)
    {p : Form} (hp : p.Valid L₂) : p.Valid L₁ := by
  intro f₁ hf₁ V₁ w₁ hw₁
  obtain ⟨f₂, hf₂, V₂, w₂, hbis⟩ := h f₁ hf₁ V₁ w₁ hw₁
  exact (hbis.holds_iff p).mpr (hp f₂ hf₂ V₂ w₂ hbis.mem_worlds.2)

end HOLMS
