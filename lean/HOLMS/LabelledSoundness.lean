import HOLMS.Labelled
import HOLMS.AdHocCorrespondence

/-!
# Kripke soundness of labelled sequent calculi

This module interprets labelled sequents in the Kripke semantics of
`HOLMS.Modal`. It proves local soundness of the reusable primitive rule
families, shows that sound calculi are closed under pointwise union, and lifts
local soundness to valid proof trees and derivability. Individual systems
specialize these results in `HOLMS.LabelledK`, `HOLMS.LabelledT`, and
`HOLMS.LabelledB`.

The development is specific to the Lean deep embedding of labelled calculi;
it has no direct HOL Light counterpart.
-/

namespace HOLMS.Labelled

/-- A semantic interpretation of syntactic labels as Kripke worlds. -/
-- HOL: no direct counterpart; semantic infrastructure for the Lean labelled calculus.
abbrev LabelAssignment (W : Type*) := Label → W

namespace LabelAssignment

/-- Every label is interpreted by a designated world of the frame. -/
-- HOL: no direct counterpart; semantic infrastructure for the Lean labelled calculus.
def Respects {W : Type*} (frame : Frame W) (assignment : LabelAssignment W) : Prop :=
  ∀ x, assignment x ∈ frame.worlds

/-- Updating one label with a designated world preserves respect for a frame. -/
-- HOL: no direct counterpart; helper for soundness of the box-right rule.
theorem update_respects {W : Type*} {frame : Frame W}
    {assignment : LabelAssignment W} (hassignment : assignment.Respects frame)
    (x : Label) {w : W} (hw : w ∈ frame.worlds) :
    Respects frame (Function.update assignment x w) := by
  intro y
  by_cases h : y = x
  · simp [h, hw]
  · simpa [Function.update, h] using hassignment y

end LabelAssignment

/-- Truth of a labelled formula under a label assignment. -/
-- HOL: no direct counterpart; interprets the Lean labelled-formula datatype.
def LFormula.Holds {W : Type*} (frame : Frame W) (valuation : Valuation W)
    (assignment : LabelAssignment W) (formula : LFormula) : Prop :=
  Form.holds frame valuation formula.formula (assignment formula.label)

/-- Truth of a syntactic accessibility atom under a label assignment. -/
-- HOL: no direct counterpart; interprets the Lean relational-atom datatype.
def RelAtom.Holds {W : Type*} (frame : Frame W)
    (assignment : LabelAssignment W) (atom : RelAtom) : Prop :=
  frame.rel (assignment atom.source) (assignment atom.target)

/-- A Kripke counterexample to a labelled sequent. -/
-- HOL: no direct counterpart; semantic infrastructure for the Lean labelled calculus.
structure Sequent.Counterexample {W : Type*} (frame : Frame W)
    (valuation : Valuation W) (assignment : LabelAssignment W) (s : Sequent) : Prop where
  /-- Every relational assumption is true. -/
  -- HOL: no direct counterpart; relational clause of a labelled counterexample.
  relations : ∀ atom ∈ s.relations, atom.Holds frame assignment
  /-- Every formula in the antecedent is true. -/
  -- HOL: no direct counterpart; antecedent clause of a labelled counterexample.
  left : ∀ formula ∈ s.left, formula.Holds frame valuation assignment
  /-- Every formula in the succedent is false. -/
  -- HOL: no direct counterpart; succedent clause of a labelled counterexample.
  right : ∀ formula ∈ s.right, ¬formula.Holds frame valuation assignment

/-- Semantic validity of a labelled sequent on one Kripke frame. -/
-- HOL: no direct counterpart; semantic validity for the Lean labelled calculus.
def Sequent.ValidOn {W : Type*} (frame : Frame W) (s : Sequent) : Prop :=
  ∀ valuation assignment, assignment.Respects frame →
    ¬s.Counterexample frame valuation assignment

namespace RuleSchema

/-- A rule schema is sound on a frame when validity of all premises implies
validity of its conclusion for every accepted local instance. -/
-- HOL: no direct counterpart; local soundness interface for the Lean labelled calculus.
def SoundOn {W : Type*} (frame : Frame W) (schema : RuleSchema) : Prop :=
  ∀ args premises conclusion, schema args premises conclusion →
    (∀ premise ∈ premises, premise.ValidOn frame) → conclusion.ValidOn frame

end RuleSchema

namespace Calculus

/-- Every local instance accepted by a calculus is sound on the frame. -/
-- HOL: no direct counterpart; compositional soundness interface for the Lean labelled calculus.
def SoundOn {W : Type*} (frame : Frame W) (calculus : Calculus) : Prop :=
  ∀ name, (calculus name).SoundOn frame

/-- The empty calculus is sound on every frame. -/
-- HOL: no direct counterpart; empty case of compositional labelled soundness.
theorem soundOn_empty {W : Type*} (frame : Frame W) : empty.SoundOn frame := by
  intro name args premises conclusion step
  exact False.elim step

/-- A singleton calculus is sound whenever its registered schema is sound. -/
-- HOL: no direct counterpart; singleton case of compositional labelled soundness.
theorem soundOn_singleton {W : Type*} {frame : Frame W} {name : String}
    {schema : RuleSchema} (hsound : schema.SoundOn frame) :
    (singleton name schema).SoundOn frame := by
  intro candidate args premises conclusion step
  exact hsound args premises conclusion step.2

/-- Pointwise union preserves soundness. -/
-- HOL: no direct counterpart; compositional soundness of unions of labelled rules.
theorem SoundOn.union {W : Type*} {frame : Frame W} {left right : Calculus}
    (hleft : left.SoundOn frame) (hright : right.SoundOn frame) :
    (left.union right).SoundOn frame := by
  intro name args premises conclusion step
  rcases step with step | step
  · exact hleft name args premises conclusion step
  · exact hright name args premises conclusion step

/-- A finite pointwise union of sound calculi is sound. -/
-- HOL: no direct counterpart; finite compositional soundness for labelled rules.
theorem soundOn_unions {W : Type*} {frame : Frame W} {family : List Calculus}
    (hsound : ∀ calculus ∈ family, calculus.SoundOn frame) :
    (unions family).SoundOn frame := by
  induction family with
  | nil => exact soundOn_empty frame
  | cons first rest ih =>
      apply (hsound first (by simp)).union
      exact ih (by
        intro calculus hcalculus
        exact hsound calculus (by simp [hcalculus]))

end Calculus

/-! ## Local soundness of the primitive rule schemas -/

/-- Generalized identity is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `IdentityStep` in the Lean labelled calculus.
theorem IdentityStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame IdentityStep := by
  intro args premises conclusion step _ valuation assignment _ counterexample
  cases step with
  | identity r g d x a =>
      exact counterexample.right ⟨x, a⟩ (by simp)
        (counterexample.left ⟨x, a⟩ (by simp))

/-- Falsity-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `FalsumLeftStep` in the Lean labelled calculus.
theorem FalsumLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame FalsumLeftStep := by
  intro args premises conclusion step _ valuation assignment _ counterexample
  cases step with
  | falsumLeft r g d x =>
      exact counterexample.left ⟨x, .falsum⟩ (by simp)

/-- Truth-right is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `VerumRightStep` in the Lean labelled calculus.
theorem VerumRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame VerumRightStep := by
  intro args premises conclusion step _ valuation assignment _ counterexample
  cases step with
  | verumRight r g d x =>
      exact counterexample.right ⟨x, .verum⟩ (by simp) trivial

/-- Truth-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `VerumLeftStep` in the Lean labelled calculus.
theorem VerumLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame VerumLeftStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | verumLeft r g d x =>
      apply validPremises ⟨r, g, d⟩ (by simp) valuation assignment respects
      exact {
        relations := counterexample.relations
        left := fun formula hformula => counterexample.left formula (by simp [hformula])
        right := counterexample.right
      }

/-- Falsity-right is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `FalsumRightStep` in the Lean labelled calculus.
theorem FalsumRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame FalsumRightStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | falsumRight r g d x =>
      apply validPremises ⟨r, g, d⟩ (by simp) valuation assignment respects
      exact {
        relations := counterexample.relations
        left := counterexample.left
        right := fun formula hformula => counterexample.right formula (by simp [hformula])
      }

/-- Negation-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `NegLeftStep` in the Lean labelled calculus.
theorem NegLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame NegLeftStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | negLeft r g d x a =>
      apply validPremises ⟨r, g, ⟨x, a⟩ ::ₘ d⟩ (by simp) valuation assignment respects
      have hnotA : ¬Form.holds frame valuation a (assignment x) := by
        simpa [LFormula.Holds, Form.holds] using
          counterexample.left ⟨x, .neg a⟩ (by simp)
      exact {
        relations := counterexample.relations
        left := fun formula hformula => counterexample.left formula (by simp [hformula])
        right := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact hnotA
          · exact counterexample.right formula hformula
      }

/-- Negation-right is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `NegRightStep` in the Lean labelled calculus.
theorem NegRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame NegRightStep := by
  classical
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | negRight r g d x a =>
      apply validPremises ⟨r, ⟨x, a⟩ ::ₘ g, d⟩ (by simp) valuation assignment respects
      have hA : Form.holds frame valuation a (assignment x) := by
        apply Classical.byContradiction
        intro hnotA
        exact counterexample.right ⟨x, .neg a⟩ (by simp) (by
          simpa [LFormula.Holds, Form.holds] using hnotA)
      exact {
        relations := counterexample.relations
        left := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact hA
          · exact counterexample.left formula hformula
        right := fun formula hformula => counterexample.right formula (by simp [hformula])
      }

/-- Conjunction-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `ConjLeftStep` in the Lean labelled calculus.
theorem ConjLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame ConjLeftStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | conjLeft r g d x a b =>
      apply validPremises ⟨r, ⟨x, a⟩ ::ₘ ⟨x, b⟩ ::ₘ g, d⟩ (by simp)
        valuation assignment respects
      have hab := counterexample.left ⟨x, .conj a b⟩ (by simp)
      exact {
        relations := counterexample.relations
        left := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact hab.1
          · rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact hab.2
            · exact counterexample.left formula (by simp [hformula])
        right := counterexample.right
      }

/-- Conjunction-right is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `ConjRightStep` in the Lean labelled calculus.
theorem ConjRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame ConjRightStep := by
  classical
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | conjRight r g d x a b =>
      have hnotConj := counterexample.right ⟨x, .conj a b⟩ (by simp)
      by_cases ha : Form.holds frame valuation a (assignment x)
      · apply validPremises ⟨r, g, ⟨x, b⟩ ::ₘ d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := counterexample.left
          right := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · intro hb
              exact hnotConj ⟨ha, hb⟩
            · exact counterexample.right formula (by simp [hformula])
        }
      · apply validPremises ⟨r, g, ⟨x, a⟩ ::ₘ d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := counterexample.left
          right := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact ha
            · exact counterexample.right formula (by simp [hformula])
        }

/-- Disjunction-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `DisjLeftStep` in the Lean labelled calculus.
theorem DisjLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame DisjLeftStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | disjLeft r g d x a b =>
      rcases counterexample.left ⟨x, .disj a b⟩ (by simp) with ha | hb
      · apply validPremises ⟨r, ⟨x, a⟩ ::ₘ g, d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact ha
            · exact counterexample.left formula (by simp [hformula])
          right := counterexample.right
        }
      · apply validPremises ⟨r, ⟨x, b⟩ ::ₘ g, d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact hb
            · exact counterexample.left formula (by simp [hformula])
          right := counterexample.right
        }

/-- Disjunction-right is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `DisjRightStep` in the Lean labelled calculus.
theorem DisjRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame DisjRightStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | disjRight r g d x a b =>
      apply validPremises ⟨r, g, ⟨x, a⟩ ::ₘ ⟨x, b⟩ ::ₘ d⟩ (by simp)
        valuation assignment respects
      have hnotDisj := counterexample.right ⟨x, .disj a b⟩ (by simp)
      exact {
        relations := counterexample.relations
        left := counterexample.left
        right := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact fun ha => hnotDisj (Or.inl ha)
          · rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact fun hb => hnotDisj (Or.inr hb)
            · exact counterexample.right formula (by simp [hformula])
      }

/-- Implication-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `ImpLeftStep` in the Lean labelled calculus.
theorem ImpLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame ImpLeftStep := by
  classical
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | impLeft r g d x a b =>
      have himp := counterexample.left ⟨x, .imp a b⟩ (by simp)
      by_cases ha : Form.holds frame valuation a (assignment x)
      · apply validPremises ⟨r, ⟨x, b⟩ ::ₘ g, d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact himp ha
            · exact counterexample.left formula (by simp [hformula])
          right := counterexample.right
        }
      · apply validPremises ⟨r, g, ⟨x, a⟩ ::ₘ d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := fun formula hformula => counterexample.left formula (by simp [hformula])
          right := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact ha
            · exact counterexample.right formula hformula
        }

/-- Implication-right is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `ImpRightStep` in the Lean labelled calculus.
theorem ImpRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame ImpRightStep := by
  classical
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | impRight r g d x a b =>
      apply validPremises ⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, b⟩ ::ₘ d⟩ (by simp)
        valuation assignment respects
      have hnotImp := counterexample.right ⟨x, .imp a b⟩ (by simp)
      have ha : Form.holds frame valuation a (assignment x) := by
        by_contra hnotA
        exact hnotImp (fun hA => (hnotA hA).elim)
      exact {
        relations := counterexample.relations
        left := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact ha
          · exact counterexample.left formula hformula
        right := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact fun hb => hnotImp (fun _ => hb)
          · exact counterexample.right formula (by simp [hformula])
      }

/-- Biconditional-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `IffLeftStep` in the Lean labelled calculus.
theorem IffLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame IffLeftStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | iffLeft r g d x a b =>
      apply validPremises
        ⟨r, ⟨x, .imp a b⟩ ::ₘ ⟨x, .imp b a⟩ ::ₘ g, d⟩ (by simp)
        valuation assignment respects
      have hab := counterexample.left ⟨x, .iff a b⟩ (by simp)
      exact {
        relations := counterexample.relations
        left := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact hab.mp
          · rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact hab.mpr
            · exact counterexample.left formula (by simp [hformula])
        right := counterexample.right
      }

/-- Biconditional-right is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `IffRightStep` in the Lean labelled calculus.
theorem IffRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame IffRightStep := by
  classical
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | iffRight r g d x a b =>
      have hnotIff := counterexample.right ⟨x, .iff a b⟩ (by simp)
      by_cases ha : Form.holds frame valuation a (assignment x)
      · have hnotB : ¬Form.holds frame valuation b (assignment x) := by
          intro hb
          exact hnotIff ⟨fun _ => hb, fun _ => ha⟩
        apply validPremises ⟨r, ⟨x, a⟩ ::ₘ g, ⟨x, b⟩ ::ₘ d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact ha
            · exact counterexample.left formula hformula
          right := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact hnotB
            · exact counterexample.right formula (by simp [hformula])
        }
      · have hb : Form.holds frame valuation b (assignment x) := by
          by_contra hnotB
          exact hnotIff ⟨fun hA => (ha hA).elim, fun hB => (hnotB hB).elim⟩
        apply validPremises ⟨r, ⟨x, b⟩ ::ₘ g, ⟨x, a⟩ ::ₘ d⟩ (by simp)
          valuation assignment respects
        exact {
          relations := counterexample.relations
          left := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact hb
            · exact counterexample.left formula hformula
          right := fun formula hformula => by
            rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact ha
            · exact counterexample.right formula (by simp [hformula])
        }

/-- Box-left is sound on every frame. -/
-- HOL: no direct counterpart; soundness of `BoxLeftStep` in the Lean labelled calculus.
theorem BoxLeftStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame BoxLeftStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | boxLeft r g d x y a =>
      apply validPremises
        ⟨⟨x, y⟩ ::ₘ r, ⟨y, a⟩ ::ₘ ⟨x, .box a⟩ ::ₘ g, d⟩ (by simp)
        valuation assignment respects
      have hbox := counterexample.left ⟨x, .box a⟩ (by simp)
      have hedge := counterexample.relations ⟨x, y⟩ (by simp)
      have ha : Form.holds frame valuation a (assignment y) :=
        hbox (assignment y) (respects y) hedge
      exact {
        relations := counterexample.relations
        left := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · exact ha
          · rcases Multiset.mem_cons.mp hformula with rfl | hformula
            · exact hbox
            · exact counterexample.left formula (by simp [hformula])
        right := counterexample.right
      }

/-- Box-right is sound on every frame.  Its eigenlabel is reinterpreted as
the counterexample successor supplied by failure of the principal box. -/
-- HOL: no direct counterpart; soundness of `BoxRightStep` in the Lean labelled calculus.
theorem BoxRightStep.soundOn {W : Type*} (frame : Frame W) :
    RuleSchema.SoundOn frame BoxRightStep := by
  classical
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | boxRight r g d x y a fresh =>
      have hnotBox : ¬∀ w, w ∈ frame.worlds → frame.rel (assignment x) w →
          Form.holds frame valuation a w := by
        simpa [LFormula.Holds, Form.holds] using
          counterexample.right ⟨x, .box a⟩ (by simp)
      push Not at hnotBox
      obtain ⟨w, hw, hedge, hnotA⟩ := hnotBox
      let updated : LabelAssignment W := Function.update assignment y w
      have updatedRespects : updated.Respects frame :=
        LabelAssignment.update_respects respects y hw
      have hxy : x ≠ y := by
        intro h
        apply fresh
        simp [Sequent.labels, h]
      apply validPremises ⟨⟨x, y⟩ ::ₘ r, g, ⟨y, a⟩ ::ₘ d⟩ (by simp)
        valuation updated updatedRespects
      exact {
        relations := fun atom hatom => by
          rcases Multiset.mem_cons.mp hatom with rfl | hatom
          · simpa [RelAtom.Holds, updated, Function.update, hxy] using hedge
          · have hsource : atom.source ≠ y := by
              intro h
              apply fresh
              simp [Sequent.labels]
              exact Or.inr (Or.inl ⟨atom, hatom, Or.inl h.symm⟩)
            have htarget : atom.target ≠ y := by
              intro h
              apply fresh
              simp [Sequent.labels]
              exact Or.inr (Or.inl ⟨atom, hatom, Or.inr h.symm⟩)
            simpa [RelAtom.Holds, updated, Function.update, hsource, htarget] using
              counterexample.relations atom hatom
        left := fun formula hformula => by
          have hlabel : formula.label ≠ y := by
            intro h
            apply fresh
            simp [Sequent.labels]
            exact Or.inr (Or.inr (Or.inl ⟨formula, hformula, h⟩))
          simpa [LFormula.Holds, updated, Function.update, hlabel] using
            counterexample.left formula hformula
        right := fun formula hformula => by
          rcases Multiset.mem_cons.mp hformula with rfl | hformula
          · simpa [LFormula.Holds, updated, Function.update] using hnotA
          · have hlabel : formula.label ≠ y := by
              intro h
              apply fresh
              simp [Sequent.labels]
              exact Or.inr (Or.inr (Or.inr ⟨formula, hformula, h⟩))
            simpa [LFormula.Holds, updated, Function.update, hlabel] using
              counterexample.right formula (by simp [hformula])
      }

/-- The reflexivity rule is sound on frames whose accessibility relation is
reflexive on their designated worlds. -/
-- HOL: no direct counterpart; soundness of `ReflStep` in the Lean labelled calculus.
theorem ReflStep.soundOn {W : Type*} {frame : Frame W}
    (hrefl : REFLEXIVE frame.worlds frame.rel) :
    RuleSchema.SoundOn frame ReflStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | refl r g d x =>
      apply validPremises ⟨⟨x, x⟩ ::ₘ r, g, d⟩ (by simp)
        valuation assignment respects
      exact {
        relations := fun atom hatom => by
          rcases Multiset.mem_cons.mp hatom with rfl | hatom
          · exact hrefl (assignment x) (respects x)
          · exact counterexample.relations atom hatom
        left := counterexample.left
        right := counterexample.right
      }

/-- The symmetry rule is sound on frames whose accessibility relation is
symmetric on their designated worlds. -/
-- HOL: no direct labelled counterpart; soundness of `SymmStep` for the
-- `SYMMETRIC` frame condition used by `B_AX` (`b_completeness.ml`).
theorem SymmStep.soundOn {W : Type*} {frame : Frame W}
    (hsymm : SYMMETRIC frame.worlds frame.rel) :
    RuleSchema.SoundOn frame SymmStep := by
  intro args premises conclusion step validPremises valuation assignment respects counterexample
  cases step with
  | symm r g d x y =>
      apply validPremises ⟨⟨y, x⟩ ::ₘ ⟨x, y⟩ ::ₘ r, g, d⟩ (by simp)
        valuation assignment respects
      have hforward := counterexample.relations ⟨x, y⟩ (by simp)
      exact {
        relations := fun atom hatom => by
          rcases Multiset.mem_cons.mp hatom with rfl | hatom
          · exact hsymm (assignment x) (assignment y)
              (respects x) (respects y) hforward
          · exact counterexample.relations atom hatom
        left := counterexample.left
        right := counterexample.right
      }

/-! ## Soundness of the primitive calculi -/

/-- The singleton identity calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `IdentityStep.soundOn`.
theorem identityCalculus_soundOn {W : Type*} (frame : Frame W) :
    identityCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (IdentityStep.soundOn frame)

/-- The singleton falsity-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `FalsumLeftStep.soundOn`.
theorem falsumLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    falsumLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (FalsumLeftStep.soundOn frame)

/-- The singleton truth-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `VerumRightStep.soundOn`.
theorem verumRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    verumRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (VerumRightStep.soundOn frame)

/-- The singleton truth-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `VerumLeftStep.soundOn`.
theorem verumLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    verumLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (VerumLeftStep.soundOn frame)

/-- The singleton falsity-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `FalsumRightStep.soundOn`.
theorem falsumRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    falsumRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (FalsumRightStep.soundOn frame)

/-- The singleton negation-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `NegLeftStep.soundOn`.
theorem negLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    negLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (NegLeftStep.soundOn frame)

/-- The singleton negation-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `NegRightStep.soundOn`.
theorem negRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    negRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (NegRightStep.soundOn frame)

/-- The singleton conjunction-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `ConjLeftStep.soundOn`.
theorem conjLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    conjLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (ConjLeftStep.soundOn frame)

/-- The singleton conjunction-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `ConjRightStep.soundOn`.
theorem conjRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    conjRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (ConjRightStep.soundOn frame)

/-- The singleton disjunction-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `DisjLeftStep.soundOn`.
theorem disjLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    disjLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (DisjLeftStep.soundOn frame)

/-- The singleton disjunction-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `DisjRightStep.soundOn`.
theorem disjRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    disjRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (DisjRightStep.soundOn frame)

/-- The singleton implication-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `ImpLeftStep.soundOn`.
theorem impLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    impLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (ImpLeftStep.soundOn frame)

/-- The singleton implication-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `ImpRightStep.soundOn`.
theorem impRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    impRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (ImpRightStep.soundOn frame)

/-- The singleton biconditional-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `IffLeftStep.soundOn`.
theorem iffLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    iffLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (IffLeftStep.soundOn frame)

/-- The singleton biconditional-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `IffRightStep.soundOn`.
theorem iffRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    iffRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (IffRightStep.soundOn frame)

/-- The singleton box-left calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `BoxLeftStep.soundOn`.
theorem boxLeftCalculus_soundOn {W : Type*} (frame : Frame W) :
    boxLeftCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (BoxLeftStep.soundOn frame)

/-- The singleton box-right calculus is sound on every frame. -/
-- HOL: no direct counterpart; singleton packaging of `BoxRightStep.soundOn`.
theorem boxRightCalculus_soundOn {W : Type*} (frame : Frame W) :
    boxRightCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (BoxRightStep.soundOn frame)

/-- The singleton reflexivity calculus is sound on every reflexive frame. -/
-- HOL: no direct counterpart; singleton packaging of `ReflStep.soundOn`.
theorem reflCalculus_soundOn {W : Type*} {frame : Frame W}
    (hrefl : REFLEXIVE frame.worlds frame.rel) :
    reflCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (ReflStep.soundOn hrefl)

/-- The singleton symmetry calculus is sound on every symmetric frame. -/
-- HOL: no direct labelled counterpart; singleton packaging of `SymmStep.soundOn`.
theorem symmCalculus_soundOn {W : Type*} {frame : Frame W}
    (hsymm : SYMMETRIC frame.worlds frame.rel) :
    symmCalculus.SoundOn frame :=
  Calculus.soundOn_singleton (SymmStep.soundOn hsymm)

/-- The complete propositional calculus is sound on every frame. -/
-- HOL: no direct counterpart; composition of the fifteen propositional soundness results.
theorem propositionalCalculus_soundOn {W : Type*} (frame : Frame W) :
    propositionalCalculus.SoundOn frame := by
  simpa only [propositionalCalculus, Calculus.unions] using
    (identityCalculus_soundOn frame).union
      ((falsumLeftCalculus_soundOn frame).union
      ((verumRightCalculus_soundOn frame).union
      ((verumLeftCalculus_soundOn frame).union
      ((falsumRightCalculus_soundOn frame).union
      ((negLeftCalculus_soundOn frame).union
      ((negRightCalculus_soundOn frame).union
      ((conjLeftCalculus_soundOn frame).union
      ((conjRightCalculus_soundOn frame).union
      ((disjLeftCalculus_soundOn frame).union
      ((disjRightCalculus_soundOn frame).union
      ((impLeftCalculus_soundOn frame).union
      ((impRightCalculus_soundOn frame).union
      ((iffLeftCalculus_soundOn frame).union
      ((iffRightCalculus_soundOn frame).union
        (Calculus.soundOn_empty frame)))))))))))))))

/-- The standard labelled K calculus is sound on every Kripke frame. -/
-- HOL: no direct counterpart; soundness of the Lean labelled K calculus.
theorem standardCalculus_soundOn {W : Type*} (frame : Frame W) :
    standardCalculus.SoundOn frame := by
  simpa only [standardCalculus, Calculus.unions] using
    (propositionalCalculus_soundOn frame).union
      ((boxLeftCalculus_soundOn frame).union
      ((boxRightCalculus_soundOn frame).union
        (Calculus.soundOn_empty frame)))

/-! ## Soundness of proof trees and derivability -/

/-- A locally valid proof tree over a sound calculus has a semantically valid
root sequent. -/
-- HOL: no direct counterpart; generic soundness induction for Lean labelled proof trees.
theorem Valid.soundOn {W : Type*} {frame : Frame W} {C : Calculus}
    (hsound : C.SoundOn frame) {tree : ProofTree} (hvalid : Valid C tree) :
    tree.conclusion.ValidOn frame := by
  induction hvalid with
  | @node conclusion rule children step _ ih =>
      apply hsound rule.name rule.arguments
        (children.map ProofTree.conclusion) conclusion step
      intro premise hpremise
      rw [List.mem_map] at hpremise
      obtain ⟨child, hchild, rfl⟩ := hpremise
      exact ih child hchild

/-- Derivability in a sound calculus implies semantic validity of the root
sequent. -/
-- HOL: no direct counterpart; generic soundness theorem for Lean labelled derivability.
theorem Derivable.soundOn {W : Type*} {frame : Frame W} {C : Calculus}
    (hsound : C.SoundOn frame) {s : Sequent} (hderivable : Derivable C s) :
    s.ValidOn frame := by
  obtain ⟨tree, hvalid, rfl⟩ := hderivable
  exact hvalid.soundOn hsound

end HOLMS.Labelled
