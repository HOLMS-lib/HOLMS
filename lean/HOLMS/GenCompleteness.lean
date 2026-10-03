import HOLMS.SetConsistent
import HOLMS.ParametricCorrespondence

/-!
# Generic completeness infrastructure

This module is the Lean 4 counterpart of `gen_completeness.ml`.  Canonical
worlds are represented directly by sets of formulas, rather than by
duplicate-free lists.  This first part defines the standard frames, models,
and valuations used by the generic completeness construction.
-/

namespace HOLMS

open ModalNotation

/-! ## Standard frames -/

/-- The canonical worlds selected by a formula schema `P`: maximally
consistent sets relative to `p` whose members all belong to `P p`. -/
def PARAMETRIC_STD_WORLD (S : Set Form) (P : Form → Set Form) (p : Form) :
    Set (Set Form) :=
  {w | MAXIMAL_SETCONSISTENT S p w ∧ w ⊆ P p}

/-- The appropriate frames whose worlds are the selected canonical worlds and
whose relation satisfies the truth condition for boxed subformulas of `p`. -/
def PARAMETRIC_STANDARD_FRAME (S : Set Form) (P : Form → Set Form)
    (p : Form) : Set (Frame (Set Form)) :=
  APPR S ∩
    {frame | frame.worlds = PARAMETRIC_STD_WORLD S P p ∧
      ∀ q w, □q ⊑ p → w ∈ frame.worlds →
        (□q ∈ w ↔ ∀ x, frame.rel w x → q ∈ x)}

/-- Defining characterization of parametric standard frames. -/
theorem PARAMETRIC_STANDARD_FRAME_DEF (S : Set Form) (P : Form → Set Form)
    (p : Form) :
    PARAMETRIC_STANDARD_FRAME S P p =
      APPR S ∩
        {frame | frame.worlds = PARAMETRIC_STD_WORLD S P p ∧
          ∀ q w, □q ⊑ p → w ∈ frame.worlds →
            (□q ∈ w ↔ ∀ x, frame.rel w x → q ∈ x)} := rfl

/-- The generic standard-frame schema consists of all subsentences of `p`. -/
def STD_FRAME_SCHEMA (p : Form) : Set Form :=
  {q | q ⊑ₛ p}

/-- The canonical worlds used by the generic completeness construction. -/
def GEN_STANDARD_WORLD (S : Set Form) (p : Form) : Set (Set Form) :=
  PARAMETRIC_STD_WORLD S STD_FRAME_SCHEMA p

/-- Defining equation for generic standard worlds. -/
theorem GEN_STANDARD_WORLD_DEF (S : Set Form) (p : Form) :
    GEN_STANDARD_WORLD S p = PARAMETRIC_STD_WORLD S STD_FRAME_SCHEMA p := rfl

/-- Expanded characterization of generic standard worlds.

The HOL Light theorem carrying this characterization is also named
`GEN_STANDARD_WORLD`; Lean uses `GEN_STANDARD_WORLD_EQ` because the definition
already occupies that name. -/
theorem GEN_STANDARD_WORLD_EQ (S : Set Form) (p : Form) :
    GEN_STANDARD_WORLD S p =
      {w | MAXIMAL_SETCONSISTENT S p w ∧ ∀ q, q ∈ w → q ⊑ₛ p} := by
  rfl

/-- The generic standard frames obtained from the subsentence schema. -/
def GEN_STANDARD_FRAME (S : Set Form) (p : Form) :
    Set (Frame (Set Form)) :=
  PARAMETRIC_STANDARD_FRAME S STD_FRAME_SCHEMA p

/-- Expanded characterization of generic standard frames. -/
theorem GEN_STANDARD_FRAME_DEF (S : Set Form) (p : Form) :
    GEN_STANDARD_FRAME S p =
      APPR S ∩
        {frame |
          frame.worlds =
              {w | MAXIMAL_SETCONSISTENT S p w ∧
                ∀ q, q ∈ w → q ⊑ₛ p} ∧
          ∀ q w, □q ⊑ p → w ∈ frame.worlds →
            (□q ∈ w ↔ ∀ x, frame.rel w x → q ∈ x)} := by
  rfl

/-- Membership characterization for generic standard frames. -/
theorem IN_GEN_STANDARD_FRAME (S : Set Form) (p : Form)
    (frame : Frame (Set Form)) :
    frame ∈ GEN_STANDARD_FRAME S p ↔
      frame.worlds =
          {w | MAXIMAL_SETCONSISTENT S p w ∧
            ∀ q, q ∈ w → q ⊑ₛ p} ∧
      frame ∈ APPR S ∧
      ∀ q w, □q ⊑ p → w ∈ frame.worlds →
        (□q ∈ w ↔ ∀ x, frame.rel w x → q ∈ x) := by
  rw [GEN_STANDARD_FRAME_DEF]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-! ## Standard models -/

/-- A standard model is based on a generic standard frame and interprets an
atom by membership in the current canonical world. -/
def GEN_STANDARD_MODEL (S : Set Form) (p : Form) (model : Model (Set Form)) :
    Prop :=
  model.frame ∈ GEN_STANDARD_FRAME S p ∧
    ∀ a w, w ∈ model.frame.worlds →
      (model.valuation a w ↔ Form.atom a ∈ w ∧ Form.atom a ⊑ p)

/-- Defining characterization of generic standard models. -/
theorem GEN_STANDARD_MODEL_DEF (S : Set Form) (p : Form)
    (model : Model (Set Form)) :
    GEN_STANDARD_MODEL S p model ↔
      model.frame ∈ GEN_STANDARD_FRAME S p ∧
        ∀ a w, w ∈ model.frame.worlds →
          (model.valuation a w ↔ Form.atom a ∈ w ∧ Form.atom a ⊑ p) := Iff.rfl

/-- The canonical valuation on set-based worlds. -/
def STANDARD_EVAL (p : Form) : Valuation (Set Form) :=
  fun a w => Form.atom a ⊑ p ∧ Form.atom a ∈ w

/-- Compatibility name for the canonical valuation on set-based worlds.

HOL Light distinguishes this definition from `STANDARD_EVAL` because the
latter acts on list worlds.  Canonical worlds are already sets in Lean, so the
two valuations coincide. -/
def SET_STANDARD_EVAL (p : Form) : Valuation (Set Form) :=
  STANDARD_EVAL p

/-- The two standard-evaluation names are definitionally equal in the
set-based translation. -/
theorem SET_STANDARD_EVAL_EQ_STANDARD_EVAL (p : Form) :
    SET_STANDARD_EVAL p = STANDARD_EVAL p := rfl

/-! ## Truth lemma -/

/-- In a generic standard model, membership in a canonical world agrees with
Kripke truth for every subformula of the distinguished formula.

As in the HOL Light statement, the theorem assumes that `p` is not derivable
without hypotheses.  The structural induction itself uses only the standard
model and subformula assumptions; the nonderivability hypothesis is retained
to preserve the original interface and for the later countermodel theorems
that instantiate this result. -/
theorem GEN_TRUTH_LEMMA {S : Set Form} {p q : Form}
    (model : Model (Set Form))
    (_hnp : ¬S ⊢ₘ[(∅ : Set Form)] p)
    (hmodel : GEN_STANDARD_MODEL S p model) (hsub : q ⊑ p) :
    ∀ w, w ∈ model.frame.worlds →
      (q ∈ w ↔ Form.holds model.frame model.valuation q w) := by
  rcases (GEN_STANDARD_MODEL_DEF S p model).mp hmodel with
    ⟨hstandard, hvaluation⟩
  rcases (IN_GEN_STANDARD_FRAME S p model.frame).mp hstandard with
    ⟨hworlds, happr, hbox⟩
  have hcanonical : ∀ {w}, w ∈ model.frame.worlds →
      MAXIMAL_SETCONSISTENT S p w ∧ ∀ r, r ∈ w → r ⊑ₛ p := by
    intro w hw
    rw [hworlds] at hw
    exact hw
  have hclosed : ∀ x y, model.frame.rel x y →
      x ∈ model.frame.worlds ∧ y ∈ model.frame.worlds :=
    ((IN_FINITE_FRAME model.frame).mp ((IN_APPR S model.frame).mp happr).1).2.1
  induction q with
  | falsum =>
      intro w hw
      simp only [Form.holds]
      constructor
      · intro hfalse
        exact (hcanonical hw).1.1 (.hyp hfalse)
      · intro hfalse
        exact hfalse.elim
  | verum =>
      intro w hw
      simp only [Form.holds]
      constructor
      · intro _
        trivial
      · intro _
        exact MAXIMAL_SETCONSISTENT_TRUE_CLOSED (hcanonical hw).1 hsub
  | atom a =>
      intro w hw
      simp only [Form.holds]
      constructor
      · intro hatom
        exact (hvaluation a w hw).mpr ⟨hatom, hsub⟩
      · intro hatom
        exact ((hvaluation a w hw).mp hatom).1
  | neg r ih =>
      intro w hw
      have hrsub : r ⊑ p := Form.of_subformula_neg hsub
      simp only [Form.holds]
      rw [MAXIMAL_SETCONSISTENT_NOT_CLOSED (hcanonical hw).1 hsub,
        ih hrsub w hw]
  | conj r s ihr ihs =>
      intro w hw
      have hrsub : r ⊑ p := Form.of_subformula_conj_left hsub
      have hssub : s ⊑ p := Form.of_subformula_conj_right hsub
      simp only [Form.holds]
      rw [MAXIMAL_SETCONSISTENT_AND_MIONOR_CLOSED (hcanonical hw).1 hsub,
        ihr hrsub w hw, ihs hssub w hw]
  | disj r s ihr ihs =>
      intro w hw
      have hrsub : r ⊑ p := Form.of_subformula_disj_left hsub
      have hssub : s ⊑ p := Form.of_subformula_disj_right hsub
      simp only [Form.holds]
      rw [MAXIMAL_SETCONSISTENT_MINOR_OR_CLOSED (hcanonical hw).1 hsub,
        ihr hrsub w hw, ihs hssub w hw]
  | imp r s ihr ihs =>
      intro w hw
      have hrsub : r ⊑ p := Form.of_subformula_imp_left hsub
      have hssub : s ⊑ p := Form.of_subformula_imp_right hsub
      simp only [Form.holds]
      rw [MAXIMAL_SETCONSISTENT_IMP_CLOSED (hcanonical hw).1 hsub,
        ihr hrsub w hw, ihs hssub w hw]
  | iff r s ihr ihs =>
      intro w hw
      have hrsub : r ⊑ p := Form.of_subformula_iff_left hsub
      have hssub : s ⊑ p := Form.of_subformula_iff_right hsub
      simp only [Form.holds]
      rw [MAXIMAL_SETCONSISTENT_IFF_CLOSED (hcanonical hw).1 hsub,
        ihr hrsub w hw, ihs hssub w hw]
  | box r ih =>
      intro w hw
      have hrsub : r ⊑ p := Form.of_subformula_box hsub
      simp only [Form.holds]
      constructor
      · intro hboxmem x hx hrel
        have hrmem : r ∈ x := (hbox r w hsub hw).mp hboxmem x hrel
        exact (ih hrsub x hx).mp hrmem
      · intro hholds
        apply (hbox r w hsub hw).mpr
        intro x hrel
        have hx : x ∈ model.frame.worlds := (hclosed w x hrel).2
        exact (ih hrsub x hx).mpr (hholds x hx hrel)

end HOLMS
