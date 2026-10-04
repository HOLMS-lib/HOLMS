import HOLMS.AdHocCorrespondence
import HOLMS.GenCompleteness

/-!
# Completeness of T

This module is the Lean 4 counterpart of the mathematical part of
`t_completeness.ml`. It specializes the generic finite canonical-model
construction to the reflexivity axiom T and proves soundness, consistency,
finite-model completeness, and completeness over every infinite type of
worlds.

The HOL Light file also defines the meta-level proof procedures `T_TAC` and
`T_RULE`. They are intentionally deferred to a separate translation stage;
this module contains only their logical foundation.
-/

namespace HOLMS

open ModalNotation

/-! ## Axiom set -/

/-- The additional axioms of T are all instances of `□p → p`. -/
def T_AX : Set Form := Set.range T_SCHEMA

/-- Every instance of the T schema belongs to `T_AX`. -/
theorem T_IN_T_AX (q : Form) : (□q ⟶ q) ∈ T_AX := ⟨q, rfl⟩

/-- Every instance of the T schema is derivable in T. -/
theorem T_AX_T (q : Form) : T_AX ⊢ₘ[(∅ : Set Form)] (□q ⟶ q) :=
  .ax (T_IN_T_AX q)

/-! ## Reflexive frames and correspondence -/

/-- The class of well-formed reflexive frames. -/
def REFL (W : Type*) : Set (Frame W) :=
  {frame | frame ∈ FRAME W ∧ REFLEXIVE frame.worlds frame.rel}

/-- Membership in the class of reflexive frames. -/
theorem IN_REFL {W : Type*} (frame : Frame W) :
    frame ∈ REFL W ↔
      frame ∈ FRAME W ∧ REFLEXIVE frame.worlds frame.rel := Iff.rfl

/-- Defining equation for the class of reflexive frames. -/
theorem REFL_DEF (W : Type*) :
    REFL W =
      {frame | frame ∈ FRAME W ∧ REFLEXIVE frame.worlds frame.rel} := rfl

/-- Reflexive frames are exactly the frames characteristic for T. -/
theorem REFL_CHAR_T (W : Type*) :
    REFL W = (CHAR T_AX : Set (Frame W)) := by
  ext frame
  rw [IN_REFL, IN_CHAR]
  constructor
  · rintro ⟨hframe, hrefl⟩
    refine ⟨hframe, ?_⟩
    intro q hq
    rcases hq with ⟨p, rfl⟩
    exact (MODAL_REFL frame.worlds frame.rel).mp hrefl p
  · rintro ⟨hframe, hvalid⟩
    refine ⟨hframe, (MODAL_REFL frame.worlds frame.rel).mpr ?_⟩
    intro p
    exact hvalid (T_SCHEMA p) ⟨p, rfl⟩

/-- Derivability in T preserves validity on reflexive frames. -/
theorem T_REFL_VALID {W : Type*} {H : Set Form} {p : Form}
    (hp : T_AX ⊢ₘ[H] p)
    (hH : ∀ q, q ∈ H → q.Valid (REFL W)) :
    p.Valid (REFL W) := by
  rw [REFL_CHAR_T W] at hH ⊢
  exact GEN_CHAR_VALID hp hH

/-! ## Finite reflexive frames -/

/-- The class of finite well-formed reflexive frames. -/
def RF (W : Type*) : Set (Frame W) :=
  {frame | frame ∈ FINITE_FRAME W ∧ REFLEXIVE frame.worlds frame.rel}

/-- Membership in the class of finite reflexive frames. -/
theorem IN_RF {W : Type*} (frame : Frame W) :
    frame ∈ RF W ↔
      frame ∈ FINITE_FRAME W ∧ REFLEXIVE frame.worlds frame.rel := Iff.rfl

/-- Defining equation for finite reflexive frames. -/
theorem RF_DEF (W : Type*) :
    RF W =
      {frame | frame ∈ FINITE_FRAME W ∧
        REFLEXIVE frame.worlds frame.rel} := rfl

/-- Every finite reflexive frame is a reflexive frame. -/
theorem RF_SUBSET_REFL {W : Type*} : RF W ⊆ REFL W := by
  intro frame hframe
  exact ⟨FINITE_FRAME_SUBSET_FRAME hframe.1, hframe.2⟩

/-- Finite reflexive frames are the intersection of reflexive and finite
frames. -/
theorem RF_FIN_REFL (W : Type*) :
    RF W = REFL W ∩ FINITE_FRAME W := by
  ext frame
  rw [IN_RF, Set.mem_inter_iff, IN_REFL, IN_FINITE_FRAME_INTER]
  tauto

/-- The finite frames appropriate for T are exactly the finite reflexive
frames. -/
theorem RF_APPR_T (W : Type*) :
    RF W = (APPR T_AX : Set (Frame W)) := by
  ext frame
  rw [IN_RF, APPR_CAR, ← REFL_CHAR_T W, IN_REFL,
    IN_FINITE_FRAME_INTER]
  tauto

/-- Every theorem of T is valid on every finite reflexive frame. -/
theorem T_RF_VALID {W : Type*} {p : Form}
    (hp : T_AX ⊢ₘ[(∅ : Set Form)] p) : p.Valid (RF W) := by
  rw [RF_APPR_T W]
  exact GEN_APPR_VALID hp

/-- Finite reflexive frames are, in particular, well-formed frames. -/
theorem RF_SUBSET_FRAME {W : Type*} : RF W ⊆ FRAME W := by
  intro frame hframe
  exact FINITE_FRAME_SUBSET_FRAME hframe.1

/-- T is syntactically consistent. -/
theorem T_CONSISTENT : ¬(T_AX ⊢ₘ[(∅ : Set Form)] ⊥ₘ) := by
  intro hfalse
  let frame : Frame Unit := ⟨Set.univ, fun _ _ => True⟩
  have hframe : frame ∈ RF Unit := by
    rw [IN_RF]
    constructor
    · rw [IN_FINITE_FRAME]
      refine ⟨Set.univ_nonempty, ?_, Set.finite_univ⟩
      intro x y _
      exact ⟨Set.mem_univ x, Set.mem_univ y⟩
    · intro w _
      trivial
  have hvalid := T_RF_VALID (W := Unit) hfalse
  have hholds := hvalid frame hframe (fun _ _ => False) () (by simp [frame])
  exact hholds

/-! ## Standard frames and models -/

/-- The standard frames for T. -/
def T_STANDARD_FRAME (p : Form) : Set (Frame (Set Form)) :=
  GEN_STANDARD_FRAME T_AX p

/-- Defining equation for T standard frames. -/
theorem T_STANDARD_FRAME_DEF (p : Form) :
    T_STANDARD_FRAME p = GEN_STANDARD_FRAME T_AX p := rfl

/-- Expanded characterization of T standard frames. -/
theorem IN_T_STANDARD_FRAME (p : Form) (frame : Frame (Set Form)) :
    frame ∈ T_STANDARD_FRAME p ↔
      frame.worlds =
          {w | MAXIMAL_SETCONSISTENT T_AX p w ∧
            ∀ q, q ∈ w → q ⊑ₛ p} ∧
      frame ∈ RF (Set Form) ∧
      ∀ q w, □q ⊑ p → w ∈ frame.worlds →
        (□q ∈ w ↔ ∀ x, frame.rel w x → q ∈ x) := by
  rw [T_STANDARD_FRAME, IN_GEN_STANDARD_FRAME, ← RF_APPR_T (Set Form)]

/-- A T standard model is the corresponding generic standard model. -/
def T_STANDARD_MODEL (p : Form) (model : Model (Set Form)) : Prop :=
  GEN_STANDARD_MODEL T_AX p model

/-- Defining equation for T standard models. -/
theorem T_STANDARD_MODEL_DEF (p : Form) (model : Model (Set Form)) :
    T_STANDARD_MODEL p model ↔ GEN_STANDARD_MODEL T_AX p model := Iff.rfl

/-- Expanded characterization of T standard models. -/
theorem T_STANDARD_MODEL_CAR (p : Form) (model : Model (Set Form)) :
    T_STANDARD_MODEL p model ↔
      model.frame ∈ T_STANDARD_FRAME p ∧
        ∀ a w, w ∈ model.frame.worlds →
          (model.valuation a w ↔
            Form.atom a ∈ w ∧ Form.atom a ⊑ p) := Iff.rfl

/-- Truth in a T standard model agrees with membership for every subformula
of the distinguished formula. -/
theorem T_TRUTH_LEMMA {p q : Form} (model : Model (Set Form))
    (hnp : ¬(T_AX ⊢ₘ[(∅ : Set Form)] p))
    (hmodel : T_STANDARD_MODEL p model) (hsub : q ⊑ p) :
    ∀ w, w ∈ model.frame.worlds →
      (q ∈ w ↔ Form.holds model.frame model.valuation q w) :=
  GEN_TRUTH_LEMMA model hnp hmodel hsub

/-! ## Canonical relation and accessibility -/

/-- The canonical accessibility relation for T. -/
def T_STANDARD_REL (p : Form) (w x : Set Form) : Prop :=
  GEN_STANDARD_REL T_AX p w x

/-- Defining equation for the T canonical relation. -/
theorem T_STANDARD_REL_DEF (p : Form) :
    T_STANDARD_REL p = GEN_STANDARD_REL T_AX p := rfl

/-- Expanded characterization of the T canonical relation. -/
theorem T_STANDARD_REL_CAR (p : Form) (w x : Set Form) :
    T_STANDARD_REL p w x ↔
      MAXIMAL_SETCONSISTENT T_AX p w ∧
      (∀ q, q ∈ w → q ⊑ₛ p) ∧
      MAXIMAL_SETCONSISTENT T_AX p x ∧
      (∀ q, q ∈ x → q ⊑ₛ p) ∧
      ∀ B, □B ∈ w → B ∈ x := Iff.rfl

/-- The T canonical worlds and relation form a finite reflexive frame. -/
theorem RF_MAXIMAL_CONSISTENT {p : Form}
    (hnp : ¬(T_AX ⊢ₘ[(∅ : Set Form)] p)) :
    (⟨GEN_STANDARD_WORLD T_AX p, T_STANDARD_REL p⟩ :
      Frame (Set Form)) ∈ RF (Set Form) := by
  rw [IN_RF]
  constructor
  · change
      (⟨GEN_STANDARD_WORLD T_AX p, GEN_STANDARD_REL T_AX p⟩ :
        Frame (Set Form)) ∈ FINITE_FRAME (Set Form)
    exact GEN_FINITE_FRAME_MAXIMAL_CONSISTENT hnp
  · intro w hw
    rw [GEN_STANDARD_WORLD_EQ] at hw
    rcases hw with ⟨hmaxw, hsubw⟩
    change T_STANDARD_REL p w w
    rw [T_STANDARD_REL_CAR]
    refine ⟨hmaxw, hsubw, hmaxw, hsubw, ?_⟩
    intro B hbox
    have hboxsub : □B ⊑ₛ p := hsubw (□B) hbox
    have hBsub : B ⊑ p := by
      cases hboxsub with
      | ofSubformula hsub => exact Form.of_subformula_box hsub
    apply
      (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmaxw hBsub).mpr
    exact MLK_modusponens
      (MODPROVES_MONO2 (T_AX_T B) (Set.empty_subset w)) (.hyp hbox)

/-- If every T-canonical successor of `w` contains `q`, then `w` contains
`□q`. -/
theorem T_ACCESSIBILITY_LEMMA {p q : Form} {w : Set Form}
    (hnp : ¬(T_AX ⊢ₘ[(∅ : Set Form)] p))
    (hmaxw : MAXIMAL_SETCONSISTENT T_AX p w)
    (hsubw : ∀ r, r ∈ w → r ⊑ₛ p) (hboxsub : □q ⊑ p)
    (hall : ∀ x, T_STANDARD_REL p w x → q ∈ x) :
    □q ∈ w := by
  by_contra hnbox
  obtain ⟨X, hmaxX, hsubX, hsubset⟩ :=
    GEN_XK_FOR_ACCESSIBILITY_LEMMA hnp hmaxw hsubw hboxsub hnbox
  have hsuccessor :=
    GEN_ACCESSIBILITY_LEMMA hnp hmaxw hsubw hboxsub hnbox
      hmaxX hsubX hsubset
  exact hsuccessor.2 (hall X hsuccessor.1)

/-! ## Countermodels and completeness -/

/-- The canonical finite reflexive frame for a non-theorem is a T standard
frame. -/
theorem RF_IN_T_STANDARD_FRAME {p : Form}
    (hnp : ¬(T_AX ⊢ₘ[(∅ : Set Form)] p)) :
    (⟨GEN_STANDARD_WORLD T_AX p, T_STANDARD_REL p⟩ :
      Frame (Set Form)) ∈ T_STANDARD_FRAME p := by
  rw [IN_T_STANDARD_FRAME]
  refine ⟨rfl, RF_MAXIMAL_CONSISTENT hnp, ?_⟩
  intro q w hboxsub hw
  constructor
  · intro hbox x hrel
    exact (T_STANDARD_REL_CAR p w x).mp hrel |>.2.2.2.2 q hbox
  · intro hall
    exact T_ACCESSIBILITY_LEMMA hnp hw.1 hw.2 hboxsub hall

/-- A canonical world containing `¬p` falsifies `p` in the T canonical model. -/
theorem T_COUNTERMODEL {M : Set Form} {p : Form}
    (hnp : ¬(T_AX ⊢ₘ[(∅ : Set Form)] p))
    (hmaxM : MAXIMAL_SETCONSISTENT T_AX p M)
    (hnotp : (¬p) ∈ M) (hsubM : ∀ q, q ∈ M → q ⊑ₛ p) :
    ¬Form.holds
      (⟨GEN_STANDARD_WORLD T_AX p, T_STANDARD_REL p⟩ : Frame (Set Form))
      (STANDARD_EVAL p) p M := by
  let model : Model (Set Form) :=
    ⟨⟨GEN_STANDARD_WORLD T_AX p, T_STANDARD_REL p⟩, STANDARD_EVAL p⟩
  apply GEN_COUNTERMODEL model hnp hmaxM hnotp hsubM
  refine (GEN_STANDARD_MODEL_DEF T_AX p model).mpr ⟨?_, ?_⟩
  · simpa only [T_STANDARD_FRAME, model] using RF_IN_T_STANDARD_FRAME hnp
  · intro a w _
    simp only [model, STANDARD_EVAL]
    tauto

/-- Every non-theorem of T has a finite reflexive countermodel whose worlds
are sets of formulas. -/
theorem T_COUNTERMODEL_FINITE_SETS {p : Form}
    (hnp : ¬(T_AX ⊢ₘ[(∅ : Set Form)] p)) :
    ¬p.holdsIn
      (⟨GEN_STANDARD_WORLD T_AX p, T_STANDARD_REL p⟩ :
        Frame (Set Form)) := by
  apply GEN_COUNTERMODEL_ALT hnp
  simpa only [T_STANDARD_FRAME] using RF_IN_T_STANDARD_FRAME hnp

/-- Finite-reflexive-frame completeness of T on the canonical set-world
type. -/
theorem T_COMPLETENESS_THM {p : Form}
    (hvalid : p.Valid (RF (Set Form))) :
    T_AX ⊢ₘ[(∅ : Set Form)] p := by
  by_contra hnp
  let frame : Frame (Set Form) :=
    ⟨GEN_STANDARD_WORLD T_AX p, T_STANDARD_REL p⟩
  have hfinite : frame ∈ RF (Set Form) := by
    simpa only [frame] using RF_MAXIMAL_CONSISTENT hnp
  exact T_COUNTERMODEL_FINITE_SETS hnp (hvalid frame hfinite)

/-- Finite-reflexive-frame completeness of T over every infinite type of
worlds. -/
theorem T_COMPLETENESS_THM_GEN {A : Type*} [Infinite A] {p : Form}
    (hvalid : p.Valid (RF A)) : T_AX ⊢ₘ[(∅ : Set Form)] p := by
  apply T_COMPLETENESS_THM
  have happA : p.Valid (APPR T_AX : Set (Frame A)) := by
    simpa only [← RF_APPR_T A] using hvalid
  have happSets := GEN_LEMMA_FOR_GEN_COMPLETENESS (A := A) T_AX happA
  simpa only [← RF_APPR_T (Set Form)] using happSets

end HOLMS
