import HOLMS.GenCompleteness

/-!
# Completeness of K

This module specializes the generic finite canonical-model construction to
the empty set of additional axioms and proves soundness, consistency,
finite-model completeness, and completeness over every infinite type of
worlds. Canonical worlds are sets of formulas.
-/

namespace HOLMS

open ModalNotation

/-! ## Correspondence and soundness -/

/-- With no additional axioms, the characteristic frames are precisely all
well-formed frames. -/
-- HOL: `FRAME_CHAR_K` (`k_completeness.ml`).
theorem FRAME_CHAR_K (W : Type*) :
    FRAME W = (CHAR (∅ : Set Form) : Set (Frame W)) := by
  ext frame
  simp [FRAME, CHAR]

/-- Derivability in K preserves validity on all well-formed frames. -/
-- HOL: `K_FRAME_VALID` (`k_completeness.ml`).
theorem K_FRAME_VALID {W : Type*} {H : Set Form} {p : Form}
    (hp : (∅ : Set Form) ⊢ₘ[H] p)
    (hH : ∀ q, q ∈ H → q.Valid (FRAME W)) :
    p.Valid (FRAME W) := by
  rw [FRAME_CHAR_K W] at hH ⊢
  exact GEN_CHAR_VALID hp hH

/-- The finite frames appropriate for K are exactly all finite well-formed
frames. -/
-- HOL: `FINITE_FRAME_APPR_K` (`k_completeness.ml`).
theorem FINITE_FRAME_APPR_K (W : Type*) :
    FINITE_FRAME W = (APPR (∅ : Set Form) : Set (Frame W)) := by
  ext frame
  rw [IN_FINITE_FRAME_INTER, APPR_CAR, ← FRAME_CHAR_K W]

/-- Every theorem of K is valid on every finite well-formed frame. -/
-- HOL: `K_FINITE_FRAME_VALID` (`k_completeness.ml`).
theorem K_FINITE_FRAME_VALID {W : Type*} {p : Form}
    (hp : (∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p) :
    p.Valid (FINITE_FRAME W) := by
  rw [FINITE_FRAME_APPR_K W]
  exact GEN_APPR_VALID hp

/-- K is syntactically consistent. -/
-- HOL: `K_CONSISTENT` (`k_completeness.ml`); set-world formulation.
theorem K_CONSISTENT : ¬((∅ : Set Form) ⊢ₘ[(∅ : Set Form)] ⊥ₘ) := by
  intro hfalse
  let frame : Frame Unit := ⟨Set.univ, fun _ _ => False⟩
  have hframe : frame ∈ FINITE_FRAME Unit := by
    rw [IN_FINITE_FRAME]
    refine ⟨Set.univ_nonempty, ?_, Set.finite_univ⟩
    intro x y hxy
    exact hxy.elim
  have hvalid := K_FINITE_FRAME_VALID (W := Unit) hfalse
  have hholds := hvalid frame hframe (fun _ _ => False) () (by simp [frame])
  exact hholds

/-! ## Standard frames and models -/

/-- The standard frames for K are the generic standard frames for the empty
additional axiom set. -/
-- HOL: `K_STANDARD_FRAME` (definition: `K_STANDARD_FRAME_DEF`) (`k_completeness.ml`); set-world
--   formulation.
def K_STANDARD_FRAME (p : Form) : Set (Frame (Set Form)) :=
  GEN_STANDARD_FRAME (∅ : Set Form) p

/-- Defining equation for K standard frames. -/
-- HOL: `K_STANDARD_FRAME_DEF` (`k_completeness.ml`); set-world formulation.
theorem K_STANDARD_FRAME_DEF (p : Form) :
    K_STANDARD_FRAME p = GEN_STANDARD_FRAME (∅ : Set Form) p := rfl

/-- Expanded characterization of K standard frames. -/
-- HOL: `IN_K_STANDARD_FRAME` (`k_completeness.ml`); set-world formulation.
theorem IN_K_STANDARD_FRAME (p : Form) (frame : Frame (Set Form)) :
    frame ∈ K_STANDARD_FRAME p ↔
      frame.worlds =
          {w | MAXIMAL_SETCONSISTENT (∅ : Set Form) p w ∧
            ∀ q, q ∈ w → q ⊑ₛ p} ∧
      frame ∈ FINITE_FRAME (Set Form) ∧
      ∀ q w, □q ⊑ p → w ∈ frame.worlds →
        (□q ∈ w ↔ ∀ x, frame.rel w x → q ∈ x) := by
  rw [K_STANDARD_FRAME, IN_GEN_STANDARD_FRAME,
    ← FINITE_FRAME_APPR_K (Set Form)]

/-- A K standard model is the corresponding generic standard model. -/
-- HOL: `K_STANDARD_MODEL` (definition: `K_STANDARD_MODEL_DEF`) (`k_completeness.ml`); set-world
--   formulation.
def K_STANDARD_MODEL (p : Form) (model : Model (Set Form)) : Prop :=
  GEN_STANDARD_MODEL (∅ : Set Form) p model

/-- Defining equation for K standard models. -/
-- HOL: `K_STANDARD_MODEL_DEF` (`k_completeness.ml`); set-world formulation.
theorem K_STANDARD_MODEL_DEF (p : Form) (model : Model (Set Form)) :
    K_STANDARD_MODEL p model ↔
      GEN_STANDARD_MODEL (∅ : Set Form) p model := Iff.rfl

/-- Expanded characterization of K standard models. -/
-- HOL: `K_STANDARD_MODEL_CAR` (`k_completeness.ml`); set-world formulation.
theorem K_STANDARD_MODEL_CAR (p : Form) (model : Model (Set Form)) :
    K_STANDARD_MODEL p model ↔
      model.frame ∈ K_STANDARD_FRAME p ∧
        ∀ a w, w ∈ model.frame.worlds →
          (model.valuation a w ↔
            Form.atom a ∈ w ∧ Form.atom a ⊑ p) := Iff.rfl

/-- Truth in a K standard model agrees with membership for every subformula
of the distinguished formula. -/
-- HOL: `K_TRUTH_LEMMA` (`k_completeness.ml`).
theorem K_TRUTH_LEMMA {p q : Form} (model : Model (Set Form))
    (hnp : ¬((∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p))
    (hmodel : K_STANDARD_MODEL p model) (hsub : q ⊑ p) :
    ∀ w, w ∈ model.frame.worlds →
      (q ∈ w ↔ Form.holds model.frame model.valuation q w) :=
  GEN_TRUTH_LEMMA model hnp hmodel hsub

/-! ## Canonical relation and accessibility -/

/-- The canonical accessibility relation for K. -/
-- HOL: `K_STANDARD_REL` (definition: `K_STANDARD_REL_DEF`) (`k_completeness.ml`); set-world
--   formulation.
def K_STANDARD_REL (p : Form) (w x : Set Form) : Prop :=
  GEN_STANDARD_REL (∅ : Set Form) p w x

/-- Defining equation for the K canonical relation. -/
-- HOL: `K_STANDARD_REL_DEF` (`k_completeness.ml`); set-world formulation.
theorem K_STANDARD_REL_DEF (p : Form) :
    K_STANDARD_REL p = GEN_STANDARD_REL (∅ : Set Form) p := rfl

/-- Expanded characterization of the K canonical relation. -/
-- HOL: `K_STANDARD_REL_CAR` (`k_completeness.ml`); set-world formulation.
theorem K_STANDARD_REL_CAR (p : Form) (w x : Set Form) :
    K_STANDARD_REL p w x ↔
      MAXIMAL_SETCONSISTENT (∅ : Set Form) p w ∧
      (∀ q, q ∈ w → q ⊑ₛ p) ∧
      MAXIMAL_SETCONSISTENT (∅ : Set Form) p x ∧
      (∀ q, q ∈ x → q ⊑ₛ p) ∧
      ∀ B, □B ∈ w → B ∈ x := Iff.rfl

/-- The K canonical worlds and relation form a finite well-formed frame. -/
-- HOL: `K_MAXIMAL_CONSISTENT` (`k_completeness.ml`); set-world formulation.
theorem K_MAXIMAL_CONSISTENT {p : Form}
    (hnp : ¬((∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p)) :
    (⟨GEN_STANDARD_WORLD (∅ : Set Form) p, K_STANDARD_REL p⟩ :
      Frame (Set Form)) ∈ FINITE_FRAME (Set Form) := by
  change
    (⟨GEN_STANDARD_WORLD (∅ : Set Form) p,
      GEN_STANDARD_REL (∅ : Set Form) p⟩ : Frame (Set Form)) ∈
        FINITE_FRAME (Set Form)
  exact GEN_FINITE_FRAME_MAXIMAL_CONSISTENT hnp

/-- If every K-canonical successor of `w` contains `q`, then `w` contains
`□q`. -/
-- HOL: `K_ACCESSIBILITY_LEMMA` (`k_completeness.ml`); set-world formulation.
theorem K_ACCESSIBILITY_LEMMA {p q : Form} {w : Set Form}
    (hnp : ¬((∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p))
    (hmaxw : MAXIMAL_SETCONSISTENT (∅ : Set Form) p w)
    (hsubw : ∀ r, r ∈ w → r ⊑ₛ p) (hboxsub : □q ⊑ p)
    (hall : ∀ x, K_STANDARD_REL p w x → q ∈ x) :
    □q ∈ w := by
  by_contra hnbox
  obtain ⟨X, hmaxX, hsubX, hsubset⟩ :=
    GEN_XK_FOR_ACCESSIBILITY_LEMMA hnp hmaxw hsubw hboxsub hnbox
  have hsuccessor :=
    GEN_ACCESSIBILITY_LEMMA hnp hmaxw hsubw hboxsub hnbox
      hmaxX hsubX hsubset
  exact hsuccessor.2 (hall X hsuccessor.1)

/-! ## Countermodels and completeness -/

/-- The canonical finite frame for a non-theorem of K is a K standard frame. -/
-- HOL: `KF_IN_STANDARD_K_FRAME` (`k_completeness.ml`); set-world formulation.
theorem KF_IN_STANDARD_K_FRAME {p : Form}
    (hnp : ¬((∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p)) :
    (⟨GEN_STANDARD_WORLD (∅ : Set Form) p, K_STANDARD_REL p⟩ :
      Frame (Set Form)) ∈ K_STANDARD_FRAME p := by
  rw [IN_K_STANDARD_FRAME]
  refine ⟨rfl, K_MAXIMAL_CONSISTENT hnp, ?_⟩
  intro q w hboxsub hw
  constructor
  · intro hbox x hrel
    exact (K_STANDARD_REL_CAR p w x).mp hrel |>.2.2.2.2 q hbox
  · intro hall
    exact K_ACCESSIBILITY_LEMMA hnp hw.1 hw.2 hboxsub hall

/-- A canonical world containing `¬p` falsifies `p` in the K canonical model. -/
-- HOL: `K_COUNTERMODEL` (`k_completeness.ml`); set-world formulation.
theorem K_COUNTERMODEL {M : Set Form} {p : Form}
    (hnp : ¬((∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p))
    (hmaxM : MAXIMAL_SETCONSISTENT (∅ : Set Form) p M)
    (hnotp : (¬p) ∈ M) (hsubM : ∀ q, q ∈ M → q ⊑ₛ p) :
    ¬Form.holds
      (⟨GEN_STANDARD_WORLD (∅ : Set Form) p, K_STANDARD_REL p⟩ :
        Frame (Set Form))
      (STANDARD_EVAL p) p M := by
  let model : Model (Set Form) :=
    ⟨⟨GEN_STANDARD_WORLD (∅ : Set Form) p, K_STANDARD_REL p⟩,
      STANDARD_EVAL p⟩
  apply GEN_COUNTERMODEL model hnp hmaxM hnotp hsubM
  refine (GEN_STANDARD_MODEL_DEF (∅ : Set Form) p model).mpr
    ⟨?_, ?_⟩
  · simpa only [K_STANDARD_FRAME, model] using KF_IN_STANDARD_K_FRAME hnp
  · intro a w _
    simp only [model, STANDARD_EVAL]
    tauto

/-- Every non-theorem of K has a finite countermodel whose worlds are sets of
formulas. -/
-- HOL: `K_COUNTERMODEL_FINITE_SETS` (`k_completeness.ml`); set-world formulation.
theorem K_COUNTERMODEL_FINITE_SETS {p : Form}
    (hnp : ¬((∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p)) :
    ¬p.holdsIn
      (⟨GEN_STANDARD_WORLD (∅ : Set Form) p, K_STANDARD_REL p⟩ :
        Frame (Set Form)) := by
  apply GEN_COUNTERMODEL_ALT hnp
  simpa only [K_STANDARD_FRAME] using KF_IN_STANDARD_K_FRAME hnp

/-- Finite-frame completeness of K on the canonical set-world type. -/
-- HOL: `K_COMPLETENESS_THM` (`k_completeness.ml`); set-world formulation.
theorem K_COMPLETENESS_THM {p : Form}
    (hvalid : p.Valid (FINITE_FRAME (Set Form))) :
    (∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p := by
  by_contra hnp
  let frame : Frame (Set Form) :=
    ⟨GEN_STANDARD_WORLD (∅ : Set Form) p, K_STANDARD_REL p⟩
  have hfinite : frame ∈ FINITE_FRAME (Set Form) := by
    simpa only [frame] using K_MAXIMAL_CONSISTENT hnp
  exact K_COUNTERMODEL_FINITE_SETS hnp (hvalid frame hfinite)

/-- Finite-frame completeness of K over every infinite type of worlds. -/
-- HOL: `K_COMPLETENESS_THM_GEN` (`k_completeness.ml`).
theorem K_COMPLETENESS_THM_GEN {A : Type*} [Infinite A] {p : Form}
    (hvalid : p.Valid (FINITE_FRAME A)) :
    (∅ : Set Form) ⊢ₘ[(∅ : Set Form)] p := by
  apply K_COMPLETENESS_THM
  have happA : p.Valid (APPR (∅ : Set Form) : Set (Frame A)) := by
    simpa only [← FINITE_FRAME_APPR_K A] using hvalid
  have happSets :=
    GEN_LEMMA_FOR_GEN_COMPLETENESS (A := A) (∅ : Set Form) happA
  simpa only [← FINITE_FRAME_APPR_K (Set Form)] using happSets

/-! ## Automated proof procedure -/

/-- Prove a closed theorem of K by finite-frame completeness, semantic
normalization, and first-order proof search. -/
-- HOL: `K_TAC` / `K_RULE` (`k_completeness.ml`); one Lean tactic interface.
macro "modal_k" : tactic =>
  `(tactic|
    apply K_COMPLETENESS_THM <;>
    simp only [Form.Valid, Form.holdsIn, Form.holds, IN_FINITE_FRAME,
      Set.mem_ofPred_eq] <;>
    grind)

/-! Compile-time regression tests for `modal_k`. -/

-- HOL: unnamed `K_RULE` example 1 in `k_completeness.ml`; regression test.
example (p q r : Form) :
    ∅ ⊢ₘ[∅] (((¬p) ⟶ q ⟶ r) ⟷ ((p ⟶ ⊥ₘ) ⟶ q ⟶ r)) := by
  modal_k

-- HOL: unnamed `K_RULE` example 2 in `k_completeness.ml`; regression test.
example (p : Form) : ∅ ⊢ₘ[∅] (((p ⟶ ⊥ₘ) ⟶ ⊥ₘ) ⟷ p) := by
  modal_k

-- HOL: unnamed `K_RULE` example 3 in `k_completeness.ml`; regression test.
example (p q : Form) : ∅ ⊢ₘ[∅] ((¬ (p ⋏ q)) ⟷ ((¬p) ⋎ ¬ q)) := by
  modal_k

end HOLMS
