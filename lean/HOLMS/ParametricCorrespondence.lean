import HOLMS.Calculus

/-!
# Parametric correspondence theory

This module defines well-formed and finite Kripke frames, the frames
characteristic for a set of modal axioms, and the finite frames appropriate
for that set. Its main results establish semantic soundness of the Hilbert
calculus over those frame classes.
-/

namespace HOLMS

open ModalNotation

/-! ## Well-formed frames -/

/-- The class of nonempty frames whose relation only connects designated
worlds. -/
-- HOL: `FRAME` (definition: `FRAME_DEF`) (`parametric_correspondence.ml`).
def FRAME (W : Type*) : Set (Frame W) :=
  {frame | frame.worlds.Nonempty ∧
    ∀ x y, frame.rel x y → x ∈ frame.worlds ∧ y ∈ frame.worlds}

/-- Membership in the class of well-formed frames. -/
-- HOL: `IN_FRAME` (`parametric_correspondence.ml`).
theorem IN_FRAME {W : Type*} (frame : Frame W) :
    frame ∈ FRAME W ↔ frame.worlds.Nonempty ∧
      ∀ x y, frame.rel x y → x ∈ frame.worlds ∧ y ∈ frame.worlds := Iff.rfl

/-- The class of finite well-formed frames. -/
-- HOL: `FINITE_FRAME` (definition: `FINITE_FRAME_DEF`) (`parametric_correspondence.ml`).
def FINITE_FRAME (W : Type*) : Set (Frame W) :=
  {frame | frame ∈ FRAME W ∧ frame.worlds.Finite}

/-- Membership in the class of finite well-formed frames. -/
-- HOL: `IN_FINITE_FRAME` (`parametric_correspondence.ml`).
theorem IN_FINITE_FRAME {W : Type*} (frame : Frame W) :
    frame ∈ FINITE_FRAME W ↔ frame.worlds.Nonempty ∧
      (∀ x y, frame.rel x y → x ∈ frame.worlds ∧ y ∈ frame.worlds) ∧
      frame.worlds.Finite := by
  simp only [FINITE_FRAME, IN_FRAME]
  change ((_ ∧ _) ∧ _) ↔ _ ∧ _ ∧ _
  tauto

/-- A finite frame is precisely a well-formed frame with finitely many
designated worlds. -/
-- HOL: `IN_FINITE_FRAME_INTER` (`parametric_correspondence.ml`).
theorem IN_FINITE_FRAME_INTER {W : Type*} (frame : Frame W) :
    frame ∈ FINITE_FRAME W ↔ frame ∈ FRAME W ∧ frame.worlds.Finite := Iff.rfl

/-- Every finite well-formed frame is a well-formed frame. -/
-- HOL: `FINITE_FRAME_SUBSET_FRAME` (`parametric_correspondence.ml`).
theorem FINITE_FRAME_SUBSET_FRAME {W : Type*} :
    FINITE_FRAME W ⊆ FRAME W := fun _ h => h.1

/-! ## Frames characteristic for an axiom set -/

/-- The well-formed frames validating every formula in `S`. -/
-- HOL: `CHAR` (definition: `CHAR_DEF`) (`parametric_correspondence.ml`).
def CHAR {W : Type*} (S : Set Form) : Set (Frame W) :=
  {frame | frame ∈ FRAME W ∧ ∀ p, p ∈ S → p.holdsIn frame}

/-- Membership in the characteristic class of an axiom set. -/
-- HOL: `IN_CHAR` (`parametric_correspondence.ml`).
theorem IN_CHAR {W : Type*} (S : Set Form) (frame : Frame W) :
    frame ∈ CHAR S ↔ frame ∈ FRAME W ∧ ∀ p, p ∈ S → p.holdsIn frame := Iff.rfl

/-! ## Semantic soundness -/

/-- Every primitive `K` axiom is valid on every Kripke frame. -/
-- HOL: no separate named theorem; framewise validity fact used in `GEN_KAXIOM_CHAR_VALID`.
theorem KAXIOM_HOLDS_IN {W : Type*} {frame : Frame W} {p : Form}
    (hp : KAxiom p) : p.holdsIn frame := by
  classical
  intro valuation w hw
  cases hp with
  | addImp => simp only [Form.holds]; tauto
  | distribImp => simp only [Form.holds]; tauto
  | doubleNeg => simp only [Form.holds]; tauto
  | iffImp₁ => simp only [Form.holds]; tauto
  | iffImp₂ => simp only [Form.holds]; tauto
  | impIff => simp only [Form.holds]; tauto
  | verum => simp only [Form.holds]; tauto
  | neg => simp only [Form.holds]
  | conj => simp only [Form.holds]; tauto
  | disj => simp only [Form.holds]; tauto
  | boxImp p q =>
      simp only [Form.holds]
      intro hpq hp y hy hry
      exact hpq y hy hry (hp y hy hry)

/-- Primitive `K` axioms are valid on every characteristic class. -/
-- HOL: `GEN_KAXIOM_CHAR_VALID` (`parametric_correspondence.ml`).
theorem GEN_KAXIOM_CHAR_VALID {W : Type*} (S : Set Form) {p : Form}
    (hp : KAxiom p) : p.Valid (CHAR S : Set (Frame W)) := by
  intro frame _
  exact KAXIOM_HOLDS_IN hp

/-- Primitive `K` axioms remain valid on every subclass of a characteristic
class. -/
-- HOL: `GEN_KAXIOM_SUBS_CHAR_VALID` (`parametric_correspondence.ml`).
theorem GEN_KAXIOM_SUBS_CHAR_VALID {W : Type*} (S : Set Form)
    (X : Set (Frame W)) (_hX : X ⊆ CHAR S) {p : Form} (hp : KAxiom p) :
    p.Valid X := by
  intro frame _
  exact KAXIOM_HOLDS_IN hp

/-- Every selected additional axiom is valid on its characteristic class. -/
-- HOL: `GEN_AX_CHAR_VALID` (`parametric_correspondence.ml`).
theorem GEN_AX_CHAR_VALID {W : Type*} (S : Set Form) {p : Form}
    (hp : p ∈ S) : p.Valid (CHAR S : Set (Frame W)) := by
  intro frame hframe
  exact hframe.2 p hp

/-- Every selected additional axiom is valid on every subclass of its
characteristic class. -/
-- HOL: `GEN_AX_SUBS_CHAR_VALID` (`parametric_correspondence.ml`).
theorem GEN_AX_SUBS_CHAR_VALID {W : Type*} (S : Set Form)
    (X : Set (Frame W)) (hX : X ⊆ CHAR S) {p : Form} (hp : p ∈ S) :
    p.Valid X := by
  intro frame hframe
  exact (hX hframe).2 p hp

/-- General soundness over an arbitrary subclass of the characteristic
frames. -/
-- HOL: `GEN_SUBS_CHAR_VALID` (`parametric_correspondence.ml`).
theorem GEN_SUBS_CHAR_VALID {W : Type*} {S H : Set Form} {X : Set (Frame W)}
    (hX : X ⊆ CHAR S) {p : Form} (hp : S ⊢ₘ[H] p)
    (hH : ∀ q, q ∈ H → q.Valid X) : p.Valid X := by
  induction hp with
  | kaxiom hk => exact GEN_KAXIOM_SUBS_CHAR_VALID S X hX hk
  | ax ha => exact GEN_AX_SUBS_CHAR_VALID S X hX ha
  | hyp hh => exact hH _ hh
  | modusPonens _ _ ihpq ihp =>
      intro frame hframe valuation w hw
      exact (ihpq hH frame hframe valuation w hw) (ihp hH frame hframe valuation w hw)
  | necessitation hp ih =>
      intro frame hframe valuation w hw y hy _
      exact ih (fun q hq => False.elim (hq)) frame hframe valuation y hy

/-- General soundness over the characteristic frames of `S`. -/
-- HOL: `GEN_CHAR_VALID` (`parametric_correspondence.ml`).
theorem GEN_CHAR_VALID {W : Type*} {S H : Set Form} {p : Form}
    (hp : S ⊢ₘ[H] p) (hH : ∀ q, q ∈ H → q.Valid (CHAR S : Set (Frame W))) :
    p.Valid (CHAR S : Set (Frame W)) :=
  GEN_SUBS_CHAR_VALID (Set.Subset.rfl) hp hH

/-- A well-formed frame is characteristic for `S` exactly when it validates
every theorem derivable from `S` without hypotheses. -/
-- HOL: `CHAR_CAR` (`parametric_correspondence.ml`).
theorem CHAR_CAR {W : Type*} (S : Set Form) (frame : Frame W) :
    (frame ∈ FRAME W ∧ ∀ p, (S ⊢ₘ[(∅ : Set Form)] p) → p.holdsIn frame) ↔
      frame ∈ CHAR S := by
  constructor
  · rintro ⟨hframe, htheorems⟩
    refine ⟨hframe, fun p hp => ?_⟩
    exact htheorems p (.ax hp)
  · intro hchar
    refine ⟨hchar.1, fun p hp => ?_⟩
    have hvalid : p.Valid (CHAR S : Set (Frame W)) :=
      GEN_CHAR_VALID hp (fun q hq => False.elim hq)
    exact hvalid frame hchar

/-! ## Finite frames appropriate for an axiom set -/

/-- The finite well-formed frames validating every theorem of `S`. -/
-- HOL: `APPR` (definition: `APPR_DEF`) (`parametric_correspondence.ml`).
def APPR {W : Type*} (S : Set Form) : Set (Frame W) :=
  {frame | frame ∈ FINITE_FRAME W ∧
    ∀ p, (S ⊢ₘ[(∅ : Set Form)] p) → p.holdsIn frame}

/-- Membership in the class of frames appropriate for `S`. -/
-- HOL: `IN_APPR` (`parametric_correspondence.ml`).
theorem IN_APPR {W : Type*} (S : Set Form) (frame : Frame W) :
    frame ∈ APPR S ↔ frame ∈ FINITE_FRAME W ∧
      ∀ p, (S ⊢ₘ[(∅ : Set Form)] p) → p.holdsIn frame := Iff.rfl

/-- Appropriate frames are exactly the finite characteristic frames. -/
-- HOL: `APPR_CAR` (`parametric_correspondence.ml`).
theorem APPR_CAR {W : Type*} (S : Set Form) (frame : Frame W) :
    frame ∈ APPR S ↔ frame ∈ CHAR S ∧ frame.worlds.Finite := by
  rw [IN_APPR, IN_FINITE_FRAME_INTER]
  constructor
  · rintro ⟨⟨hframe, hfinite⟩, htheorems⟩
    exact ⟨(CHAR_CAR S frame).mp ⟨hframe, htheorems⟩, hfinite⟩
  · rintro ⟨hchar, hfinite⟩
    exact ⟨⟨hchar.1, hfinite⟩, (CHAR_CAR S frame).mpr hchar |>.2⟩

/-- The appropriate class is the intersection of the characteristic and
finite-frame classes. -/
-- HOL: `APPR_EQ_CHAR_FINITE` (`parametric_correspondence.ml`).
theorem APPR_EQ_CHAR_FINITE {W : Type*} (S : Set Form) :
    APPR S = CHAR S ∩ FINITE_FRAME W := by
  ext frame
  rw [APPR_CAR, Set.mem_inter_iff, IN_FINITE_FRAME_INTER]
  constructor
  · rintro ⟨hchar, hfinite⟩
    exact ⟨hchar, hchar.1, hfinite⟩
  · rintro ⟨hchar, _, hfinite⟩
    exact ⟨hchar, hfinite⟩

/-- Every appropriate frame is characteristic. -/
-- HOL: `APPR_SUBSET_CHAR` (`parametric_correspondence.ml`).
theorem APPR_SUBSET_CHAR {W : Type*} (S : Set Form) :
    (APPR S : Set (Frame W)) ⊆ CHAR S := by
  intro frame hframe
  exact (APPR_CAR S frame).mp hframe |>.1

/-- Every theorem of `S` is valid on the frames appropriate for `S`. -/
-- HOL: `GEN_APPR_VALID` (`parametric_correspondence.ml`).
theorem GEN_APPR_VALID {W : Type*} {S : Set Form} {p : Form}
    (hp : S ⊢ₘ[(∅ : Set Form)] p) : p.Valid (APPR S : Set (Frame W)) := by
  intro frame hframe
  exact hframe.2 p hp

end HOLMS
