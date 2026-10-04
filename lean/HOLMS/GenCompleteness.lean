import HOLMS.SetConsistent
import HOLMS.ParametricCorrespondence

/-!
# Generic completeness infrastructure

This module is the Lean 4 counterpart of `gen_completeness.ml`.  It constructs
finite canonical frames, proves the truth and accessibility lemmas, extracts
generic countermodels, and transports validity to an arbitrary infinite world
type. Canonical worlds are represented directly by sets of formulas, rather
than by duplicate-free lists; consequently, the source file's permutation and
list-to-set infrastructure has no separate Lean counterpart.
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

/-! ## Standard relation and finite canonical frame -/

/-- The canonical accessibility relation: both endpoints are generic
canonical worlds and every box content of the source belongs to the target. -/
def GEN_STANDARD_REL (S : Set Form) (p : Form) (w x : Set Form) : Prop :=
  MAXIMAL_SETCONSISTENT S p w ∧
    (∀ q, q ∈ w → q ⊑ₛ p) ∧
    MAXIMAL_SETCONSISTENT S p x ∧
    (∀ q, q ∈ x → q ⊑ₛ p) ∧
    ∀ B, □B ∈ w → B ∈ x

/-- If `p` is not derivable, its canonical worlds equipped with the canonical
relation form a finite well-formed frame. -/
theorem GEN_FINITE_FRAME_MAXIMAL_CONSISTENT {S : Set Form} {p : Form}
    (hnp : ¬S ⊢ₘ[(∅ : Set Form)] p) :
    (⟨GEN_STANDARD_WORLD S p, GEN_STANDARD_REL S p⟩ : Frame (Set Form)) ∈
      FINITE_FRAME (Set Form) := by
  rw [IN_FINITE_FRAME]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨M, hmax, _, hsubs⟩ := NONEMPTY_MAXIMAL_SETCONSISTENT hnp
    refine ⟨M, ?_⟩
    rw [GEN_STANDARD_WORLD_EQ]
    exact ⟨hmax, hsubs⟩
  · intro w x hrel
    rw [GEN_STANDARD_WORLD_EQ]
    exact ⟨⟨hrel.1, hrel.2.1⟩, hrel.2.2.1, hrel.2.2.2.1⟩
  · apply (FINITE_SUBSENTENCE p).finite_subsets.subset
    intro w hw
    rw [GEN_STANDARD_WORLD_EQ] at hw
    exact hw.2

/-! ## Accessibility -/

/-- The unboxed contents of all boxed formulas in a canonical world. -/
def GEN_BOX_CONTENT (w : Set Form) : Set Form :=
  {q | □q ∈ w}

/-- Lift a derivation under `box`: if `p` follows from `Γ` and the target
context `w` contains `□q` for every hypothesis `q ∈ Γ`, then `□p` follows
from `w`.

This local principle replaces the HOL Light argument that collects `Γ` into
`CONJLIST Γ`, boxes that conjunction, and distributes `box` back over the
derivation.  The proof instead follows the derivation directly. Primitive and
additional axioms are boxed by necessitation, hypotheses use the corresponding
member of `w`, modus ponens uses `MLK_box_modusponens`, and a necessitation
step is boxed once more. The last case is sound because the premise of
necessitation is derivable from the empty hypothesis set. -/
private theorem box_derivation_from_context {S Γ w : Set Form} {p : Form}
    (hp : S ⊢ₘ[Γ] p) (hΓ : ∀ q, q ∈ Γ → □q ∈ w) : S ⊢ₘ[w] □p := by
  induction hp with
  | kaxiom h => exact .necessitation (.kaxiom h)
  | ax h => exact .necessitation (.ax h)
  | hyp h => exact .hyp (hΓ _ h)
  | modusPonens _ _ ihpq ihp =>
      exact MLK_box_modusponens (ihpq hΓ) (ihp hΓ)
  | necessitation hp _ => exact .necessitation (.necessitation hp)

/-- Removing the outer box from a subsentence leaves a subsentence. -/
private theorem content_subsentence_of_box_subsentence {p q : Form}
    (h : □q ⊑ₛ p) : q ⊑ₛ p := by
  cases h with
  | ofSubformula hsub =>
      exact .ofSubformula (Form.of_subformula_box hsub)

/-- If a boxed subformula is absent from a canonical world, the negation of
its body together with all box contents extends to another canonical world. -/
theorem GEN_XK_FOR_ACCESSIBILITY_LEMMA {S w : Set Form} {p q : Form}
    (_hnp : ¬S ⊢ₘ[(∅ : Set Form)] p)
    (hmaxw : MAXIMAL_SETCONSISTENT S p w)
    (hsubw : ∀ r, r ∈ w → r ⊑ₛ p) (hboxsub : □q ⊑ p)
    (hnbox : □q ∉ w) :
    ∃ X, MAXIMAL_SETCONSISTENT S p X ∧
      (∀ r, r ∈ X → r ⊑ₛ p) ∧
      insert (¬q) (GEN_BOX_CONTENT w) ⊆ X := by
  have hconsistent : SETCONSISTENT S (insert (¬q) (GEN_BOX_CONTENT w)) := by
    intro hfalse
    have himp : S ⊢ₘ[GEN_BOX_CONTENT w] (¬q) ⟶ ⊥ₘ :=
      MODPROVES_DEDUCTION_LEMMA.mpr hfalse
    have hnotnot : S ⊢ₘ[GEN_BOX_CONTENT w] ¬(¬q) :=
      MLK_not_def.mpr himp
    have hq : S ⊢ₘ[GEN_BOX_CONTENT w] q := MLK_DOUBLENEG_CL hnotnot
    have hboxed : S ⊢ₘ[w] □q :=
      box_derivation_from_context hq (fun r hr => hr)
    exact hnbox
      ((MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmaxw hboxsub).mpr
        hboxed)
  have hwfinite : w.Finite :=
    (FINITE_SUBSENTENCE p).subset hsubw
  have hcontentfinite : (GEN_BOX_CONTENT w).Finite := by
    change (Form.box ⁻¹' w).Finite
    exact Set.Finite.preimage
      (fun _ _ _ _ h => Form.box.inj h) hwfinite
  have hfinite : (insert (¬q) (GEN_BOX_CONTENT w)).Finite :=
    hcontentfinite.insert _
  have hsubq : q ⊑ p := Form.of_subformula_box hboxsub
  have hsubs : ∀ r, r ∈ insert (¬q) (GEN_BOX_CONTENT w) → r ⊑ₛ p := by
    intro r hr
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · exact SUBFORMULA_IMP_NEG_SUBSENTENCE hsubq
    · exact content_subsentence_of_box_subsentence (hsubw (□r) hr)
  obtain ⟨X, hmaxX, _, hsubX, hsubset⟩ :=
    EXTEND_MAXIMAL_SETCONSISTENT hconsistent hfinite hsubs
  exact ⟨X, hmaxX, hsubX, hsubset⟩

/-- A maximal extension supplied by `GEN_XK_FOR_ACCESSIBILITY_LEMMA` is a
canonical successor in which the target formula is absent. -/
theorem GEN_ACCESSIBILITY_LEMMA {S w X : Set Form} {p q : Form}
    (_hnp : ¬S ⊢ₘ[(∅ : Set Form)] p)
    (hmaxw : MAXIMAL_SETCONSISTENT S p w)
    (hsubw : ∀ r, r ∈ w → r ⊑ₛ p) (_hboxsub : □q ⊑ p)
    (_hnbox : □q ∉ w) (hmaxX : MAXIMAL_SETCONSISTENT S p X)
    (hsubX : ∀ r, r ∈ X → r ⊑ₛ p)
    (hsubset : insert (¬q) (GEN_BOX_CONTENT w) ⊆ X) :
    GEN_STANDARD_REL S p w X ∧ q ∉ X := by
  constructor
  · refine ⟨hmaxw, hsubw, hmaxX, hsubX, ?_⟩
    intro B hboxB
    apply hsubset
    exact Set.mem_insert_iff.mpr (Or.inr hboxB)
  · intro hqX
    have hnqX : (¬q) ∈ X := hsubset (Set.mem_insert _ _)
    exact hmaxX.1 (MLK_NC_ALT (.hyp hqX) (.hyp hnqX))

/-- The K accessibility context is contained in the context that also keeps
the boxed assumptions.  The historical `SUBLIST` name is retained although
the Lean statement is set inclusion. -/
def GEN_BOX_CONTENT_K4 (w : Set Form) : Set Form :=
  GEN_BOX_CONTENT w ∪ Form.box '' GEN_BOX_CONTENT w

theorem XK_SUBLIST_XK4 (w : Set Form) (q : Form) :
    insert (¬q) (GEN_BOX_CONTENT w) ⊆
      insert (¬q) (GEN_BOX_CONTENT_K4 w) := by
  intro r hr
  rcases Set.mem_insert_iff.mp hr with rfl | hr
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Or.inl hr)

/-! ## Generic countermodels -/

/-- A canonical world containing `¬p` falsifies `p` in every generic standard
model based on the same canonical construction. -/
theorem GEN_COUNTERMODEL {S M : Set Form} {p : Form}
    (model : Model (Set Form)) (hnp : ¬S ⊢ₘ[(∅ : Set Form)] p)
    (hmaxM : MAXIMAL_SETCONSISTENT S p M) (hnotp : (¬p) ∈ M)
    (hsubM : ∀ q, q ∈ M → q ⊑ₛ p)
    (hmodel : GEN_STANDARD_MODEL S p model) :
    ¬Form.holds model.frame model.valuation p M := by
  have hframe := (GEN_STANDARD_MODEL_DEF S p model).mp hmodel |>.1
  have hworlds := (IN_GEN_STANDARD_FRAME S p model.frame).mp hframe |>.1
  have hMworld : M ∈ model.frame.worlds := by
    rw [hworlds]
    exact ⟨hmaxM, hsubM⟩
  have htruth := GEN_TRUTH_LEMMA model hnp hmodel (.refl p) M hMworld
  intro hholds
  have hpM : p ∈ M := htruth.mpr hholds
  exact hmaxM.1 (MLK_NC_ALT (.hyp hpM) (.hyp hnotp))

/-- Every generic standard frame for a non-theorem carries a valuation and a
world that falsify that formula. -/
theorem GEN_COUNTERMODEL_ALT {S : Set Form} {p : Form}
    {frame : Frame (Set Form)} (hnp : ¬S ⊢ₘ[(∅ : Set Form)] p)
    (hframe : frame ∈ GEN_STANDARD_FRAME S p) :
    ¬p.holdsIn frame := by
  obtain ⟨M, hmaxM, hnotp, hsubM⟩ := NONEMPTY_MAXIMAL_SETCONSISTENT hnp
  let model : Model (Set Form) := ⟨frame, STANDARD_EVAL p⟩
  have hmodel : GEN_STANDARD_MODEL S p model := by
    refine (GEN_STANDARD_MODEL_DEF S p model).mpr ⟨hframe, ?_⟩
    intro a w _
    dsimp [model, STANDARD_EVAL]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩
  have hworlds := (IN_GEN_STANDARD_FRAME S p frame).mp hframe |>.1
  have hMworld : M ∈ frame.worlds := by
    rw [hworlds]
    exact ⟨hmaxM, hsubM⟩
  intro hvalid
  exact GEN_COUNTERMODEL model hnp hmaxM hnotp hsubM hmodel
    (hvalid model.valuation M hMworld)

/-! ## Transport to an arbitrary infinite world type -/

/-- Transport a frame along an embedding of its designated-world subtype. -/
private def embeddedFrame {W A : Type*} (frame : Frame W)
    (e : {w // w ∈ frame.worlds} ↪ A) : Frame A where
  worlds := Set.range e
  rel a b := ∃ x y, a = e x ∧ b = e y ∧ frame.rel x.1 y.1

/-- The graph relating each designated world to its embedded copy. -/
private def embeddedWorldRel {W A : Type*} (frame : Frame W)
    (e : {w // w ∈ frame.worlds} ↪ A) : W → A → Prop :=
  fun w a => ∃ hw : w ∈ frame.worlds, a = e ⟨w, hw⟩

/-- Compatible valuations make a frame and its embedded copy bisimilar. -/
private theorem embeddedFrame_bisimulation {W A : Type*} {frame : Frame W}
    (hclosed : ∀ x y, frame.rel x y →
      x ∈ frame.worlds ∧ y ∈ frame.worlds)
    (e : {w // w ∈ frame.worlds} ↪ A) {V : Valuation W} {V' : Valuation A}
    (hatoms : ∀ a x, V a x.1 ↔ V' a (e x)) :
    Bisimulation ⟨frame, V⟩ ⟨embeddedFrame frame e, V'⟩
      (embeddedWorldRel frame e) := by
  intro w a hwa
  rcases hwa with ⟨hw, ha⟩
  subst a
  refine
    { world₁ := hw
      world₂ := ⟨⟨w, hw⟩, rfl⟩
      atoms := fun atom => hatoms atom ⟨w, hw⟩
      forth := ?_
      back := ?_ }
  · intro w' hrel
    have hw' : w' ∈ frame.worlds := (hclosed w w' hrel).2
    refine ⟨e ⟨w', hw'⟩, ⟨⟨w', hw'⟩, rfl⟩, ⟨hw', rfl⟩, ?_⟩
    exact ⟨⟨w, hw⟩, ⟨w', hw'⟩, rfl, rfl, hrel⟩
  · intro a' hrel
    rcases hrel with ⟨x, y, hx, hy, hxy⟩
    have hx' : x = ⟨w, hw⟩ := e.injective hx.symm
    subst x
    refine ⟨y.1, y.2, ⟨y.2, hy⟩, ?_⟩
    exact hxy

/-- Every finite appropriate frame has an isomorphic copy on any infinite
world type. -/
private theorem exists_embedded_appropriate_frame {W A : Type*} [Infinite A]
    {S : Set Form} {frame : Frame W} (hframe : frame ∈ APPR S) :
    ∃ e : {w // w ∈ frame.worlds} ↪ A,
      embeddedFrame frame e ∈ APPR S := by
  classical
  have happr := (IN_APPR S frame).mp hframe
  have hfinite := (IN_FINITE_FRAME frame).mp happr.1
  let _ : Finite {w // w ∈ frame.worlds} := hfinite.2.2.to_subtype
  let e : {w // w ∈ frame.worlds} ↪ A :=
    (Finite.equivFin _).toEmbedding.trans
      (Fin.valEmbedding.trans (Infinite.natEmbedding A))
  refine ⟨e, (IN_APPR S (embeddedFrame frame e)).mpr ⟨?_, ?_⟩⟩
  · apply (IN_FINITE_FRAME (embeddedFrame frame e)).mpr
    refine ⟨?_, ?_, Set.finite_range e⟩
    · obtain ⟨w, hw⟩ := hfinite.1
      exact ⟨e ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩⟩
    · intro a b hab
      rcases hab with ⟨x, y, rfl, rfl, _⟩
      exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  · intro r hr V' a ha
    rcases ha with ⟨x, rfl⟩
    let V : Valuation W := fun atom w =>
      ∃ hw : w ∈ frame.worlds, V' atom (e ⟨w, hw⟩)
    have hatoms : ∀ atom x, V atom x.1 ↔ V' atom (e x) := by
      intro atom x
      constructor
      · rintro ⟨hx, hV⟩
        have heq : (⟨x.1, hx⟩ : {w // w ∈ frame.worlds}) = x :=
          Subtype.ext rfl
        simpa [V, heq] using hV
      · intro hV
        exact ⟨x.2, by simpa [V] using hV⟩
    have hbis := embeddedFrame_bisimulation hfinite.2.1 e hatoms
    have horig : Form.holds frame V r x.1 := happr.2 r hr V x.1 x.2
    exact (Bisimulation.holds_iff hbis ⟨x.2, rfl⟩).mp horig

/-- Validity on appropriate frames over an arbitrary infinite type implies
validity on the set-based canonical-world type. -/
theorem GEN_LEMMA_FOR_GEN_COMPLETENESS {A : Type*} [Infinite A]
    (S : Set Form) {p : Form}
    (hp : p.Valid (APPR S : Set (Frame A))) :
    p.Valid (APPR S : Set (Frame (Set Form))) := by
  apply Form.valid_of_bisimilar ?_ hp
  intro frame hframe V w hw
  obtain ⟨e, hembedded⟩ :=
    exists_embedded_appropriate_frame (A := A) hframe
  let V' : Valuation A := fun atom a =>
    ∃ x : {u // u ∈ frame.worlds}, a = e x ∧ V atom x.1
  have hatoms : ∀ atom x, V atom x.1 ↔ V' atom (e x) := by
    intro atom x
    constructor
    · intro hV
      exact ⟨x, rfl, hV⟩
    · rintro ⟨y, hxy, hV⟩
      have h : x = y := e.injective hxy
      subst y
      exact hV
  have hclosed : ∀ x y, frame.rel x y →
      x ∈ frame.worlds ∧ y ∈ frame.worlds :=
    ((IN_FINITE_FRAME frame).mp ((IN_APPR S frame).mp hframe).1).2.1
  have hbis := embeddedFrame_bisimulation hclosed e hatoms
  refine ⟨embeddedFrame frame e, hembedded, V', e ⟨w, hw⟩, ?_⟩
  exact ⟨embeddedWorldRel frame e, hbis, ⟨hw, rfl⟩⟩

end HOLMS
