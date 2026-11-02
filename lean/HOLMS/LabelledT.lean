import HOLMS.LabelledK

/-!
# The labelled calculus for modal logic T

T extends labelled K with the reusable reflexivity rule family. This module
contains the system composition, K-to-T inclusion, the explicit T-schema
certificate, and soundness on reflexive Kripke frames.
-/

namespace HOLMS.Labelled

/-- T extends K by the reflexivity rule family. -/
-- HOL: no direct labelled counterpart; deep-embedding analogue of modal T.
def T : Calculus := K.union reflCalculus

/-- T includes the shared core through its K component. -/
-- HOL: no direct labelled counterpart; core availability for labelled T.
instance : HasCore T := ⟨Calculus.included_union_left _ _⟩

/-- The reflexivity family is available in T. -/
-- HOL: no direct labelled counterpart; T-rule availability.
instance : HasRefl T := ⟨Calculus.included_union_right _ _⟩

/-- Every K step is also a T step. -/
-- HOL: no direct labelled counterpart; inclusion of labelled calculi.
theorem k_included_t : K.Included T := by
  exact Calculus.included_union_left _ _

/-- A K-valid tree remains valid in T without changing the tree. -/
-- HOL: no direct labelled counterpart; certificate monotonicity from K to T.
theorem Valid.k_to_t {d : ProofTree} (h : Valid K d) : Valid T d :=
  h.mono k_included_t

/-- A certificate for `x : □a ⊢ x : a`, using box-left and reflexivity. -/
-- HOL: no direct labelled counterpart; internal certificate stage for the T schema.
def reflexiveBoxTree (x : Label) (a : Form) : ProofTree :=
  .node ⟨0, {⟨x, .box a⟩}, {⟨x, a⟩}⟩
    ⟨"refl", [.label x]⟩ [boxUseTree 0 x x a]

/-- The reflexive box certificate needs propositional rules, box-left, and reflexivity. -/
-- HOL: no direct labelled counterpart; validity of `reflexiveBoxTree`.
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
-- HOL: labelled certificate counterpart of the T schema.
def tAxiomTree (x : Label) (a : Form) : ProofTree :=
  .node ⟨0, 0, {⟨x, .imp (.box a) a⟩}⟩
    ⟨"impRight", [.label x, .formula (.box a), .formula a]⟩
    [reflexiveBoxTree x a]

/-- The T-axiom tree needs no box-right capability. -/
-- HOL: labelled certificate counterpart of the T schema.
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
-- HOL: no direct labelled counterpart; certificate-level separation of K and T.
theorem tAxiomTree_not_valid_k (x : Label) (a : Form) :
    ¬Valid K (tAxiomTree x a) := by
  intro h
  have hc := (valid_node_iff.mp h).2 (reflexiveBoxTree x a) (by simp)
  exact not_valid_k_refl _ _ _ hc

/-- The labelled T calculus is sound on every reflexive Kripke frame. -/
-- HOL: no direct labelled counterpart; soundness of labelled T.
theorem T_soundOn {W : Type*} {frame : Frame W}
    (hrefl : REFLEXIVE frame.worlds frame.rel) : T.SoundOn frame := by
  exact (K_soundOn frame).union (reflCalculus_soundOn hrefl)

/-- Every T-derivable labelled sequent is valid on every reflexive Kripke frame. -/
-- HOL: no direct labelled counterpart; derivability soundness for labelled T.
theorem T_derivable_sound {W : Type*} {frame : Frame W}
    (hrefl : REFLEXIVE frame.worlds frame.rel) {s : Sequent}
    (hderivable : Derivable T s) : s.ValidOn frame :=
  hderivable.soundOn (T_soundOn hrefl)

-- The identical raw K certificate is accepted in T by monotonicity.
-- HOL: no direct labelled counterpart; regression example for `K ⊆ T`.
example : Valid T (boxedIdentityTree 0 1 (.atom "p")) :=
  (boxedIdentityTree_valid K 0 1 _ (by decide)).k_to_t

-- Class-based validation of a concrete T-axiom certificate.
-- HOL: no direct labelled counterpart; regression example for labelled T.
example : Valid T (tAxiomTree 0 (.atom "p")) := tAxiomTree_valid T 0 _

-- The same T-axiom certificate is rejected in K.
-- HOL: no direct labelled counterpart; regression example separating K and T.
example : ¬Valid K (tAxiomTree 0 (.atom "p")) := tAxiomTree_not_valid_k 0 _

-- Structural measures compute on data without validity proofs.
-- HOL: no direct labelled counterpart; computation on the explicit T certificate.
example : (tAxiomTree 0 (.atom "p")).height = 4 ∧
    (tAxiomTree 0 (.atom "p")).nodes = 4 := by
  norm_num [tAxiomTree, reflexiveBoxTree, boxUseTree, ProofTree.height, ProofTree.nodes]

section CapabilityRegression

/-- A test calculus retaining T's rules except for standard box-right. -/
-- HOL: no direct labelled counterpart; regression calculus for granular capabilities.
private def noBoxRight : Calculus := Calculus.unions
  [propositionalCalculus, boxLeftCalculus, reflCalculus]

-- The test calculus has propositional rules despite missing box-right.
-- HOL: no direct labelled counterpart; local capability witness.
local instance : HasPropositionalCore noBoxRight where
  included := Calculus.included_unions_of_mem (by simp)

-- Standard box-left remains available in the restricted test calculus.
-- HOL: no direct labelled counterpart; local capability witness.
local instance : HasBoxLeft noBoxRight where
  included := Calculus.included_unions_of_mem (by simp)

-- Reflexivity remains available independently of box-right.
-- HOL: no direct labelled counterpart; local capability witness.
local instance : HasRefl noBoxRight where
  included := Calculus.included_unions_of_mem (by simp)

-- The propositional certificate works without full-core availability.
-- HOL: no direct labelled counterpart; granular-capability regression example.
example : Valid noBoxRight (conjunctionTree 0 (.atom "p")) :=
  conjunctionTree_valid noBoxRight 0 _

-- T's axiom certificate does not require the missing box-right rule.
-- HOL: no direct labelled counterpart; granular-capability regression example.
example : Valid noBoxRight (tAxiomTree 0 (.atom "p")) :=
  tAxiomTree_valid noBoxRight 0 _

-- The restricted calculus rejects the certificate that uses standard box-right.
-- HOL: no direct labelled counterpart; granular-capability regression example.
example : ¬Valid noBoxRight (boxedIdentityTree 0 1 (.atom "p")) := by
  intro h
  have hs := (valid_node_iff.mp h).1
  simp [Calculus.step, noBoxRight, propositionalCalculus, Calculus.unions,
    Calculus.union, Calculus.singleton, Calculus.empty] at hs

end CapabilityRegression

end HOLMS.Labelled
