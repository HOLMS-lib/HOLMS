import HOLMS.LabelledSoundness

/-!
# The labelled calculus for modal logic K

This module assembles the reusable labelled rules into K, supplies its
capability instance, specializes generic Kripke soundness, and records
K-specific certificate tests. The underlying rule schemas and proof-tree
infrastructure remain in `HOLMS.Labelled`.
-/

namespace HOLMS.Labelled

/-- K contains exactly the standard propositional and modal rule families. -/
-- HOL: no direct labelled counterpart; deep-embedding analogue of modal K.
def K : Calculus := standardCalculus

/-- K includes the shared propositional and modal core. -/
-- HOL: no direct labelled counterpart; rule availability for labelled K.
instance : HasCore K := ⟨Calculus.Included.refl _⟩

/-- K never accepts a node carrying the reflexivity rule. -/
-- HOL: no direct labelled counterpart; certificate-level separation of K and T.
theorem not_valid_k_refl (s : Sequent) (x : Label) (ds : List ProofTree) :
    ¬Valid K (.node s ⟨"refl", [.label x]⟩ ds) := by
  intro h
  have hs := (valid_node_iff.mp h).1
  simp [Calculus.step, K, standardCalculus, propositionalCalculus,
    Calculus.unions, Calculus.union, Calculus.singleton, Calculus.empty] at hs

/-- A box-right node with no premise cannot be a valid K certificate. -/
-- HOL: no direct labelled counterpart; arity rejection in labelled K.
theorem boxRight_leaf_not_valid_k (s : Sequent) (x y : Label) (a : Form) :
    ¬Valid K (.node s
      ⟨"boxRight", [.label x, .label y, .formula a]⟩ []) := by
  intro h
  have hs := (valid_node_iff.mp h).1
  have hbox : BoxRightStep [.label x, .label y, .formula a] [] s := by
    simpa [Calculus.step, K, standardCalculus, propositionalCalculus,
      Calculus.unions, Calculus.union, Calculus.singleton, Calculus.empty] using hs
  cases hbox

/-- The labelled K calculus is sound on every Kripke frame. -/
-- HOL: no direct labelled counterpart; soundness of labelled K.
theorem K_soundOn {W : Type*} (frame : Frame W) : K.SoundOn frame := by
  simpa only [K] using standardCalculus_soundOn frame

/-- Every K-derivable labelled sequent is valid on every Kripke frame. -/
-- HOL: no direct labelled counterpart; derivability soundness for labelled K.
theorem K_derivable_sound {W : Type*} {frame : Frame W} {s : Sequent}
    (hderivable : Derivable K s) : s.ValidOn frame :=
  hderivable.soundOn (K_soundOn frame)

-- Branching example checks conjunction-right and both identity leaves.
-- HOL: no direct labelled counterpart; regression certificate for labelled K.
example : Valid K (conjunctionTree 0 (.atom "p")) := conjunctionTree_valid K 0 _

-- Concrete K certificate exercising both modal rules and freshness.
-- HOL: no direct labelled counterpart; regression certificate for labelled K.
example : Valid K (boxedIdentityTree 0 1 (.atom "p")) :=
  boxedIdentityTree_valid K 0 1 _ (by decide)

end HOLMS.Labelled
