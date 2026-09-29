import HOLMS.Calculus

/-!
# Consistent sets of modal formulas

This module is the Lean 4 counterpart of `setconsistent.ml`.  Consistency and
maximal consistency are formulated only for `Set Form`; the redundant
list-based presentation from `consistent.ml` is intentionally not reproduced.
-/

namespace HOLMS

open ModalNotation

/-! ## Consistent sets -/

/-- A set of hypotheses is consistent when it does not derive falsity. -/
def SETCONSISTENT (S X : Set Form) : Prop := ¬S ⊢ₘ[X] ⊥ₘ

/-- A consistent set cannot derive both a formula and its negation. -/
theorem SETCONSISTENT_NC {S w : Set Form} {p : Form}
    (hcons : SETCONSISTENT S w) :
    ¬(S ⊢ₘ[w] p) ∨ ¬(S ⊢ₘ[w] Form.neg p) := by
  classical
  by_contra h
  push Not at h
  exact hcons (MLK_NC_ALT h.1 h.2)

/-- A consistent set cannot contain both a formula and its negation. -/
theorem IN_SETCONSISTENT_NC {S w : Set Form} {p : Form}
    (hcons : SETCONSISTENT S w) : p ∉ w ∨ Form.neg p ∉ w := by
  classical
  by_contra h
  push Not at h
  exact hcons (MLK_NC_ALT (.hyp h.1) (.hyp h.2))

/-- Every subset of a consistent set is consistent. -/
theorem SETCONSISTENT_SUBSET {S X Y : Set Form} (hcons : SETCONSISTENT S X)
    (hYX : Y ⊆ X) : SETCONSISTENT S Y := by
  intro hfalse
  exact hcons (MODPROVES_MONO2 hfalse hYX)

/-- Consistency of a singleton is equivalent to the nonderivability of its
negated member without hypotheses. -/
theorem SETCONSISTENT_SING {S : Set Form} {p : Form} :
    SETCONSISTENT S {p} ↔ ¬(S ⊢ₘ[(∅ : Set Form)] Form.neg p) := by
  have hnot : (S ⊢ₘ[(∅ : Set Form)] Form.neg p) ↔
      (S ⊢ₘ[(∅ : Set Form)] p ⟶ ⊥ₘ) := MLK_not_def
  have hset : insert p (∅ : Set Form) = {p} := by
    ext q
    simp
  have hded : (S ⊢ₘ[(∅ : Set Form)] p ⟶ ⊥ₘ) ↔
      (S ⊢ₘ[({p} : Set Form)] ⊥ₘ) := by
    rw [← hset]
    exact MODPROVES_DEDUCTION_LEMMA
  have h := hnot.trans hded
  exact not_congr h.symm

/-- A consistent set can be extended by either a formula or its negation. -/
theorem SETCONSISTENT_EXTEND_CASES {S X : Set Form} {p : Form}
    (hcons : SETCONSISTENT S X) :
    SETCONSISTENT S (insert p X) ∨ SETCONSISTENT S (insert (¬p) X) := by
  classical
  by_contra h
  push Not at h
  simp only [SETCONSISTENT, not_not] at h
  have hnp : S ⊢ₘ[X] Form.neg p := MLK_not_def.mpr
    (MODPROVES_DEDUCTION_LEMMA.mpr h.1)
  have hnnp : S ⊢ₘ[X] (¬p) ⟶ ⊥ₘ :=
    MODPROVES_DEDUCTION_LEMMA.mpr h.2
  exact hcons (MLK_modusponens hnnp hnp)

/-! ## Maximal consistent sets relative to a formula -/

/-- A consistent set deciding every subformula of `p`. -/
def MAXIMAL_SETCONSISTENT (S : Set Form) (p : Form) (X : Set Form) : Prop :=
  SETCONSISTENT S X ∧ ∀ q, q ⊑ p → q ∈ X ∨ Form.neg q ∈ X

/-- Maximal consistent sets are consistent. -/
theorem MAXIMAL_SETCONSISTENT_IMP_SETCONSISTENT {S X : Set Form} {p : Form}
    (h : MAXIMAL_SETCONSISTENT S p X) : SETCONSISTENT S X := h.1

/-- A maximal consistent set contains each subformula or its negation. -/
theorem IN_MAXIMAL_SETCONSISTENT_CASES {S X : Set Form} {p q : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p X) (hsub : q ⊑ p) :
    q ∈ X ∨ Form.neg q ∈ X := hmax.2 q hsub

/-! ## Subsentences -/

/-- A subsentence of `p` is a subformula of `p` or the negation of one. -/
inductive Subsentence : Form → Form → Prop where
  | ofSubformula {q p : Form} : q ⊑ p → Subsentence q p
  | negOfSubformula {q p : Form} : q ⊑ p → Subsentence (¬q) p

namespace ModalNotation

scoped infix:50 " ⊑ₛ " => Subsentence

end ModalNotation

open ModalNotation

/-- Every subformula is a subsentence. -/
theorem SUBFORMULA_IMP_SUBSENTENCE {p q : Form} (h : p ⊑ q) : p ⊑ₛ q :=
  .ofSubformula h

/-- The negation of every subformula is a subsentence. -/
theorem SUBFORMULA_IMP_NEG_SUBSENTENCE {p q : Form} (h : p ⊑ q) :
    (¬p) ⊑ₛ q := .negOfSubformula h

/-- Subsentences are exactly subformulas and their negations. -/
theorem SUBSENTENCE_EQ_SUBFORMULA (p : Form) :
    {q | q ⊑ₛ p} = {q | q ⊑ p} ∪ Form.neg '' {q | q ⊑ p} := by
  ext q
  constructor
  · intro h
    cases h with
    | ofSubformula hsub => exact Or.inl hsub
    | negOfSubformula hsub => exact Or.inr ⟨_, hsub, rfl⟩
  · rintro (hsub | ⟨q, hsub, rfl⟩)
    · exact .ofSubformula hsub
    · exact .negOfSubformula hsub

/-- Every formula has finitely many subsentences. -/
theorem FINITE_SUBSENTENCE (p : Form) : Set.Finite {q | q ⊑ₛ p} := by
  rw [SUBSENTENCE_EQ_SUBFORMULA]
  exact (Form.finite_subformulas p).union
    ((Form.finite_subformulas p).image Form.neg)

/-! ## Membership and derivability -/

/-- For a subformula, membership in a maximal consistent set is equivalent to
derivability from that set. -/
theorem MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE
    {S w : Set Form} {p q : Form} (hmax : MAXIMAL_SETCONSISTENT S p w)
    (hsub : q ⊑ p) : q ∈ w ↔ S ⊢ₘ[w] q := by
  constructor
  · exact MODPROVES_HP
  · intro hq
    by_contra hnmem
    rcases hmax.2 q hsub with hmem | hnq
    · exact hnmem hmem
    · exact hmax.1 (MLK_NC_ALT hq (.hyp hnq))

/-- The analogous membership characterization for negated subformulas. -/
theorem MAXIMAL_SETCONSISTENT_NOT_SUBFORMULA_MEMBER_IFF_DERIVABLE
    {S w : Set Form} {p q : Form} (hmax : MAXIMAL_SETCONSISTENT S p w)
    (hsub : q ⊑ p) : Form.neg q ∈ w ↔ S ⊢ₘ[w] Form.neg q := by
  constructor
  · exact MODPROVES_HP
  · intro hnq
    by_contra hnmem
    rcases hmax.2 q hsub with hq | hmem
    · exact hmax.1 (MLK_NC_ALT (.hyp hq) hnq)
    · exact hnmem hmem

/-- A derivable subformula belongs to every maximal consistent superset of
the hypotheses used in its derivation. -/
theorem MAXIMAL_SETCONSISTENT_LEMMA {S X A : Set Form} {p b : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p X) (hAX : A ⊆ X) (hsub : b ⊑ p)
    (hb : S ⊢ₘ[A] b) : b ∈ X :=
  (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mpr
    (MODPROVES_MONO2 hb hAX)

/-! ## Closure properties -/

/-- A maximal consistent set contains truth whenever truth is among the
subformulas under consideration. -/
theorem MAXIMAL_SETCONSISTENT_TRUE_CLOSED {S w : Set Form} {p : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p w) (hsub : ⊤ₘ ⊑ p) : ⊤ₘ ∈ w :=
  (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mpr
    MLK_truth_th

/-- Membership of a negated subformula is complementary to membership of the
subformula. -/
theorem MAXIMAL_SETCONSISTENT_NOT_CLOSED {S w : Set Form} {p q : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p w) (hsub : Form.neg q ⊑ p) :
    Form.neg q ∈ w ↔ q ∉ w := by
  have hqsub : q ⊑ p := Form.of_subformula_neg hsub
  constructor
  · intro hnq hq
    exact hmax.1 (MLK_NC_ALT (.hyp hq) (.hyp hnq))
  · intro hnq
    rcases hmax.2 q hqsub with hq | hnqmem
    · exact False.elim (hnq hq)
    · exact hnqmem

/-- A conjunction belongs to a maximal consistent set exactly when both
conjuncts belong to it.  The misspelling `MIONOR` is retained for compatibility
with the HOL Light theorem name. -/
theorem MAXIMAL_SETCONSISTENT_AND_MIONOR_CLOSED
    {S w : Set Form} {p q₁ q₂ : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p w) (hsub : q₁ ⋏ q₂ ⊑ p) :
    q₁ ⋏ q₂ ∈ w ↔ q₁ ∈ w ∧ q₂ ∈ w := by
  have hq₁ : q₁ ⊑ p := Form.of_subformula_conj_left hsub
  have hq₂ : q₂ ⊑ p := Form.of_subformula_conj_right hsub
  rw [MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub,
    MLK_and,
    ← MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hq₁,
    ← MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hq₂]

/-- A disjunction belongs to a maximal consistent set exactly when one of its
disjuncts belongs to it. -/
theorem MAXIMAL_SETCONSISTENT_MINOR_OR_CLOSED
    {S w : Set Form} {p q₁ q₂ : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p w) (hsub : q₁ ⋎ q₂ ⊑ p) :
    q₁ ⋎ q₂ ∈ w ↔ q₁ ∈ w ∨ q₂ ∈ w := by
  have hq₁ : q₁ ⊑ p := Form.of_subformula_disj_left hsub
  have hq₂ : q₂ ⊑ p := Form.of_subformula_disj_right hsub
  constructor
  · intro hor
    classical
    by_contra hnone
    push Not at hnone
    have hnq₁ : Form.neg q₁ ∈ w :=
      (hmax.2 q₁ hq₁).resolve_left hnone.1
    have hnq₂ : Form.neg q₂ ∈ w :=
      (hmax.2 q₂ hq₂).resolve_left hnone.2
    have hdor : S ⊢ₘ[w] q₁ ⋎ q₂ :=
      (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mp hor
    exact hmax.1 (MLK_NC_ALT hdor (MLK_proves_not_or (.hyp hnq₁) (.hyp hnq₂)))
  · rintro (hq₁mem | hq₂mem)
    · apply (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mpr
      exact MLK_or_introl q₂ (.hyp hq₁mem)
    · apply (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mpr
      exact MLK_or_intror q₁ (.hyp hq₂mem)

/-- An implication belongs to a maximal consistent set exactly when
membership of its antecedent entails membership of its consequent. -/
theorem MAXIMAL_SETCONSISTENT_IMP_CLOSED
    {S w : Set Form} {p q₁ q₂ : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p w) (hsub : (q₁ ⟶ q₂) ⊑ p) :
    (q₁ ⟶ q₂) ∈ w ↔ (q₁ ∈ w → q₂ ∈ w) := by
  have hq₁ : q₁ ⊑ p := Form.of_subformula_imp_left hsub
  have hq₂ : q₂ ⊑ p := Form.of_subformula_imp_right hsub
  constructor
  · intro himp hq₁mem
    apply (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hq₂).mpr
    exact MLK_modusponens
      ((MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mp himp)
      (.hyp hq₁mem)
  · intro hmem
    apply (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mpr
    rcases hmax.2 q₁ hq₁ with hq₁mem | hnq₁mem
    · exact MLK_add_assum q₁ (.hyp (hmem hq₁mem))
    · exact MLK_imp_introl (.hyp hnq₁mem)

/-- An equivalence belongs to a maximal consistent set exactly when its two
sides have the same membership status. -/
theorem MAXIMAL_SETCONSISTENT_IFF_CLOSED
    {S w : Set Form} {p q₁ q₂ : Form}
    (hmax : MAXIMAL_SETCONSISTENT S p w) (hsub : (q₁ ⟷ q₂) ⊑ p) :
    (q₁ ⟷ q₂) ∈ w ↔ (q₁ ∈ w ↔ q₂ ∈ w) := by
  have hq₁ : q₁ ⊑ p := Form.of_subformula_iff_left hsub
  have hq₂ : q₂ ⊑ p := Form.of_subformula_iff_right hsub
  constructor
  · intro hiff
    have hd : S ⊢ₘ[w] q₁ ⟷ q₂ :=
      (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mp hiff
    constructor
    · intro h₁
      apply (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hq₂).mpr
      exact MLK_modusponens (MLK_iff_imp1 hd) (.hyp h₁)
    · intro h₂
      apply (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hq₁).mpr
      exact MLK_modusponens (MLK_iff_imp2 hd) (.hyp h₂)
  · intro hmem
    apply (MAXIMAL_SETCONSISTENT_SUBFORMULA_MEMBER_IFF_DERIVABLE hmax hsub).mpr
    rcases hmax.2 q₁ hq₁ with hq₁mem | hnq₁mem
    · exact MLK_proves_iff_pos (.hyp hq₁mem) (.hyp (hmem.mp hq₁mem))
    · have hnq₁ : q₁ ∉ w := fun hq₁mem =>
        hmax.1 (MLK_NC_ALT (.hyp hq₁mem) (.hyp hnq₁mem))
      have hnq₂ : q₂ ∉ w := fun hq₂mem => hnq₁ (hmem.mpr hq₂mem)
      rcases hmax.2 q₂ hq₂ with hq₂mem | hnq₂mem
      · exact False.elim (hnq₂ hq₂mem)
      · exact MLK_proves_iff_neg (.hyp hnq₁mem) (.hyp hnq₂mem)

/-! ## Maximal extension -/

/-- Every finite consistent set of subsentences of `p` extends to a finite
maximal consistent set of subsentences of `p`. -/
theorem EXTEND_MAXIMAL_SETCONSISTENT {S X : Set Form} {p : Form}
    (hcons : SETCONSISTENT S X) (hfinite : X.Finite)
    (hsubs : ∀ q, q ∈ X → q ⊑ₛ p) :
    ∃ M, MAXIMAL_SETCONSISTENT S p M ∧ M.Finite ∧
      (∀ q, q ∈ M → q ⊑ₛ p) ∧ X ⊆ M := by
  classical
  have extend : ∀ s : Finset Form,
      (∀ q, q ∈ s → q ⊑ p) →
      ∀ Y : Set Form, SETCONSISTENT S Y → Y.Finite →
        (∀ q, q ∈ Y → q ⊑ₛ p) →
        (∀ q, q ⊑ p → q ∈ s ∨ q ∈ Y ∨ Form.neg q ∈ Y) →
        ∃ M, MAXIMAL_SETCONSISTENT S p M ∧ M.Finite ∧
          (∀ q, q ∈ M → q ⊑ₛ p) ∧ Y ⊆ M := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ Y hY hYfinite hYsubs hdecides
        refine ⟨Y, ⟨hY, ?_⟩, hYfinite, hYsubs, Set.Subset.rfl⟩
        intro q hq
        simpa using hdecides q hq
    | @insert x s hx ih =>
        intro hs Y hY hYfinite hYsubs hdecides
        have hxsub : x ⊑ p := hs x (by simp)
        have hssub : ∀ q, q ∈ s → q ⊑ p := by
          intro q hq
          exact hs q (by simp [hq])
        obtain ⟨y, hy, hY'⟩ : ∃ y, (y = x ∨ y = Form.neg x) ∧
            SETCONSISTENT S (insert y Y) := by
          rcases SETCONSISTENT_EXTEND_CASES (S := S) (X := Y) (p := x) hY with
            hpos | hneg
          · exact ⟨x, Or.inl rfl, hpos⟩
          · exact ⟨Form.neg x, Or.inr rfl, hneg⟩
        have hnewsubs : ∀ q, q ∈ insert y Y → q ⊑ₛ p := by
          intro q hq
          rcases hq with rfl | hq
          · rcases hy with rfl | rfl
            · exact .ofSubformula hxsub
            · exact .negOfSubformula hxsub
          · exact hYsubs q hq
        have hnewdecides : ∀ q, q ⊑ p →
            q ∈ s ∨ q ∈ insert y Y ∨ Form.neg q ∈ insert y Y := by
          intro q hq
          rcases hdecides q hq with hqs | hqY | hnqY
          · rw [Finset.mem_insert] at hqs
            rcases hqs with rfl | hqs
            · rcases hy with rfl | rfl
              · exact Or.inr (Or.inl (Set.mem_insert _ _))
              · exact Or.inr (Or.inr (Set.mem_insert _ _))
            · exact Or.inl hqs
          · exact Or.inr (Or.inl (Set.mem_insert_of_mem _ hqY))
          · exact Or.inr (Or.inr (Set.mem_insert_of_mem _ hnqY))
        obtain ⟨M, hMmax, hMfinite, hMsubs, hYM⟩ :=
          ih hssub (insert y Y) hY' (hYfinite.insert y) hnewsubs hnewdecides
        exact ⟨M, hMmax, hMfinite, hMsubs,
          fun q hq => hYM (Set.mem_insert_of_mem y hq)⟩
  apply extend p.subformulas
  · intro q hq
    exact Form.mem_subformulas_iff.mp hq
  · exact hcons
  · exact hfinite
  · exact hsubs
  · intro q hq
    exact Or.inl (Form.mem_subformulas_iff.mpr hq)

/-- Every formula not derivable without hypotheses has a maximal consistent
set of its subsentences containing its negation. -/
theorem NONEMPTY_MAXIMAL_SETCONSISTENT {S : Set Form} {p : Form}
    (hp : ¬(S ⊢ₘ[(∅ : Set Form)] p)) :
    ∃ M, MAXIMAL_SETCONSISTENT S p M ∧ Form.neg p ∈ M ∧
      ∀ q, q ∈ M → q ⊑ₛ p := by
  have hsingleton : SETCONSISTENT S ({Form.neg p} : Set Form) := by
    rw [SETCONSISTENT_SING]
    intro hnnp
    exact hp (MLK_DOUBLENEG_CL hnnp)
  obtain ⟨M, hmax, _, hsubs, hcontains⟩ :=
    EXTEND_MAXIMAL_SETCONSISTENT hsingleton (Set.finite_singleton _)
      (fun q hq => by
        have hq' : q = Form.neg p := by simpa using hq
        subst q
        exact .negOfSubformula (.refl p))
  exact ⟨M, hmax, hcontains (by simp), hsubs⟩

end HOLMS
