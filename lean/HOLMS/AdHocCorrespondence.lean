import HOLMS.Calculus

/-!
# Ad hoc correspondence theory

This module defines the standard modal axiom schemata and the corresponding
properties of Kripke relations, then proves their frame-correspondence
theorems.
-/

namespace HOLMS

open ModalNotation

/-! ## Axiom schemata -/

/-- Seriality axiom `D`: `□p → ◇p`. -/
-- HOL: `D_SCHEMA` (definition: `D_SCHEMA_DEF`) (`ad_hoc_correspondence.ml`).
def D_SCHEMA (p : Form) : Form := □p ⟶ ◇p

/-- Reflexivity axiom `T`: `□p → p`. -/
-- HOL: `T_SCHEMA` (definition: `T_SCHEMA_DEF`) (`ad_hoc_correspondence.ml`).
def T_SCHEMA (p : Form) : Form := □p ⟶ p

/-- Transitivity axiom `4`: `□p → □□p`. -/
-- HOL: `FOUR_SCHEMA` (definition: `FOUR_SCHEMA_DEF`) (`ad_hoc_correspondence.ml`).
def FOUR_SCHEMA (p : Form) : Form := □p ⟶ □□p

/-- Symmetry axiom `B`: `p → □◇p`. -/
-- HOL: `B_SCHEMA` (definition: `B_SCHEMA_DEF`) (`ad_hoc_correspondence.ml`).
def B_SCHEMA (p : Form) : Form := p ⟶ □(◇p)

/-- Euclideanity axiom `5`: `◇p → □◇p`. -/
-- HOL: `FIVE_SCHEMA` (definition: `FIVE_SCHEMA_DEF`) (`ad_hoc_correspondence.ml`).
def FIVE_SCHEMA (p : Form) : Form := ◇p ⟶ □(◇p)

/-- Löb's axiom. -/
-- HOL: `LOB_SCHEMA` (definition: `LOB_SCHEMA_DEF`) (`ad_hoc_correspondence.ml`).
def LOB_SCHEMA (p : Form) : Form := □(□p ⟶ p) ⟶ □p

/-- Grzegorczyk's axiom. -/
-- HOL: `GRZ_SCHEMA` (definition: `GRZ_SCHEMA_DEF`) (`ad_hoc_correspondence.ml`).
def GRZ_SCHEMA (p : Form) : Form := □(□(p ⟶ □p) ⟶ p) ⟶ p

/-! ## Properties of a relation on a set of worlds -/

/-- Every world has a successor in the set of worlds. -/
-- HOL: `SERIAL` (`ad_hoc_correspondence.ml`).
def SERIAL {W : Type*} (worlds : Set W) (rel : W → W → Prop) : Prop :=
  ∀ w, w ∈ worlds → ∃ y, y ∈ worlds ∧ rel w y

/-- Every world is related to itself. -/
-- HOL: `REFLEXIVE` (`ad_hoc_correspondence.ml`).
def REFLEXIVE {W : Type*} (worlds : Set W) (rel : W → W → Prop) : Prop :=
  ∀ w, w ∈ worlds → rel w w

/-- No world is related to itself. -/
-- HOL: `IRREFLEXIVE` (`ad_hoc_correspondence.ml`).
def IRREFLEXIVE {W : Type*} (worlds : Set W) (rel : W → W → Prop) : Prop :=
  ∀ w, w ∈ worlds → ¬rel w w

/-- Relational transitivity, restricted to the designated worlds. -/
-- HOL: `TRANSITIVE` (`ad_hoc_correspondence.ml`).
def TRANSITIVE {W : Type*} (worlds : Set W) (rel : W → W → Prop) : Prop :=
  ∀ w w' w'', w ∈ worlds → w' ∈ worlds → w'' ∈ worlds →
    rel w w' → rel w' w'' → rel w w''

/-- Relational symmetry, restricted to the designated worlds. -/
-- HOL: `SYMMETRIC` (`ad_hoc_correspondence.ml`).
def SYMMETRIC {W : Type*} (worlds : Set W) (rel : W → W → Prop) : Prop :=
  ∀ w w', w ∈ worlds → w' ∈ worlds → rel w w' → rel w' w

/-- Relational antisymmetry, restricted to the designated worlds. -/
-- HOL: `ANTISYMMETRIC` (`ad_hoc_correspondence.ml`).
def ANTISYMMETRIC {W : Type*} (worlds : Set W) (rel : W → W → Prop) : Prop :=
  ∀ w w', w ∈ worlds → w' ∈ worlds → rel w w' → rel w' w → w = w'

/-- Euclideanity on designated worlds: `rel w w'` and `rel w w''` imply
`rel w'' w'`. -/
-- HOL: `EUCLIDEAN` (`ad_hoc_correspondence.ml`).
def EUCLIDEAN {W : Type*} (worlds : Set W) (rel : W → W → Prop) : Prop :=
  ∀ w w' w'', w ∈ worlds → w' ∈ worlds → w'' ∈ worlds →
    rel w w' → rel w w'' → rel w'' w'

/-- The field of a relation: the points occurring at either end of an edge. -/
-- HOL: `fld`, the HOL Light relation field used in `WWF` (`ad_hoc_correspondence.ml`).
def relField {W : Type*} (rel : W → W → Prop) : Set W :=
  {x | ∃ y, rel x y ∨ rel y x}

/-- Weak well-foundedness: every nonempty predicate contained in the field has
a minimal point with respect to the strict part of `rel`. -/
-- HOL: `WWF` (`ad_hoc_correspondence.ml`).
def WWF {W : Type*} (rel : W → W → Prop) : Prop :=
  ∀ P : W → Prop, (∃ x, P x) ∧ (∀ x, P x → x ∈ relField rel) →
    ∃ x, P x ∧ ∀ y, y ≠ x → rel y x → ¬P y

/-- The field-based definition of weak well-foundedness is equivalent to
ordinary well-foundedness of the strict part of the relation. -/
-- HOL: no named counterpart; bridge from `WWF` to Lean's `WellFounded`.
theorem wwf_iff_wellFounded_strict {W : Type*} (rel : W → W → Prop) :
    WWF rel ↔ WellFounded (fun y x => y ≠ x ∧ rel y x) := by
  rw [WellFounded.wellFounded_iff_has_min]
  constructor
  · intro h s hs
    by_cases hsub : ∀ x, x ∈ s → x ∈ relField rel
    · obtain ⟨m, hm, hmin⟩ := h (fun x => x ∈ s) ⟨hs, hsub⟩
      exact ⟨m, hm, fun y hy hrel => hmin y hrel.1 hrel.2 hy⟩
    · push Not at hsub
      obtain ⟨m, hm, hmfield⟩ := hsub
      refine ⟨m, hm, fun y _ hrel => ?_⟩
      exact hmfield ⟨y, Or.inr hrel.2⟩
  · intro hwf P ⟨hne, hfield⟩
    obtain ⟨m, hm, hmin⟩ := hwf {x | P x} hne
    exact ⟨m, hm, fun y hy hrel hPy => hmin y hPy ⟨hy, hrel⟩⟩

/-- Weak well-foundedness characterized by minimal elements. -/
-- HOL: `WWF_EQ` (`ad_hoc_correspondence.ml`).
theorem WWF_EQ {W : Type*} (rel : W → W → Prop) :
    WWF rel ↔ ∀ P : W → Prop, (∀ x, P x → x ∈ relField rel) →
      ((∃ x, P x) ↔ ∃ x, P x ∧ ∀ y, y ≠ x → rel y x → ¬P y) := by
  constructor
  · intro h P hfield
    constructor
    · intro hne
      exact h P ⟨hne, hfield⟩
    · rintro ⟨x, hx, _⟩
      exact ⟨x, hx⟩
  · intro h P ⟨hne, hfield⟩
    exact (h P hfield).mp hne

/-- Weak well-foundedness characterized by induction over strict predecessors. -/
-- HOL: `WWF_IND` (`ad_hoc_correspondence.ml`).
theorem WWF_IND {W : Type*} (rel : W → W → Prop) :
    WWF rel ↔ ∀ P : W → Prop,
      (∀ x, ¬P x → x ∈ relField rel) →
      (∀ x, (∀ y, rel y x → y ≠ x → P y) → P x) → ∀ x, P x := by
  constructor
  · intro hwf P _ hP x
    have hstrict := (wwf_iff_wellFounded_strict rel).mp hwf
    exact hstrict.induction x
      (fun x ih => hP x fun y hyr hy => ih y ⟨hy, hyr⟩)
  · intro hind P ⟨hne, hfield⟩
    classical
    by_contra hminimal
    push Not at hminimal
    have hall : ∀ x, ¬P x := hind (fun x => ¬P x)
      (fun x hx => hfield x (not_not.mp hx)) (fun x ih hx => by
        obtain ⟨y, hy, hyx, hPy⟩ := hminimal x hx
        exact (ih y hyx hy) hPy)
    obtain ⟨x, hx⟩ := hne
    exact hall x hx

/-! ## Elementary correspondence theorems -/

/-- `D` is valid exactly on serial frames. -/
-- HOL: `MODAL_SER` (`ad_hoc_correspondence.ml`).
theorem MODAL_SER {W : Type*} (worlds : Set W) (rel : W → W → Prop) :
    SERIAL worlds rel ↔ ∀ p, Form.holdsIn ⟨worlds, rel⟩ (D_SCHEMA p) := by
  constructor
  · intro hserial p valuation w hw hbox
    obtain ⟨y, hy, hrel⟩ := hserial w hw
    simp only [Form.holds, Form.diam]
    intro hnot
    exact hnot y hy hrel (hbox y hy hrel)
  · intro hvalid w hw
    let valuation : Valuation W := fun _ y => rel w y
    have h := hvalid (Form.atom "p") valuation w hw
    simp only [D_SCHEMA, Form.holds, Form.diam] at h
    by_contra hsucc
    have hbox : ∀ y, y ∈ worlds → rel w y → valuation "p" y := by
      intro y _ hry
      exact hry
    have hdiam := h hbox
    push Not at hdiam
    obtain ⟨y, hy, hry⟩ := hdiam
    exact hsucc ⟨y, hy, by simpa [valuation] using hry⟩

/-- `T` is valid exactly on reflexive frames. -/
-- HOL: `MODAL_REFL` (`ad_hoc_correspondence.ml`).
theorem MODAL_REFL {W : Type*} (worlds : Set W) (rel : W → W → Prop) :
    REFLEXIVE worlds rel ↔ ∀ p, Form.holdsIn ⟨worlds, rel⟩ (T_SCHEMA p) := by
  constructor
  · intro hrefl p valuation w hw hbox
    exact hbox w hw (hrefl w hw)
  · intro hvalid w hw
    let valuation : Valuation W := fun _ y => rel w y
    have h := hvalid (Form.atom "p") valuation w hw
    exact h (fun y _ hry => hry)

/-- `4` is valid exactly on transitive frames. -/
-- HOL: `MODAL_TRANS` (`ad_hoc_correspondence.ml`).
theorem MODAL_TRANS {W : Type*} (worlds : Set W) (rel : W → W → Prop) :
    TRANSITIVE worlds rel ↔ ∀ p, Form.holdsIn ⟨worlds, rel⟩ (FOUR_SCHEMA p) := by
  constructor
  · intro htrans p valuation w hw hbox y hy hwy z hz hyz
    exact hbox z hz (htrans w y z hw hy hz hwy hyz)
  · intro hvalid w y z hw hy hz hwy hyz
    let valuation : Valuation W := fun _ u => rel w u
    have h := hvalid (Form.atom "p") valuation w hw
    exact h (fun u _ hwu => hwu) y hy hwy z hz hyz

/-- `B` is valid exactly on symmetric frames. -/
-- HOL: `MODAL_SYM` (`ad_hoc_correspondence.ml`).
theorem MODAL_SYM {W : Type*} (worlds : Set W) (rel : W → W → Prop) :
    SYMMETRIC worlds rel ↔ ∀ p, Form.holdsIn ⟨worlds, rel⟩ (B_SCHEMA p) := by
  constructor
  · intro hsym p valuation w hw hp y hy hwy
    simp only [Form.holds, Form.diam]
    intro hnot
    exact hnot w hw (hsym w y hw hy hwy) hp
  · intro hvalid w y hw hy hwy
    let valuation : Valuation W := fun _ u => u = w
    have h := hvalid (Form.atom "p") valuation w hw rfl y hy hwy
    simp only [Form.holds, Form.diam] at h
    by_contra hnot
    apply h
    intro z _ hyz hz
    subst z
    exact hnot hyz

/-- `5` is valid exactly on Euclidean frames. -/
-- HOL: `MODAL_EUCL` (`ad_hoc_correspondence.ml`).
theorem MODAL_EUCL {W : Type*} (worlds : Set W) (rel : W → W → Prop) :
    EUCLIDEAN worlds rel ↔ ∀ p, Form.holdsIn ⟨worlds, rel⟩ (FIVE_SCHEMA p) := by
  constructor
  · intro heucl p valuation w hw hdiam y hy hwy
    simp only [Form.holds, Form.diam] at hdiam ⊢
    intro hnot
    apply hdiam
    intro z hz hwz hpz
    exact hnot z hz (heucl w z y hw hz hy hwz hwy) hpz
  · intro hvalid w y z hw hy hz hwy hwz
    let valuation : Valuation W := fun _ u => u = y
    have h := hvalid (Form.atom "p") valuation w hw
    simp only [FIVE_SCHEMA, Form.holds, Form.diam] at h
    have hdiam : ¬∀ u, u ∈ worlds → rel w u → u ≠ y := by
      intro hall
      exact hall y hy hwy rfl
    have hzdiam := h hdiam z hz hwz
    by_contra hnot
    apply hzdiam
    intro u _ hzu hu
    subst u
    exact hnot hzu

/-! ## Löb correspondence -/

/-- Löb's axiom characterizes transitive frames whose converse relation is
well-founded, assuming that every relational edge stays inside the frame. -/
-- HOL: `MODAL_TRANSNT` (`ad_hoc_correspondence.ml`).
theorem MODAL_TRANSNT {W : Type*} (worlds : Set W) (rel : W → W → Prop)
    (hclosed : ∀ x y, rel x y → x ∈ worlds ∧ y ∈ worlds) :
    (TRANSITIVE worlds rel ∧ WellFounded (fun x y => rel y x)) ↔
      ∀ p, Form.holdsIn ⟨worlds, rel⟩ (LOB_SCHEMA p) := by
  constructor
  · rintro ⟨htrans, hwf⟩ p valuation w hw hante
    simp only [Form.holds] at hante ⊢
    intro y hy hwy
    induction y using hwf.induction with
    | h y ih =>
        apply hante y hy hwy
        intro z hz hyz
        exact ih z hyz hz (htrans w y z hw hy hz hwy hyz)
  · intro hvalid
    constructor
    · intro w y z hw hy hz hwy hyz
      let valuation : Valuation W := fun _ u =>
        u ∈ worlds ∧ rel w u ∧ ∀ v, v ∈ worlds → rel u v → rel w v
      have hlob := hvalid (Form.atom "p") valuation w hw
      simp only [LOB_SCHEMA, Form.holds] at hlob
      have hante : ∀ u, u ∈ worlds → rel w u →
          (∀ v, v ∈ worlds → rel u v → valuation "p" v) → valuation "p" u := by
        intro u hu hwu hbox
        exact ⟨hu, hwu, fun v hv huv => (hbox v hv huv).2.1⟩
      have hbox := hlob hante
      exact (hbox y hy hwy).2.2 z hz hyz
    · classical
      by_contra hnwf
      have hchain : Nonempty {f : ℕ → W //
          ∀ n, (fun x y => rel y x) (f (n + 1)) (f n)} := by
        rw [wellFounded_iff_isEmpty_descending_chain] at hnwf
        exact not_isEmpty_iff.mp hnwf
      obtain ⟨⟨f, hstep⟩⟩ := hchain
      have hrel : ∀ n, rel (f n) (f (n + 1)) := hstep
      have hfworld : ∀ n, f n ∈ worlds := by
        intro n
        exact (hclosed (f n) (f (n + 1)) (hrel n)).1
      let valuation : Valuation W := fun _ u => u ∉ Set.range f
      have hlob := hvalid (Form.atom "p") valuation (f 0) (hfworld 0)
      simp only [LOB_SCHEMA, Form.holds] at hlob
      have hante : ∀ y, y ∈ worlds → rel (f 0) y →
          (∀ z, z ∈ worlds → rel y z → valuation "p" z) → valuation "p" y := by
        intro y _ _ hbox
        change y ∉ Set.range f
        by_contra hy
        obtain ⟨n, rfl⟩ := hy
        exact (hbox (f (n + 1)) (hfworld (n + 1)) (hrel n))
          ⟨n + 1, rfl⟩
      have hbox := hlob hante
      have hp1 := hbox (f 1) (hfworld 1) (by simpa using hrel 0)
      exact hp1 ⟨1, rfl⟩

/-! ## Grzegorczyk correspondence -/

/-- Grzegorczyk's axiom characterizes reflexive, transitive, weakly
well-founded frames, assuming that every relational edge stays inside the
frame. -/
-- HOL: `MODAL_RTWN` (`ad_hoc_correspondence.ml`).
theorem MODAL_RTWN {W : Type*} (worlds : Set W) (rel : W → W → Prop)
    (hclosed : ∀ x y, rel x y → x ∈ worlds ∧ y ∈ worlds) :
    (REFLEXIVE worlds rel ∧ TRANSITIVE worlds rel ∧
        WWF (fun x y => rel y x)) ↔
      ∀ p, Form.holdsIn ⟨worlds, rel⟩ (GRZ_SCHEMA p) := by
  constructor
  · rintro ⟨hrefl, htrans, hwf⟩ p valuation w hw hante
    simp only [Form.holds] at hante ⊢
    let strictSucc : W → W → Prop := fun y x => y ≠ x ∧ rel x y
    have hwf' : WellFounded strictSucc :=
      (wwf_iff_wellFounded_strict (fun x y => rel y x)).mp hwf
    induction w using hwf'.induction with
    | h w ih =>
        have hatw := hante w hw (hrefl w hw)
        apply hatw
        intro y hy hwy hpy z hz hyz
        by_cases hzw : z = w
        · subst z
          have hyw : rel y w := hyz
          by_cases hywEq : y = w
          · simpa [hywEq] using hpy
          · exact False.elim
              (hwf'.asymm.asymm y w ⟨hywEq, hwy⟩ ⟨Ne.symm hywEq, hyw⟩)
        · apply ih z
          · exact ⟨hzw, htrans w y z hw hy hz hwy hyz⟩
          · exact hz
          · intro u hu hzu
            exact hante u hu (htrans w z u hw hz hu
              (htrans w y z hw hy hz hwy hyz) hzu)
  · intro hvalid
    have hrefl : REFLEXIVE worlds rel := by
      intro w hw
      let valuation : Valuation W := fun _ u => rel w u
      have hgrz := hvalid (Form.atom "p") valuation w hw
      simp only [GRZ_SCHEMA, Form.holds] at hgrz
      apply hgrz
      intro y _ hwy _
      exact hwy
    have htrans : TRANSITIVE worlds rel := by
      intro x y z hx hy hz hxy hyz
      by_contra hxz
      let valuation : Valuation W := fun _ u => u ≠ x ∧ rel x u
      have hgrz := hvalid (Form.atom "p") valuation x hx
      simp only [GRZ_SCHEMA, Form.holds] at hgrz
      have hante : ∀ u, u ∈ worlds → rel x u →
          (∀ v, v ∈ worlds → rel u v →
            valuation "p" v → ∀ t, t ∈ worlds → rel v t → valuation "p" t) →
          valuation "p" u := by
        intro u hu hxu hbox
        by_cases hux : u = x
        · subst u
          exfalso
          have hyx : valuation "p" y := ⟨by
            intro hyx
            subst y
            exact hxz hyz, hxy⟩
          have hboxy := hbox y hy hxy hyx
          exact hxz (hboxy z hz hyz).2
        · exact ⟨hux, hxu⟩
      exact (hgrz hante).1 rfl
    have hantisymm : ANTISYMMETRIC worlds rel := by
      intro x y hx hy hxy hyx
      by_contra hne
      let valuation : Valuation W := fun _ u => u ≠ x
      have hgrz := hvalid (Form.atom "p") valuation x hx
      simp only [GRZ_SCHEMA, Form.holds] at hgrz
      have hante : ∀ u, u ∈ worlds → rel x u →
          (∀ v, v ∈ worlds → rel u v →
            valuation "p" v → ∀ t, t ∈ worlds → rel v t → valuation "p" t) →
          valuation "p" u := by
        intro u hu hxu hbox
        by_cases hux : u = x
        · subst u
          exfalso
          have hpy : valuation "p" y := Ne.symm hne
          have hboxy := hbox y hy hxy hpy
          exact hboxy x hx hyx rfl
        · exact hux
      exact (hgrz hante) rfl
    refine ⟨hrefl, htrans, ?_⟩
    apply (wwf_iff_wellFounded_strict (fun x y => rel y x)).mpr
    classical
    by_contra hnwf
    have hchain : Nonempty {f : ℕ → W //
        ∀ n, (fun y x => y ≠ x ∧ rel x y) (f (n + 1)) (f n)} := by
      rw [wellFounded_iff_isEmpty_descending_chain] at hnwf
      exact not_isEmpty_iff.mp hnwf
    obtain ⟨⟨f, hstep⟩⟩ := hchain
    have hne : ∀ n, f (n + 1) ≠ f n := fun n => (hstep n).1
    have hrel : ∀ n, rel (f n) (f (n + 1)) := fun n => (hstep n).2
    have hfworld : ∀ n, f n ∈ worlds := by
      intro n
      exact (hclosed (f n) (f (n + 1)) (hrel n)).1
    have hreach : ∀ i j, i ≤ j → rel (f i) (f j) := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => exact hrefl (f i) (hfworld i)
      | succ j hij ih =>
          exact htrans (f i) (f j) (f (j + 1))
            (hfworld i) (hfworld j) (hfworld (j + 1)) ih (hrel j)
    have finj : Function.Injective f := by
      intro i j hij
      by_contra hijne
      rcases Nat.lt_or_gt_of_ne hijne with hlt | hgt
      · have hr := hreach (i + 1) j (Nat.succ_le_iff.mpr hlt)
        have hback : rel (f (i + 1)) (f i) := by
          simpa only [hij] using hr
        have heq := hantisymm (f i) (f (i + 1))
          (hfworld i) (hfworld (i + 1)) (hrel i) hback
        exact hne i heq.symm
      · have hr := hreach (j + 1) i (Nat.succ_le_iff.mpr hgt)
        have hback : rel (f (j + 1)) (f j) := by
          simpa only [hij] using hr
        have heq := hantisymm (f j) (f (j + 1))
          (hfworld j) (hfworld (j + 1)) (hrel j) hback
        exact hne j heq.symm
    let valuation : Valuation W := fun _ u =>
      ¬∃ n, u = f (2 * n)
    have hgrz := hvalid (Form.atom "p") valuation (f 0) (hfworld 0)
    simp only [GRZ_SCHEMA, Form.holds] at hgrz
    have hante : ∀ y, y ∈ worlds → rel (f 0) y →
        (∀ z, z ∈ worlds → rel y z →
          valuation "p" z → ∀ u, u ∈ worlds → rel z u → valuation "p" u) →
        valuation "p" y := by
      intro y _ _ hbox
      change ¬∃ n, y = f (2 * n)
      by_contra hyp
      obtain ⟨n, rfl⟩ := hyp
      have hpOdd : valuation "p" (f (2 * n + 1)) := by
        change ¬∃ m, f (2 * n + 1) = f (2 * m)
        intro heven
        obtain ⟨m, hm⟩ := heven
        have hindices : 2 * n + 1 = 2 * m := finj hm
        omega
      have hboxOdd := hbox (f (2 * n + 1)) (hfworld (2 * n + 1))
        (by simpa [Nat.add_assoc] using hrel (2 * n)) hpOdd
      have hpEven := hboxOdd (f (2 * (n + 1))) (hfworld (2 * (n + 1)))
        (by simpa [Nat.mul_add, Nat.add_assoc] using hrel (2 * n + 1))
      exact hpEven ⟨n + 1, rfl⟩
    have hp0 := hgrz hante
    exact hp0 ⟨0, by simp⟩

end HOLMS
