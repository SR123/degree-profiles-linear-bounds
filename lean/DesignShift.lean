import PolynomialDesign

namespace SelfContainedCycle055
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037 SelfContainedCycle038
open SelfContainedCycle053 SelfContainedCycle054
open MvPolynomial DegreeProfilesReview.NS

/-- The linear space of design equations, with normalization deliberately separate. -/
def IsDesign {F : Type*} [CommRing F] (n m d : ℕ) (ψ : Edges → F) : Prop :=
  (∀ P, ¬ IsMatching P → ψ P=0) ∧
  (∀ P, P ⊆ grid n m → P.card+1≤d → ∀ i ∈ Finset.Icc 1 n,
    (∑ j ∈ Finset.Icc 1 m, ψ (insert (i,j) P))=ψ P) ∧
  (∀ P, P ⊆ grid n m → P.card+1≤d → ∀ j ∈ Finset.Icc 1 m,
    (∑ i ∈ Finset.Icc 1 n, ψ (insert (i,j) P))=ψ P)

theorem normalized_iff {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F} :
    IsMatchingDesign n m d ψ ↔ ψ ∅=1 ∧ IsDesign n m d ψ := Iff.rfl

theorem design_zero {F : Type*} [CommRing F] (n m d : ℕ) :
    IsDesign n m d (0 : Edges → F) := by
  refine ⟨by simp,?_,?_⟩ <;> intros <;> simp

theorem design_add {F : Type*} [CommRing F] {n m d : ℕ} {ψ ν : Edges → F}
    (hψ : IsDesign n m d ψ) (hν : IsDesign n m d ν) : IsDesign n m d (ψ+ν) := by
  refine ⟨?_,?_,?_⟩
  · intro P hm; simp [hψ.1 P hm,hν.1 P hm]
  · intro P hP hd i hi
    simp only [Pi.add_apply,Finset.sum_add_distrib,hψ.2.1 P hP hd i hi,hν.2.1 P hP hd i hi]
  · intro P hP hd j hj
    simp only [Pi.add_apply,Finset.sum_add_distrib,hψ.2.2 P hP hd j hj,hν.2.2 P hP hd j hj]

theorem design_smul {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (c : F) (hψ : IsDesign n m d ψ) : IsDesign n m d (c • ψ) := by
  refine ⟨?_,?_,?_⟩
  · intro P hm; simp [hψ.1 P hm]
  · intro P hP hd i hi
    simp only [Pi.smul_apply,← Finset.smul_sum,hψ.2.1 P hP hd i hi]
  · intro P hP hd j hj
    simp only [Pi.smul_apply,← Finset.smul_sum,hψ.2.2 P hP hd j hj]

/-- An actual submodule, rather than assumed closure laws. -/
def designSpace (F : Type*) [CommRing F] (n m d : ℕ) : Submodule F (Edges → F) where
  carrier := {ψ | IsDesign n m d ψ}
  zero_mem' := design_zero n m d
  add_mem' := design_add
  smul_mem' := by intro c x hx; exact design_smul c hx

theorem design_mono {F : Type*} [CommRing F] {n m d e : ℕ} {ψ : Edges → F}
    (h : IsDesign n m d ψ) (he : e≤d) : IsDesign n m e ψ := by
  exact ⟨h.1,fun P hP hd i hi => h.2.1 P hP (hd.trans he) i hi,
    fun P hP hd j hj => h.2.2 P hP (hd.trans he) j hj⟩

/-- Insertion includes both the repeated-variable and occupied-line cases. -/
def shift {F : Type*} {n m : ℕ} (ψ : Edges → F) (v : Var n m) : Edges → F :=
  fun P => ψ (insert (SelfContainedCycle054.edgeEmbedding n m v) P)

theorem shift_repeated {F : Type*} {n m : ℕ} (ψ : Edges → F) (v : Var n m)
    (P : Edges) (hv : SelfContainedCycle054.edgeEmbedding n m v ∈ P) : shift ψ v P=ψ P := by
  simp [shift,Finset.insert_eq_of_mem hv]

theorem shift_idempotent {F : Type*} {n m : ℕ} (ψ : Edges → F) (v : Var n m) :
    shift (shift ψ v) v=shift ψ v := by ext P; simp [shift]

theorem shift_commute {F : Type*} {n m : ℕ} (ψ : Edges → F) (v w : Var n m) :
    shift (shift ψ v) w=shift (shift ψ w) v := by ext P; simp [shift,Finset.insert_comm]

theorem shift_design {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsDesign n m (d+1) ψ) (v : Var n m) : IsDesign n m d (shift ψ v) := by
  refine ⟨?_,?_,?_⟩
  · intro P hm; exact h.1 _ (nonmatching_insert hm _)
  · intro P hP hd i hi
    have hPg : insert (SelfContainedCycle054.edgeEmbedding n m v) P ⊆ grid n m :=
      insert_grid hP v.1.property v.2.property
    have hcard : (insert (SelfContainedCycle054.edgeEmbedding n m v) P).card+1≤d+1 := by
      have := Finset.card_insert_le (SelfContainedCycle054.edgeEmbedding n m v) P; omega
    simpa only [shift,Finset.insert_comm] using h.2.1 _ hPg hcard i hi
  · intro P hP hd j hj
    have hPg : insert (SelfContainedCycle054.edgeEmbedding n m v) P ⊆ grid n m :=
      insert_grid hP v.1.property v.2.property
    have hcard : (insert (SelfContainedCycle054.edgeEmbedding n m v) P).card+1≤d+1 := by
      have := Finset.card_insert_le (SelfContainedCycle054.edgeEmbedding n m v) P; omega
    simpa only [shift,Finset.insert_comm] using h.2.2 _ hPg hcard j hj

/-- The shift is a linear map between the actual design submodules. -/
def shiftLinear (F : Type*) [CommRing F] (n m d : ℕ) (v : Var n m) :
    designSpace F n m (d+1) →ₗ[F] designSpace F n m d where
  toFun ψ := ⟨shift ψ.val v,shift_design (show IsDesign n m (d+1) ψ.val from ψ.property) v⟩
  map_add' := by intro ψ ν; rfl
  map_smul' := by intro c ψ; rfl

/-- Multiplication compatibility in the original ring, for every polynomial and every function. -/
theorem functional_X_mul {F : Type*} [CommRing F] {n m : ℕ} (ψ : Edges → F)
    (v : Var n m) (f : MvPolynomial (Var n m) F) :
    designFunctional ψ (X v*f)=designFunctional (shift ψ v) f := by
  classical
  conv_lhs => rw [as_sum f,Finset.mul_sum,map_sum]
  conv_rhs => rw [as_sum f,map_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [X,monomial_mul,one_mul,functional_monomial,functional_monomial]
  rw [add_comm,edgeSupport_add_single μ v 1 (by decide)]
  rfl

/-- Agreement only in the degree range is enough; collision values are explicitly zero. -/
theorem functional_agreement {F : Type*} [CommRing F] {n m e : ℕ} {ψ ν : Edges → F}
    (hψ : ∀ P, ¬ IsMatching P → ψ P=0) (hν : ∀ P, ¬ IsMatching P → ν P=0)
    (hagree : ∀ P, IsMatching P → P ⊆ grid n m → P.card≤e → ψ P=ν P)
    (f : MvPolynomial (Var n m) F) (hf : f.totalDegree≤e) :
    designFunctional ψ f=designFunctional ν f := by
  classical
  conv_lhs => rw [as_sum f,map_sum]
  conv_rhs => rw [as_sum f,map_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [functional_monomial,functional_monomial]
  by_cases hm : IsMatching (edgeSupport μ)
  · have hdeg : mdeg μ≤f.totalDegree := le_totalDegree hμ
    rw [hagree _ hm (edgeSupport_grid μ) ((edgeSupport_card μ).trans (hdeg.trans hf))]
  · rw [hψ _ hm,hν _ hm]

/-- The scalar normalization is not used to annihilate axiom multiples. -/
theorem design_row_multiple {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsDesign n m d ψ) (μ : Var n m →₀ ℕ) (hd : mdeg μ+1≤d) (i : Label n) :
    designFunctional ψ (monomial μ (1:F)*rowAxiom i)=0 := by
  rw [rowAxiom,mul_sub,mul_one,Finset.mul_sum,map_sub,map_sum]
  have he : ∀ j : Label m, designFunctional ψ (monomial μ (1:F)*X (i,j))=
      ψ (insert (i.val,j.val) (edgeSupport μ)) := by
    intro j; simpa only [pow_one,SelfContainedCycle054.edgeEmbedding] using functional_monomial_mul_X_pow ψ μ (i,j) 1 (by decide)
  simp only [he,functional_monomial,one_mul]
  rw [sum_labels m (fun j => ψ (insert (i.val,j) (edgeSupport μ)))]
  exact sub_eq_zero.mpr (h.2.1 _ (edgeSupport_grid μ) (by have := edgeSupport_card μ; omega) i.val i.property)

theorem design_col_multiple {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsDesign n m d ψ) (μ : Var n m →₀ ℕ) (hd : mdeg μ+1≤d) (j : Label m) :
    designFunctional ψ (monomial μ (1:F)*colAxiom j)=0 := by
  rw [colAxiom,mul_sub,mul_one,Finset.mul_sum,map_sub,map_sum]
  have he : ∀ i : Label n, designFunctional ψ (monomial μ (1:F)*X (i,j))=
      ψ (insert (i.val,j.val) (edgeSupport μ)) := by
    intro i; simpa only [pow_one,SelfContainedCycle054.edgeEmbedding] using functional_monomial_mul_X_pow ψ μ (i,j) 1 (by decide)
  simp only [he,functional_monomial,one_mul]
  rw [sum_labels n (fun i => ψ (insert (i,j.val) (edgeSupport μ)))]
  exact sub_eq_zero.mpr (h.2.2 _ (edgeSupport_grid μ) (by have := edgeSupport_card μ; omega) j.val j.property)

theorem design_collision_multiple {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsDesign n m d ψ) (μ : Var n m →₀ ℕ) (v w : Var n m)
    (hne : v≠w) (hc : v.1=w.1 ∨ v.2=w.2) :
    designFunctional ψ (monomial μ (1:F)*(X v*X w))=0 := by
  rw [← mul_assoc]
  simp only [X,monomial_mul,one_mul,functional_monomial,
    edgeSupport_add_single _ _ 1 (by decide)]
  exact h.1 _ (conflicting_support _ v w hne hc)

theorem design_axiom_multiple {F : Type*} [Field F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsDesign n m d ψ) (hn : 1≤n) (hm : 1≤m)
    (μ : Var n m →₀ ℕ) (f : MvPolynomial (Var n m) F)
    (hf : IsBAxiom n m f) (hd : mdeg μ+f.totalDegree≤d) :
    designFunctional ψ (monomial μ (1:F)*f)=0 := by
  cases hf with
  | row i =>
    have hpos := row_degree_positive (F:=F) hm i
    exact design_row_multiple h μ (by omega) i
  | col j =>
    have hpos := col_degree_positive (F:=F) hn j
    exact design_col_multiple h μ (by omega) j
  | boolean v => exact functional_boolean_multiple ψ μ v
  | rowCollision i j k hjk =>
    exact design_collision_multiple h μ (i,j) (i,k) (fun he => hjk (congrArg Prod.snd he)) (Or.inl rfl)
  | colCollision i k j hik =>
    exact design_collision_multiple h μ (i,j) (k,j) (fun he => hik (congrArg Prod.fst he)) (Or.inr rfl)

theorem design_axiom {F : Type*} [Field F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsDesign n m d ψ) (hn : 1≤n) (hm : 1≤m)
    (f : MvPolynomial (Var n m) F) (hf : IsBAxiom n m f) (hd : f.totalDegree≤d) :
    designFunctional ψ f=0 := by
  have hh := design_axiom_multiple h hn hm 0 f hf (by simpa [mdeg] using hd)
  have he : (monomial (0 : Var n m →₀ ℕ) (1:F))=1 := rfl
  simpa only [he,one_mul] using hh

open DegreeProfilesReview.PC

/-- Conditional assembly for actual PC lists. The extension premise remains a separate obligation. -/
theorem pc_proof_invariant {F : Type*} [Field F] {n m D : ℕ}
    (hn : 1≤n) (hm : 1≤m)
    (hext : ∀ ψ : Edges → F, IsDesign n m (D-1) ψ →
      ∃ ν : Edges → F, IsDesign n m D ν ∧
        ∀ P, IsMatching P → P ⊆ grid n m → P.card≤D-1 → ν P=ψ P)
    {l : List (MvPolynomial (Var n m) F)}
    (hp : IsProof {f : MvPolynomial (Var n m) F | IsBAxiom n m f} l) :
    DegBounded D l → ∀ f ∈ l, ∀ ψ : Edges → F, IsDesign n m D ψ → designFunctional ψ f=0 := by
  induction hp with
  | nil => intro _ f hf; simp at hf
  | @ax l f hp hf ih =>
    intro hb g hg ψ hψ
    have hbl : DegBounded D l := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    rcases List.mem_cons.mp hg with rfl | hg
    · exact design_axiom hψ hn hm g hf (hb g (List.mem_cons_self))
    · exact ih hbl g hg ψ hψ
  | @lin l f hp hf ih =>
    intro hb g hg ψ hψ
    have hbl : DegBounded D l := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    rcases List.mem_cons.mp hg with rfl | hg
    · have hker : Submodule.span F {t : MvPolynomial (Var n m) F | t ∈ l} ≤
          LinearMap.ker (designFunctional ψ) := by
        apply Submodule.span_le.mpr
        intro t ht
        exact ih hbl t ht ψ hψ
      exact hker hf
    · exact ih hbl g hg ψ hψ
  | @mulX l g v hp hg ih =>
    intro hb f hf ψ hψ
    have hbl : DegBounded D l := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    rcases List.mem_cons.mp hf with rfl | hf
    · by_cases hz : g=0
      · simp [hz]
      · have hdeg := totalDegree_succ_le_X_mul v hz
        have hmul := hb (X v*g) List.mem_cons_self
        have hD : 1≤D := by omega
        have hdg : g.totalDegree≤D-1 := by omega
        have hshift : IsDesign n m (D-1) (shift ψ v) :=
          shift_design (by simpa only [Nat.sub_add_cancel hD] using hψ) v
        obtain ⟨ν,hν,hagree⟩ := hext (shift ψ v) hshift
        rw [functional_X_mul,
          functional_agreement hshift.1 hν.1 (fun P hm hP hd => (hagree P hm hP hd).symm) g hdg]
        exact ih hbl g hg ν hν
    · exact ih hbl f hf ψ hψ

/-- This is explicitly conditional on actual design extension, not a completed PC lower bound. -/
theorem no_PCRefutes_of_extension {F : Type*} [Field F] {n m D : ℕ}
    (hn : 1≤n) (hm : 1≤m)
    (hext : ∀ ψ : Edges → F, IsDesign n m (D-1) ψ →
      ∃ ν : Edges → F, IsDesign n m D ν ∧
        ∀ P, IsMatching P → P ⊆ grid n m → P.card≤D-1 → ν P=ψ P)
    {η : Edges → F} (hη : IsMatchingDesign n m D η) :
    ¬ Refutes {f : MvPolynomial (Var n m) F | IsBAxiom n m f} D := by
  rintro ⟨l,hp,hb,hmem⟩
  have hz := pc_proof_invariant hn hm hext hp hb 1 hmem η hη.2
  rw [functional_one hη] at hz
  exact one_ne_zero hz

/-- At degree zero the extension premise is actually discharged by the identity. -/
theorem no_PCRefutes_degree_zero {F : Type*} [Field F] {n m : ℕ}
    (hn : 1≤n) (hm : 1≤m) {η : Edges → F} (hη : IsMatchingDesign n m 0 η) :
    ¬ Refutes {f : MvPolynomial (Var n m) F | IsBAxiom n m f} 0 := by
  apply no_PCRefutes_of_extension hn hm ?_ hη
  intro ψ hψ
  exact ⟨ψ,hψ,by intros; rfl⟩

/-- The degree-zero to degree-one extension is constructed, not postulated. -/
theorem design_extension_one {F : Type*} [CommRing F] {n m : ℕ}
    {η : Edges → F} (hη : IsMatchingDesign n m 1 η) :
    ∀ ψ : Edges → F, IsDesign n m 0 ψ →
      ∃ ν : Edges → F, IsDesign n m 1 ν ∧
        ∀ P, IsMatching P → P ⊆ grid n m → P.card≤0 → ν P=ψ P := by
  intro ψ _
  refine ⟨ψ ∅ • η,design_smul _ hη.2,?_⟩
  intro P _ _ hP
  have he : P=∅ := Finset.card_eq_zero.mp (by omega)
  subst P
  simp [hη.1]

/-- A positive-degree instance of the PC assembly with the extension discharged. -/
theorem no_PCRefutes_degree_one {F : Type*} [Field F] {n m : ℕ}
    (hn : 1≤n) (hm : 1≤m) {η : Edges → F} (hη : IsMatchingDesign n m 1 η) :
    ¬ Refutes {f : MvPolynomial (Var n m) F | IsBAxiom n m f} 1 :=
  no_PCRefutes_of_extension hn hm (design_extension_one hη) hη

/-- The zero-degree boundary of the concrete PC family needs no unproved extension. -/
theorem concrete_PC_zero_degree {F : Type*} [Field F] [CharP F 2] (a : ℕ) :
    ¬ Refutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} 0 := by
  have hq : 0<2^a := pow_pos (by decide) _
  exact no_PCRefutes_degree_zero (by omega) (by omega) (concrete_family_design a 0 hq)

/-- A genuine degree-one PC exclusion for every concrete family member with q>1. -/
theorem concrete_PC_one_degree {F : Type*} [Field F] [CharP F 2] (a : ℕ) (ha : 1<2^a) :
    ¬ Refutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} 1 := by
  exact no_PCRefutes_degree_one (by omega) (by omega) (concrete_family_design a 1 ha)

/-- Actual unnormalized rectangular designs in the characteristic range. -/
theorem actual_design {F : Type*} [CommRing F] {p a n m d : ℕ}
    (hp : p.Prime) [CharP F p] (hn : 2*d≤n) (hd : d<p^a) (hnm : n≤m)
    (hdiv : p^a∣m-n) : IsDesign n m d (fun P => (rectCoefficient n m P : F)) :=
  (actual_rectangular_design hp hn hd hnm hdiv).2

def v22 : Var 4 8 := (⟨2,by decide⟩,⟨2,by decide⟩)
def v23 : Var 4 8 := (⟨2,by decide⟩,⟨3,by decide⟩)
noncomputable def rectangle : Edges → ZMod 2 := fun P => (rectCoefficient 4 8 P : ZMod 2)

/-- A genuine nonzero normalized design shifts to empty value zero. -/
theorem shifted_design_not_normalized :
    IsMatchingDesign 4 8 2 rectangle ∧
    IsDesign 4 8 1 (shift rectangle v22) ∧
    shift rectangle v22 ∅=0 ∧
    ¬ IsMatchingDesign 4 8 1 (shift rectangle v22) := by
  have hrect : IsMatchingDesign 4 8 2 rectangle := four_by_eight_design
  have hs : IsDesign 4 8 1 (shift rectangle v22) := shift_design hrect.2 v22
  have hz : shift rectangle v22 ∅=0 := by
    simp [shift,rectangle,v22,SelfContainedCycle054.edgeEmbedding,four_by_eight_terminal_value]
  refine ⟨hrect,hs,hz,?_⟩
  intro hnorm
  have hh := hnorm.1
  rw [hz] at hh
  exact zero_ne_one hh

/-- Repeated insertion and a genuine same-row collision use the original polynomial variables. -/
theorem actual_shift_cases :
    shift rectangle v22 {(2,2)}=rectangle {(2,2)} ∧
    shift rectangle v22 {(2,3)}=0 ∧
    designFunctional rectangle (X v22 * X v22)=designFunctional (shift rectangle v22) (X v22) ∧
    designFunctional rectangle (X v22 * X v23)=0 := by
  refine ⟨shift_repeated _ _ _ (by decide),?_,functional_X_mul _ _ _,?_⟩
  · exact four_by_eight_design.2.1 _ (by decide)
  · have hc : (v23 : Var 4 8).1=v22.1 := rfl
    have hn : (v23 : Var 4 8)≠v22 := by decide
    have hh := design_collision_multiple four_by_eight_design.2 (0 : Var 4 8 →₀ ℕ) v22 v23
      (Ne.symm hn) (Or.inl hc.symm)
    have he : (monomial (0 : Var 4 8 →₀ ℕ) (1:ZMod 2))=1 := rfl
    simpa only [he,one_mul] using hh

end SelfContainedCycle055

