import RectangularDesign
import DegreeProfilesReview.Nullstellensatz
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace SelfContainedCycle054
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037 SelfContainedCycle053
open SelfContainedCycle038
open MvPolynomial
open DegreeProfilesReview.NS

abbrev Label (n : ℕ) := ↥(Finset.Icc 1 n)
abbrev Var (n m : ℕ) := Label n × Label m

def edgeEmbedding (n m : ℕ) : Var n m ↪ ℕ × ℕ where
  toFun e := (e.1.val,e.2.val)
  inj' := by intro x y h; exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

def edgeSupport {n m : ℕ} (μ : Var n m →₀ ℕ) : Edges := μ.support.map (edgeEmbedding n m)

theorem edgeSupport_grid {n m : ℕ} (μ : Var n m →₀ ℕ) : edgeSupport μ ⊆ grid n m := by
  intro e he
  obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp he
  exact Finset.mem_product.mpr ⟨v.1.property,v.2.property⟩

theorem edgeSupport_card {n m : ℕ} (μ : Var n m →₀ ℕ) : (edgeSupport μ).card ≤ mdeg μ := by
  rw [edgeSupport,Finset.card_map]
  unfold mdeg Finsupp.sum
  calc
    μ.support.card = ∑ _v ∈ μ.support, 1 := by simp
    _ ≤ ∑ v ∈ μ.support, μ v := Finset.sum_le_sum (fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))

@[simp] theorem edgeSupport_zero (n m : ℕ) : edgeSupport (0 : Var n m →₀ ℕ)=∅ := by simp [edgeSupport]

theorem edgeSupport_add_single {n m : ℕ} (μ : Var n m →₀ ℕ) (v : Var n m) (k : ℕ) (hk : k≠0) :
    edgeSupport (μ+Finsupp.single v k)=insert (edgeEmbedding n m v) (edgeSupport μ) := by
  classical
  have hs : (μ+Finsupp.single v k).support=insert v μ.support := by
    ext x
    by_cases hx : x=v
    · subst x; simp only [Finsupp.mem_support_iff,Finsupp.add_apply,Finsupp.single_eq_same,Finset.mem_insert_self,iff_true]; omega
    · simp [Finsupp.mem_support_iff,hx]
  simp [edgeSupport,hs,Finset.map_insert]

noncomputable def designFunctional {F : Type*} [CommRing F] {n m : ℕ} (ψ : Edges → F) :
    MvPolynomial (Var n m) F →ₗ[F] F :=
  Finsupp.linearCombination F (fun μ => ψ (edgeSupport μ))

theorem functional_monomial {F : Type*} [CommRing F] {n m : ℕ} (ψ : Edges → F)
    (μ : Var n m →₀ ℕ) (c : F) : designFunctional ψ (monomial μ c)=c*ψ (edgeSupport μ) := by
  exact Finsupp.linearCombination_single F _ _

theorem functional_one {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) : designFunctional (n:=n) (m:=m) ψ 1=1 := by
  change designFunctional ψ (monomial 0 (1:F))=1
  rw [functional_monomial,edgeSupport_zero,h.1,one_mul]

theorem functional_monomial_mul_X_pow {F : Type*} [CommRing F] {n m : ℕ} (ψ : Edges → F)
    (μ : Var n m →₀ ℕ) (v : Var n m) (k : ℕ) (hk : k≠0) :
    designFunctional ψ (monomial μ (1:F) * X v ^ k)=ψ (insert (edgeEmbedding n m v) (edgeSupport μ)) := by
  rw [X_pow_eq_monomial,monomial_mul,one_mul,functional_monomial,one_mul,edgeSupport_add_single μ v k hk]

noncomputable def rowAxiom {F : Type*} [CommRing F] {n m : ℕ} (i : Label n) : MvPolynomial (Var n m) F :=
  (∑ j : Label m, X (i,j)) - 1
noncomputable def colAxiom {F : Type*} [CommRing F] {n m : ℕ} (j : Label m) : MvPolynomial (Var n m) F :=
  (∑ i : Label n, X (i,j)) - 1
noncomputable def boolAxiom {F : Type*} [CommRing F] {n m : ℕ} (v : Var n m) : MvPolynomial (Var n m) F := X v^2-X v

/-- Original axioms in the ordinary polynomial ring, before Boolean reduction. -/
inductive IsBAxiom {F : Type*} [CommRing F] (n m : ℕ) : MvPolynomial (Var n m) F → Prop
  | row (i : Label n) : IsBAxiom n m (rowAxiom i)
  | col (j : Label m) : IsBAxiom n m (colAxiom j)
  | boolean (v : Var n m) : IsBAxiom n m (boolAxiom v)
  | rowCollision (i : Label n) (j k : Label m) (h : j≠k) : IsBAxiom n m (X (i,j)*X (i,k))
  | colCollision (i k : Label n) (j : Label m) (h : i≠k) : IsBAxiom n m (X (i,j)*X (k,j))

theorem functional_boolean_multiple {F : Type*} [CommRing F] {n m : ℕ} (ψ : Edges → F)
    (μ : Var n m →₀ ℕ) (v : Var n m) :
    designFunctional ψ (monomial μ (1:F)*boolAxiom v)=0 := by
  rw [boolAxiom,mul_sub,map_sub,functional_monomial_mul_X_pow ψ μ v 2 (by decide)]
  have h := functional_monomial_mul_X_pow ψ μ v 1 (by decide)
  simp only [pow_one] at h
  rw [h,sub_self]

theorem sum_labels {F : Type*} [AddCommMonoid F] (m : ℕ) (f : ℕ → F) :
    (∑ j : Label m, f j.val)=∑ j ∈ Finset.Icc 1 m, f j := by
  exact Finset.sum_coe_sort (Finset.Icc 1 m) f

theorem functional_row_multiple {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) (μ : Var n m →₀ ℕ) (hd : mdeg μ+1≤d) (i : Label n) :
    designFunctional ψ (monomial μ (1:F)*rowAxiom i)=0 := by
  rw [rowAxiom,mul_sub,mul_one,Finset.mul_sum,map_sub,map_sum]
  have he : ∀ j : Label m, designFunctional ψ (monomial μ (1:F)*X (i,j))=
      ψ (insert (i.val,j.val) (edgeSupport μ)) := by
    intro j; simpa only [pow_one,edgeEmbedding] using functional_monomial_mul_X_pow ψ μ (i,j) 1 (by decide)
  simp only [he,functional_monomial,one_mul]
  rw [sum_labels m (fun j => ψ (insert (i.val,j) (edgeSupport μ)))]
  exact sub_eq_zero.mpr (h.2.2.1 _ (edgeSupport_grid μ) (by have := edgeSupport_card μ; omega) i.val i.property)

theorem functional_col_multiple {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) (μ : Var n m →₀ ℕ) (hd : mdeg μ+1≤d) (j : Label m) :
    designFunctional ψ (monomial μ (1:F)*colAxiom j)=0 := by
  rw [colAxiom,mul_sub,mul_one,Finset.mul_sum,map_sub,map_sum]
  have he : ∀ i : Label n, designFunctional ψ (monomial μ (1:F)*X (i,j))=
      ψ (insert (i.val,j.val) (edgeSupport μ)) := by
    intro i; simpa only [pow_one,edgeEmbedding] using functional_monomial_mul_X_pow ψ μ (i,j) 1 (by decide)
  simp only [he,functional_monomial,one_mul]
  rw [sum_labels n (fun i => ψ (insert (i,j.val) (edgeSupport μ)))]
  exact sub_eq_zero.mpr (h.2.2.2 _ (edgeSupport_grid μ) (by have := edgeSupport_card μ; omega) j.val j.property)

/-- Two conflicting original variables cannot belong to a matching support. -/
theorem conflicting_support {n m : ℕ} (P : Edges) (v w : Var n m) (hne : v≠w)
    (hc : v.1=w.1 ∨ v.2=w.2) :
    ¬ IsMatching (insert (edgeEmbedding n m w) (insert (edgeEmbedding n m v) P)) := by
  intro h
  have heq := h (edgeEmbedding n m v) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    (edgeEmbedding n m w) (Finset.mem_insert_self _ _) (by
      rcases hc with hr | hc
      · exact Or.inl (congrArg Subtype.val hr)
      · exact Or.inr (congrArg Subtype.val hc))
  exact hne ((edgeEmbedding n m).injective heq)

theorem functional_collision_multiple {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) (μ : Var n m →₀ ℕ) (v w : Var n m)
    (hne : v≠w) (hc : v.1=w.1 ∨ v.2=w.2) :
    designFunctional ψ (monomial μ (1:F)*(X v*X w))=0 := by
  rw [← mul_assoc]
  simp only [X,monomial_mul,one_mul,functional_monomial,
    edgeSupport_add_single _ _ 1 (by decide)]
  exact h.2.1 _ (conflicting_support _ v w hne hc)

theorem row_coefficient {F : Type*} [CommRing F] {n m : ℕ} (i : Label n) (j : Label m) :
    coeff (Finsupp.single (i,j) 1) (rowAxiom (F:=F) i)=1 := by
  classical
  have h0 : (0 : Var n m →₀ ℕ) ≠ Finsupp.single (i,j) 1 := by
    intro he; have hh := congrArg (fun μ : Var n m →₀ ℕ => μ (i,j)) he; simp at hh
  simp [rowAxiom,coeff_sum,coeff_single_X,coeff_one,h0]

theorem col_coefficient {F : Type*} [CommRing F] {n m : ℕ} (i : Label n) (j : Label m) :
    coeff (Finsupp.single (i,j) 1) (colAxiom (F:=F) j)=1 := by
  classical
  have h0 : (0 : Var n m →₀ ℕ) ≠ Finsupp.single (i,j) 1 := by
    intro he; have hh := congrArg (fun μ : Var n m →₀ ℕ => μ (i,j)) he; simp at hh
  simp [colAxiom,coeff_sum,coeff_single_X,coeff_one,h0]

/-- Positive dimensions keep a totality axiom from becoming the constant -1. -/
theorem row_degree_positive {F : Type*} [CommRing F] [Nontrivial F] {n m : ℕ}
    (hm : 1≤m) (i : Label n) : 1≤(rowAxiom (F:=F) (m:=m) i).totalDegree := by
  let j : Label m := ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,hm⟩⟩
  have hmem : Finsupp.single (i,j) 1 ∈ (rowAxiom (F:=F) i).support := by
    rw [mem_support_iff,row_coefficient]; exact one_ne_zero
  simpa using (le_totalDegree hmem)

theorem col_degree_positive {F : Type*} [CommRing F] [Nontrivial F] {n m : ℕ}
    (hn : 1≤n) (j : Label m) : 1≤(colAxiom (F:=F) (n:=n) j).totalDegree := by
  let i : Label n := ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,hn⟩⟩
  have hmem : Finsupp.single (i,j) 1 ∈ (colAxiom (F:=F) j).support := by
    rw [mem_support_iff,col_coefficient]; exact one_ne_zero
  simpa using (le_totalDegree hmem)

theorem functional_axiom_multiple {F : Type*} [Field F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) (hn : 1≤n) (hm : 1≤m)
    (μ : Var n m →₀ ℕ) (f : MvPolynomial (Var n m) F)
    (hf : IsBAxiom n m f) (hd : mdeg μ+f.totalDegree≤d) :
    designFunctional ψ (monomial μ (1:F)*f)=0 := by
  cases hf with
  | row i =>
    have hpos := row_degree_positive (F:=F) hm i
    exact functional_row_multiple h μ (by omega) i
  | col j =>
    have hpos := col_degree_positive (F:=F) hn j
    exact functional_col_multiple h μ (by omega) j
  | boolean v => exact functional_boolean_multiple ψ μ v
  | rowCollision i j k hjk =>
    exact functional_collision_multiple h μ (i,j) (i,k) (fun he => hjk (congrArg Prod.snd he)) (Or.inl rfl)
  | colCollision i k j hik =>
    exact functional_collision_multiple h μ (i,j) (k,j) (fun he => hik (congrArg Prod.fst he)) (Or.inr rfl)

/-- Soundness for the frozen total-product-degree NS certificate definition. -/
theorem no_NSRefutes_of_design {F : Type*} [Field F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) (hn : 1≤n) (hm : 1≤m) :
    ¬ NSRefutes {f : MvPolynomial (Var n m) F | IsBAxiom n m f} d := by
  intro href
  have hspan := nsRefutes_iff_one_mem_NSspan.mp href
  have hker : NSspan {f : MvPolynomial (Var n m) F | IsBAxiom n m f} d ≤
      LinearMap.ker (designFunctional (n:=n) (m:=m) ψ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨μ,f,hf,hd,rfl⟩
    exact functional_axiom_multiple h hn hm μ f hf hd
  have hz := hker hspan
  change designFunctional ψ 1=0 at hz
  rw [functional_one h] at hz
  exact one_ne_zero hz

/-- Actual original-polynomial NS exclusion; the design premise is fully discharged. -/
theorem rectangular_no_NSRefutes {F : Type*} [Field F] {p a n m d : ℕ}
    (hp : p.Prime) [CharP F p] (hn : 1≤n) (hsize : 2*d≤n) (hd : d<p^a)
    (hnm : n≤m) (hdiv : p^a∣m-n) :
    ¬ NSRefutes {f : MvPolynomial (Var n m) F | IsBAxiom n m f} d :=
  no_NSRefutes_of_design (actual_rectangular_design hp hsize hd hnm hdiv) hn (hn.trans hnm)

/-- A genuine linear NS lower bound in universe size n=3q, q=2^a. -/
theorem concrete_family_NS_lower_bound {F : Type*} [Field F] [CharP F 2] (a d : ℕ)
    (hd : d<2^a) :
    ¬ NSRefutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} d := by
  have hq : 0<2^a := pow_pos (by decide) _
  exact no_NSRefutes_of_design (concrete_family_design a d hd) (by omega) (by omega)

/-- Every actual certificate has degree at least q; the parameter is row-universe size 3q. -/
theorem concrete_family_certificate_degree {F : Type*} [Field F] [CharP F 2] (a d : ℕ)
    (h : NSRefutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} d) :
    2^a≤d := Nat.le_of_not_gt (fun hd => concrete_family_NS_lower_bound a d hd h)

/-- The original functional preserves repeated-variable exponents in the ring, not in its values. -/
theorem repeated_variable_budget_example {F : Type*} [CommRing F] [Nontrivial F] {n m : ℕ}
    (ψ : Edges → F) (v : Var n m) :
    (X v ^ 2 : MvPolynomial (Var n m) F).totalDegree=2 ∧
    (edgeSupport (Finsupp.single v 2)).card=1 ∧
    designFunctional ψ (X v^2)=designFunctional ψ (X v) := by
  refine ⟨totalDegree_X_pow v 2,?_,?_⟩
  · simp [edgeSupport,Finsupp.support_single_ne_zero _ (by decide : (2:ℕ)≠0)]
  · have h2 := functional_monomial_mul_X_pow ψ 0 v 2 (by decide)
    have h1 := functional_monomial_mul_X_pow ψ 0 v 1 (by decide)
    have he : (monomial (0 : Var n m →₀ ℕ) (1:F))=1 := rfl
    simp only [he,one_mul,pow_one] at h2 h1
    exact h2.trans h1.symm

/-- Real original-polynomial certificate exclusions in two characteristics. -/
theorem original_rectangle_examples :
    (¬ NSRefutes {f : MvPolynomial (Var 4 8) (ZMod 2) | IsBAxiom 4 8 f} 2) ∧
    (¬ NSRefutes {f : MvPolynomial (Var 4 7) (ZMod 3) | IsBAxiom 4 7 f} 2) ∧
    (¬ NSRefutes {f : MvPolynomial (Var 3 6) (ZMod 2) | IsBAxiom 3 6 f} 0) := by
  exact ⟨no_NSRefutes_of_design four_by_eight_design (by decide) (by decide),
    no_NSRefutes_of_design characteristic_three_design (by decide) (by decide),
    concrete_family_NS_lower_bound 0 0 (by decide)⟩

/-- An assignment satisfying the original totalities and collisions forces equal dimensions. -/
theorem solution_implies_square {F : Type*} [Field F] {n m : ℕ} (x : Var n m → F)
    (hx : ∀ f : MvPolynomial (Var n m) F, IsBAxiom n m f → eval x f=0) : n=m := by
  classical
  have hr : ∀ i : Label n, ∑ j : Label m, x (i,j)=1 := by
    intro i
    have hh := hx (rowAxiom i) (IsBAxiom.row i)
    simpa [rowAxiom,sub_eq_zero] using hh
  have hc : ∀ j : Label m, ∑ i : Label n, x (i,j)=1 := by
    intro j
    have hh := hx (colAxiom j) (IsBAxiom.col j)
    simpa [colAxiom,sub_eq_zero] using hh
  have er : ∀ i : Label n, ∃ j : Label m, x (i,j)≠0 := by
    intro i
    by_contra he
    push_neg at he
    have hz : ∑ j : Label m, x (i,j)=0 := Finset.sum_eq_zero (fun j _ => he j)
    exact one_ne_zero ((hr i).symm.trans hz)
  have ec : ∀ j : Label m, ∃ i : Label n, x (i,j)≠0 := by
    intro j
    by_contra he
    push_neg at he
    have hz : ∑ i : Label n, x (i,j)=0 := Finset.sum_eq_zero (fun i _ => he i)
    exact one_ne_zero ((hc j).symm.trans hz)
  choose r hrow using er
  have hri : Function.Injective r := by
    intro i k he
    by_contra hne
    have hz := hx (X (i,r i)*X (k,r i)) (IsBAxiom.colCollision i k (r i) hne)
    have hk : x (k,r i)≠0 := by simpa only [he] using hrow k
    exact (mul_ne_zero (hrow i) hk) (by simpa using hz)
  have hrs : Function.Surjective r := by
    intro j
    obtain ⟨i,hi⟩ := ec j
    refine ⟨i,?_⟩
    by_contra hne
    have hz := hx (X (i,r i)*X (i,j)) (IsBAxiom.rowCollision i (r i) j hne)
    exact (mul_ne_zero (hrow i) hi) (by simpa using hz)
  have hcard := Fintype.card_congr (Equiv.ofBijective r ⟨hri,hrs⟩)
  simpa [Label] using hcard

/-- The hard family is unsatisfiable over every field, so its lower bound has actual content. -/
theorem concrete_family_unsatisfiable {F : Type*} [Field F] (a : ℕ) :
    ¬ ∃ x : Var (3*2^a) (6*2^a) → F,
      ∀ f : MvPolynomial (Var (3*2^a) (6*2^a)) F,
        IsBAxiom (3*2^a) (6*2^a) f → eval x f=0 := by
  rintro ⟨x,hx⟩
  have he := solution_implies_square x hx
  have hq : 0<2^a := pow_pos (by decide) _
  omega

end SelfContainedCycle054



