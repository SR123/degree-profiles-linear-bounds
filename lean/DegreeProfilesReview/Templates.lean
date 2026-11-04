/-
Stage 2, step 1b–2: uniform polynomial templates, their polynomial instances, the ACTUAL
NS/PC degree profiles, degree stability and degree-zero stabilisation.

A template (manuscript §3.1, "Uniform polynomial templates") consists of
* a basis system `Var` of variables, each with at most `k` labels,
* a basis system `Ax` of axiom indices, each with at most `s` labels,
* a coefficient function `coeff i m` (coefficient of the monomial `m` in the axiom with index
  `i`) which is INVARIANT under relabelling and independent of the universe size,
* a degree bound `D`, and `n₀ ≥ max {1, kD + s}`.

The instance at universe size `t` is the set of polynomials `poly t i ∈ R[Var.Rk t]`,
`i ∈ Ax.Rk t`, whose coefficient at a rank-`t` monomial `m` is `coeff (up i) (up m)`.
The profiles are `PC.pcDegree (inst t)` and `NS.nsDegree (inst t)`: the actual proof-system
definitions of `PolynomialCalculus.lean` and `Nullstellensatz.lean`.

Proved here without external hypotheses:
* `totalDegree_poly`: for `t ≥ n₀` the degree of an instance axiom is the rank-independent
  `axDeg` of its index (the manuscript's "we may enlarge n₀ to make each axiom-orbit degree
  constant" is a theorem for `n₀ ≥ kD + s`);
* `zeroStable_pc`, `zeroStable_ns`: the degree-zero predicate is constant beyond `n₀`;
* `inst_map`: base change of the coefficient field commutes with taking instances.
-/
import DegreeProfilesReview.BasisSystems
import DegreeProfilesReview.FieldDescent
import DegreeProfilesReview.LinearBounds

open MvPolynomial

namespace DegreeProfilesReview.Uniform

open BasisSystem

/-- A uniform polynomial template with coefficients in the field `R`. -/
structure Template (R : Type) [Field R] where
  Var : BasisSystem
  Ax : BasisSystem
  k : ℕ
  s : ℕ
  D : ℕ
  n0 : ℕ
  hk : 1 ≤ k
  hn0 : 1 ≤ n0
  hn0' : k * D + s ≤ n0
  var_bounded : Var.Bounded k
  ax_bounded : Ax.Bounded s
  /-- Coefficient of the monomial `m` in the axiom with index `i`. -/
  coeff : Ax.Obj → (Var.Obj →₀ ℕ) → R
  coeff_inv : ∀ (g : Equiv.Perm ℕ) i m, coeff (g • i) (Var.monSMul g m) = coeff i m
  coeff_deg : ∀ i m, coeff i m ≠ 0 → mdeg m ≤ D

namespace Template

variable {R : Type} [Field R] (T : Template R)

/-! ### Instances and profiles -/

theorem finite_support (t : ℕ) (i : T.Ax.Rk t) :
    (Function.support fun m : T.Var.Rk t →₀ ℕ =>
      T.coeff (T.Ax.up t i) (T.Var.monUp t m)).Finite := by
  have hfin : Set.Finite {m : T.Var.Rk t →₀ ℕ | mdeg m ≤ T.D} :=
    Set.finite_coe_iff.mp (finite_mdeg_le (T.Var.Rk t) T.D)
  apply hfin.subset
  intro m hm
  have := T.coeff_deg _ _ hm
  rwa [mdeg_monUp] at this

/-- The axiom with index `i` at universe size `t`. -/
noncomputable def poly (t : ℕ) (i : T.Ax.Rk t) : MvPolynomial (T.Var.Rk t) R :=
  Finsupp.ofSupportFinite _ (T.finite_support t i)

theorem coeff_poly (t : ℕ) (i : T.Ax.Rk t) (m : T.Var.Rk t →₀ ℕ) :
    MvPolynomial.coeff m (T.poly t i) = T.coeff (T.Ax.up t i) (T.Var.monUp t m) := rfl

/-- The polynomial system at universe size `t`. -/
def inst (t : ℕ) : Set (MvPolynomial (T.Var.Rk t) R) := Set.range (T.poly t)

/-- The actual ordinary-PC degree profile. -/
noncomputable def pcProfile (n : ℕ) : ℕ∞ := PC.pcDegree (T.inst n)

/-- The actual total-product NS degree profile. -/
noncomputable def nsProfile (n : ℕ) : ℕ∞ := NS.nsDegree (T.inst n)

theorem pcProfile_le_nsProfile (n : ℕ) : T.pcProfile n ≤ T.nsProfile n :=
  NS.pcDegree_le_nsDegree _

/-! ### The rank-independent degree of an axiom index -/

open Classical in
/-- The degree of the formal axiom with index `i`: the least bound on the degrees of its
monomials. -/
noncomputable def axDeg (i : T.Ax.Obj) : ℕ :=
  Nat.find (⟨T.D, fun m hm => T.coeff_deg i m hm⟩ :
    ∃ d, ∀ m, T.coeff i m ≠ 0 → mdeg m ≤ d)

theorem le_axDeg {i : T.Ax.Obj} {m : T.Var.Obj →₀ ℕ} (h : T.coeff i m ≠ 0) :
    mdeg m ≤ T.axDeg i := by
  classical
  exact Nat.find_spec (⟨T.D, fun m hm => T.coeff_deg i m hm⟩ :
    ∃ d, ∀ m, T.coeff i m ≠ 0 → mdeg m ≤ d) m h

theorem axDeg_le_D (i : T.Ax.Obj) : T.axDeg i ≤ T.D := by
  classical
  exact Nat.find_min' _ fun m hm => T.coeff_deg i m hm

theorem exists_axDeg {i : T.Ax.Obj} (h : 0 < T.axDeg i) :
    ∃ m, T.coeff i m ≠ 0 ∧ mdeg m = T.axDeg i := by
  classical
  obtain ⟨e, he⟩ : ∃ e, T.axDeg i = e + 1 := ⟨T.axDeg i - 1, by omega⟩
  have hmin : ¬ ∀ m, T.coeff i m ≠ 0 → mdeg m ≤ e :=
    Nat.find_min (⟨T.D, fun m hm => T.coeff_deg i m hm⟩ :
      ∃ d, ∀ m, T.coeff i m ≠ 0 → mdeg m ≤ d) (by unfold axDeg at he; omega)
  push_neg at hmin
  obtain ⟨m, hm, hlt⟩ := hmin
  have := T.le_axDeg hm
  exact ⟨m, hm, by omega⟩

theorem axDeg_smul (g : Equiv.Perm ℕ) (i : T.Ax.Obj) : T.axDeg (g • i) = T.axDeg i := by
  classical
  have key : ∀ (h : Equiv.Perm ℕ) (j : T.Ax.Obj), T.axDeg (h • j) ≤ T.axDeg j := by
    intro h j
    apply Nat.find_min'
    intro m hm
    have e : T.coeff (h • j) m = T.coeff j (T.Var.monSMul h⁻¹ m) := by
      have := T.coeff_inv h j (T.Var.monSMul h⁻¹ m)
      rwa [← monSMul_mul, mul_inv_cancel, monSMul_one] at this
    rw [e] at hm
    have := T.le_axDeg hm
    rwa [mdeg_monSMul] at this
  apply le_antisymm (key g i)
  have := key g⁻¹ (g • i)
  rwa [inv_smul_smul] at this

/-! ### Degree stability -/

theorem totalDegree_poly_le (t : ℕ) (i : T.Ax.Rk t) :
    (T.poly t i).totalDegree ≤ T.axDeg (T.Ax.up t i) := by
  apply Finset.sup_le
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_poly] at hm
  have := T.le_axDeg hm
  rwa [mdeg_monUp] at this

/-- Moving a monomial of an axiom into rank `t` without moving the axiom index. -/
theorem exists_rank_monomial {t : ℕ} (ht : T.n0 ≤ t) (i : T.Ax.Rk t) {m : T.Var.Obj →₀ ℕ}
    (hm : T.coeff (T.Ax.up t i) m ≠ 0) :
    ∃ m' : T.Var.Rk t →₀ ℕ, T.coeff (T.Ax.up t i) (T.Var.monUp t m') ≠ 0 ∧
      mdeg m' = mdeg m := by
  have hA : T.Ax.supp (T.Ax.up t i) ⊆ Finset.range t := T.Ax.supp_up t i
  have hcard : (T.Ax.supp (T.Ax.up t i) ∪ T.Var.monSupp m).card ≤ t := by
    have h1 := Finset.card_union_le (T.Ax.supp (T.Ax.up t i)) (T.Var.monSupp m)
    have h2 := T.ax_bounded (T.Ax.up t i)
    have h3 := card_monSupp_le T.var_bounded m
    have h4 : T.k * mdeg m ≤ T.k * T.D := Nat.mul_le_mul_left _ (T.coeff_deg _ _ hm)
    have h5 := T.hn0'
    omega
  obtain ⟨σ, hσA, hσB⟩ := exists_perm_fix_move' _ (T.Var.monSupp m) t hA hcard
  have hfix : σ • T.Ax.up t i = T.Ax.up t i := T.Ax.fixed σ _ hσA
  have hsupp : T.Var.monSupp (T.Var.monSMul σ m) ⊆ Finset.range t := by
    rw [monSupp_monSMul]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hσB b hb)
  obtain ⟨m', hm'⟩ := (T.Var.range_monUp t _).mpr hsupp
  refine ⟨m', ?_, ?_⟩
  · rw [hm']
    have := T.coeff_inv σ (T.Ax.up t i) m
    rw [hfix] at this
    rwa [this]
  · rw [← mdeg_monUp, hm', mdeg_monSMul]

/-- **Degree stability.**  Beyond `n₀` the degree of an instance axiom is `axDeg` of its
index. -/
theorem totalDegree_poly {t : ℕ} (ht : T.n0 ≤ t) (i : T.Ax.Rk t) :
    (T.poly t i).totalDegree = T.axDeg (T.Ax.up t i) := by
  apply le_antisymm (T.totalDegree_poly_le t i)
  by_cases h0 : T.axDeg (T.Ax.up t i) = 0
  · rw [h0]; exact Nat.zero_le _
  · obtain ⟨m, hm, hdeg⟩ := T.exists_axDeg (Nat.pos_of_ne_zero h0)
    obtain ⟨m', hm', hdeg'⟩ := T.exists_rank_monomial ht i hm
    have hsupp : m' ∈ (T.poly t i).support := by
      rw [MvPolynomial.mem_support_iff, coeff_poly]; exact hm'
    have := le_totalDegree hsupp
    have e : (m'.sum fun _ e => e) = mdeg m' := rfl
    rw [e, hdeg', hdeg] at this
    exact this

/-! ### Degree-zero stabilisation -/

/-- Some axiom is a nonzero constant (a statement independent of the universe size). -/
def HasConstAxiom : Prop :=
  ∃ i : T.Ax.Obj, T.coeff i 0 ≠ 0 ∧ ∀ m, m ≠ 0 → T.coeff i m = 0

theorem mdeg_eq_zero {α : Type*} {m : α →₀ ℕ} (h : mdeg m = 0) : m = 0 := by
  ext a
  have := le_mdeg m a
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem one_mem_V0_zero_iff {t : ℕ} (ht : T.n0 ≤ t) :
    (1 : MvPolynomial (T.Var.Rk t) R) ∈ PC.V0 (T.inst t) 0 ↔ T.HasConstAxiom := by
  constructor
  · intro h1
    by_contra hno
    have hzero : ∀ f ∈ {f | f ∈ T.inst t ∧ f.totalDegree ≤ 0}, f = (0 : MvPolynomial _ R) := by
      rintro _ ⟨⟨x, rfl⟩, hdeg⟩
      rw [T.totalDegree_poly ht x] at hdeg
      have hall : ∀ m, T.coeff (T.Ax.up t x) m ≠ 0 → m = 0 := fun m hm =>
        mdeg_eq_zero (by have := T.le_axDeg hm; omega)
      have hc0 : T.coeff (T.Ax.up t x) 0 = 0 := by
        by_contra hc
        exact hno ⟨T.Ax.up t x, hc, fun m hm => by
          by_contra hcm
          exact hm (hall m hcm)⟩
      apply MvPolynomial.ext
      intro m
      rw [coeff_poly, MvPolynomial.coeff_zero]
      by_contra hcm
      have := hall _ hcm
      rw [this] at hcm
      exact hcm hc0
    have hbot : PC.V0 (T.inst t) 0 = ⊥ := by
      unfold PC.V0
      rw [Submodule.span_eq_bot]
      exact hzero
    rw [hbot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · rintro ⟨i, hi0, hi⟩
    -- move the index into rank `t`
    have hcard : ((∅ : Finset ℕ) ∪ T.Ax.supp i).card ≤ t := by
      rw [Finset.empty_union]
      have h1 := T.ax_bounded i
      have h2 := T.hn0'
      omega
    obtain ⟨σ, -, hσ⟩ := exists_perm_fix_move' ∅ (T.Ax.supp i) t (Finset.empty_subset _) hcard
    have hsupp : T.Ax.supp (σ • i) ⊆ Finset.range t := by
      rw [T.Ax.supp_smul]
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hσ b hb)
    obtain ⟨x, hx⟩ := (T.Ax.range_up t _).mpr hsupp
    have hcoeff : ∀ m, T.coeff (σ • i) m = T.coeff i (T.Var.monSMul σ⁻¹ m) := by
      intro m
      have := T.coeff_inv σ i (T.Var.monSMul σ⁻¹ m)
      rwa [← monSMul_mul, mul_inv_cancel, monSMul_one] at this
    have hpoly : T.poly t x = C (T.coeff i 0) := by
      classical
      apply MvPolynomial.ext
      intro m
      rw [coeff_poly, hx, hcoeff, MvPolynomial.coeff_C]
      by_cases hm : 0 = m
      · subst hm
        rw [if_pos rfl]
        unfold BasisSystem.monUp BasisSystem.monSMul
        rw [Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]
      · rw [if_neg hm]
        apply hi
        intro h0
        apply hm
        have h1 : T.Var.monSMul σ⁻¹ (T.Var.monUp t m) = T.Var.monSMul σ⁻¹ 0 := by
          rw [h0]; unfold BasisSystem.monSMul; rw [Finsupp.mapDomain_zero]
        have h2 := T.Var.monSMul_injective σ⁻¹ h1
        have h3 : T.Var.monUp t m = T.Var.monUp t 0 := by
          rw [h2]; unfold BasisSystem.monUp; rw [Finsupp.mapDomain_zero]
        exact (T.Var.monUp_injective t h3).symm
    have hmem : C (T.coeff i 0) ∈ PC.V0 (T.inst t) 0 := by
      apply Submodule.subset_span
      refine ⟨⟨x, hpoly⟩, ?_⟩
      rw [totalDegree_C]
    have := (PC.V0 (T.inst t) 0).smul_mem (T.coeff i 0)⁻¹ hmem
    rwa [smul_eq_C_mul, ← C_mul, inv_mul_cancel₀ hi0, C_1] at this

theorem pc_refutes_zero_iff {t : ℕ} (ht : T.n0 ≤ t) :
    PC.Refutes (T.inst t) 0 ↔ T.HasConstAxiom := by
  rw [PC.refutes_iff_one_mem_Vinf, PC.Vinf_zero, T.one_mem_V0_zero_iff ht]

theorem NSspan_zero {σ : Type*} (Γ : Set (MvPolynomial σ R)) : NS.NSspan Γ 0 = PC.V0 Γ 0 := by
  unfold NS.NSspan PC.V0
  congr 1
  ext g
  constructor
  · rintro ⟨m, f, hf, hdeg, rfl⟩
    have hm : m = 0 := mdeg_eq_zero (by
      have : NS.mdeg m = mdeg m := rfl
      omega)
    subst hm
    have h1 : (monomial (0 : σ →₀ ℕ) (1 : R)) = 1 := rfl
    rw [h1, one_mul]
    exact ⟨hf, by omega⟩
  · rintro ⟨hf, hdeg⟩
    refine ⟨0, g, hf, ?_, ?_⟩
    · have : NS.mdeg (0 : σ →₀ ℕ) = 0 := by simp [NS.mdeg]
      omega
    · have h1 : (monomial (0 : σ →₀ ℕ) (1 : R)) = 1 := rfl
      rw [h1, one_mul]

theorem ns_refutes_zero_iff {t : ℕ} (ht : T.n0 ≤ t) :
    NS.NSRefutes (T.inst t) 0 ↔ T.HasConstAxiom := by
  rw [NS.nsRefutes_iff_one_mem_NSspan, NSspan_zero, T.one_mem_V0_zero_iff ht]

/-- **Degree-zero stabilisation for the actual PC profile.** -/
theorem zeroStable_pc : Profiles.ZeroStable T.n0 T.pcProfile := by
  intro n m hn hm
  unfold pcProfile
  rw [PC.pcDegree_le_iff, PC.pcDegree_le_iff, T.pc_refutes_zero_iff hn, T.pc_refutes_zero_iff hm]

/-- **Degree-zero stabilisation for the actual NS profile.** -/
theorem zeroStable_ns : Profiles.ZeroStable T.n0 T.nsProfile := by
  intro n m hn hm
  unfold nsProfile
  rw [NS.nsDegree_le_iff, NS.nsDegree_le_iff, T.ns_refutes_zero_iff hn, T.ns_refutes_zero_iff hm]

/-! ### Base change of the coefficient field -/

/-- The same template with coefficients mapped along a field homomorphism. -/
@[reducible] def map {S : Type} [Field S] (φ : R →+* S) : Template S where
  Var := T.Var
  Ax := T.Ax
  k := T.k
  s := T.s
  D := T.D
  n0 := T.n0
  hk := T.hk
  hn0 := T.hn0
  hn0' := T.hn0'
  var_bounded := T.var_bounded
  ax_bounded := T.ax_bounded
  coeff := fun i m => φ (T.coeff i m)
  coeff_inv := fun g i m => by rw [T.coeff_inv]
  coeff_deg := fun i m h => T.coeff_deg i m fun h0 => h (by rw [h0, map_zero])

theorem poly_map {S : Type} [Field S] (φ : R →+* S) (t : ℕ) (i : T.Ax.Rk t) :
    (T.map φ).poly t i = MvPolynomial.map φ (T.poly t i) := by
  apply MvPolynomial.ext
  intro m
  exact (MvPolynomial.coeff_map φ (T.poly t i) m).symm

theorem inst_map {K : Type} [Field K] [Algebra R K] (t : ℕ) :
    (T.map (algebraMap R K)).inst t = FieldDescent.mapSet K (T.inst t) := by
  unfold inst FieldDescent.mapSet
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨T.poly t i, ⟨i, rfl⟩, (T.poly_map _ t i).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, T.poly_map _ t i⟩

/-- The actual profiles do not change under extension of the coefficient field. -/
theorem pcProfile_map {K : Type} [Field K] [Algebra R K] (n : ℕ) :
    (T.map (algebraMap R K)).pcProfile n = T.pcProfile n := by
  unfold pcProfile
  rw [inst_map, FieldDescent.pcDegree_map]

theorem nsProfile_map {K : Type} [Field K] [Algebra R K] (n : ℕ) :
    (T.map (algebraMap R K)).nsProfile n = T.nsProfile n := by
  unfold nsProfile
  rw [inst_map, FieldDescent.nsDegree_map]

end Template

end DegreeProfilesReview.Uniform
