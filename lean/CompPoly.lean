/-
Claude, 26 Sep 2026.  Uniform NS–PC comparison, part 3: from permutation modules over an
algebraically closed field to the polynomial chains of `ChainBound`, over any field of
characteristic `p`.

* Scalar extension (`extS`): for a set `X` and fields `R ⊆ K`, the `K`-span of an
  `R`-subspace of `R^X` in `K^X`.  Strict inclusions stay strict (a separating `R`-functional
  extends `K`-linearly), and invariance under a permutation action is kept.
* Polynomials (`cf`): the coefficient map from `R[x_v : v ∈ 𝒰_n]` to `R[(𝒰.mon t)_n]`, where
  `𝒰.mon t` is Stage 5's basis system of monomials of degree `≤ t`.  It is injective on
  `restrictTotalDegree _ R t` and intertwines `rename (g • ·)` with the permutation action.
* `chainBound_of_bounded`: `ClaudeC017.ChainBound R 𝒰` for every basis system of bounded
  support, i.e. the hypothesis (★) of `C017TypeAgreement`, now proved.
-/
import CompChain

set_option autoImplicit false
open MvPolynomial

namespace ClaudeComparison
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep

/-! ### Scalar extension on `R^X` -/

section BaseChange
variable {R K : Type} [Field R] [Field K] [Algebra R K] {X : Type}

/-- Coefficientwise extension of scalars `R^X → K^X`. -/
noncomputable def ext (v : X →₀ R) : X →₀ K :=
  Finsupp.mapRange (algebraMap R K) (map_zero _) v

theorem ext_add (v v' : X →₀ R) : ext (K := K) (v + v') = ext v + ext v' :=
  Finsupp.mapRange_add (fun _ _ => map_add _ _ _) v v'

theorem ext_single (i : X) (b : R) :
    ext (K := K) (Finsupp.single i b) = Finsupp.single i (algebraMap R K b) :=
  Finsupp.mapRange_single

/-- The `K`-span of an `R`-subspace. -/
noncomputable def extS (W : Submodule R (X →₀ R)) : Submodule K (X →₀ K) :=
  Submodule.span K (ext '' (W : Set (X →₀ R)))

theorem extS_mono {W W' : Submodule R (X →₀ R)} (h : W ≤ W') :
    extS (K := K) W ≤ extS W' :=
  Submodule.span_mono (Set.image_mono h)

/-- A functional separating `v` from `W` extends to `K^X`. -/
theorem ext_notMem {W : Submodule R (X →₀ R)} {v : X →₀ R} (hv : v ∉ W) :
    ext (K := K) v ∉ extS (K := K) W := by
  obtain ⟨φ, hφv, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let φK : (X →₀ K) →ₗ[K] K :=
    Finsupp.linearCombination K fun i => algebraMap R K (φ (Finsupp.single i 1))
  have key : ∀ y : X →₀ R, φK (ext y) = algebraMap R K (φ y) := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero =>
      have : ext (K := K) (0 : X →₀ R) = 0 := Finsupp.mapRange_zero
      rw [this, map_zero, map_zero, map_zero]
    | add f g hf hg => rw [ext_add, map_add, hf, hg, map_add, map_add]
    | single i b =>
      rw [ext_single, Finsupp.linearCombination_single, smul_eq_mul, ← map_mul,
        show Finsupp.single i b = b • Finsupp.single i (1 : R) by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  have hker : extS (K := K) W ≤ LinearMap.ker φK := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    have h0 : φ y ∈ W.map φ := Submodule.mem_map_of_mem hy
    rw [hφW, Submodule.mem_bot] at h0
    change φK (ext y) = 0
    rw [key, h0, map_zero]
  intro hmem
  have h1 := hker hmem
  rw [LinearMap.mem_ker, key] at h1
  exact hφv ((map_eq_zero_iff _ (algebraMap R K).injective).mp h1)

theorem extS_strict {W W' : Submodule R (X →₀ R)} (h : W < W') :
    extS (K := K) W < extS W' := by
  obtain ⟨v, hv', hv⟩ := SetLike.exists_of_lt h
  exact lt_of_le_of_ne (extS_mono h.le) fun heq =>
    ext_notMem (K := K) hv (heq ▸ Submodule.subset_span ⟨v, hv', rfl⟩)

theorem ext_ofMulAction {G : Type} [Group G] [MulAction G X] (g : G) (v : X →₀ R) :
    Representation.ofMulAction K G X g (ext v) = ext (Representation.ofMulAction R G X g v) := by
  ext i
  simp only [ext, Representation.ofMulAction_apply, Finsupp.mapRange_apply]

theorem extS_isInv {G : Type} [Group G] [MulAction G X] {W : Submodule R (X →₀ R)}
    (hW : IsInv (Representation.ofMulAction R G X) W) :
    IsInv (Representation.ofMulAction K G X) (extS (K := K) W) := by
  intro g
  apply Submodule.span_le.mpr
  rintro _ ⟨y, hy, rfl⟩
  change Representation.ofMulAction K G X g (ext y) ∈ extS W
  rw [ext_ofMulAction]
  exact Submodule.subset_span ⟨_, hW g hy, rfl⟩

end BaseChange

/-! ### Polynomials of degree `≤ t` as the monomial permutation module -/

section Poly
variable {R : Type} [Field R] (𝒰 : BasisSystem) (t n : ℕ)

/-- Coefficients at the monomials of degree `≤ t`. -/
noncomputable def cf : MvPolynomial (𝒰.Rk n) R →ₗ[R] ((𝒰.mon t).Rk n →₀ R) where
  toFun f := Finsupp.equivFunOnFinite.symm fun m => coeff m.1 f
  map_add' f f' := by
    ext m
    simp only [Finsupp.equivFunOnFinite_symm_apply_toFun, coeff_add, Finsupp.coe_add,
      Pi.add_apply]
  map_smul' c f := by
    ext m
    simp only [Finsupp.equivFunOnFinite_symm_apply_toFun, coeff_smul, smul_eq_mul,
      RingHom.id_apply, Finsupp.coe_smul, Pi.smul_apply]

theorem cf_apply (f : MvPolynomial (𝒰.Rk n) R) (m : (𝒰.mon t).Rk n) :
    cf 𝒰 t n f m = coeff m.1 f := rfl

variable {𝒰 t n}

theorem cf_injOn {f : MvPolynomial (𝒰.Rk n) R} (hf : f ∈ restrictTotalDegree (𝒰.Rk n) R t)
    (h0 : cf 𝒰 t n f = 0) : f = 0 := by
  rw [mem_restrictTotalDegree] at hf
  ext m
  rw [coeff_zero]
  by_contra hne
  have hdeg : (m.sum fun _ e => e) ≤ t :=
    le_trans (le_totalDegree (mem_support_iff.mpr hne)) hf
  have := congrArg (fun F : (𝒰.mon t).Rk n →₀ R => F ⟨m, hdeg⟩) h0
  exact hne this

/-- The action of `S_n` on monomials of degree `≤ t` is relabelling of variables. -/
theorem mon_smul_val (g : Sfin n) (m : (𝒰.mon t).Rk n) :
    (g • m).1 = Finsupp.mapDomain (fun v : 𝒰.Rk n => g • v) m.1 := by
  apply 𝒰.monUp_injective n
  have h := congrArg Subtype.val (up_smul (𝒰 := 𝒰.mon t) g m)
  change 𝒰.monUp n (g • m).1 = 𝒰.monSMul g.1 (𝒰.monUp n m.1) at h
  rw [h]
  unfold BasisSystem.monUp BasisSystem.monSMul
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext v
  exact (up_smul g v).symm

theorem cf_rename (g : Sfin n) (f : MvPolynomial (𝒰.Rk n) R) :
    cf 𝒰 t n (rename (fun v => g • v) f) =
      Representation.ofMulAction R (Sfin n) ((𝒰.mon t).Rk n) g (cf 𝒰 t n f) := by
  ext m
  rw [Representation.ofMulAction_apply, cf_apply, cf_apply, mon_smul_val]
  have hinj : Function.Injective (fun v : 𝒰.Rk n => g • v) := MulAction.injective g
  have hm : m.1 = Finsupp.mapDomain (fun v : 𝒰.Rk n => g • v)
      (Finsupp.mapDomain (fun v : 𝒰.Rk n => g⁻¹ • v) m.1) := by
    rw [← Finsupp.mapDomain_comp]
    have : ((fun v : 𝒰.Rk n => g • v) ∘ fun v => g⁻¹ • v) = id := by
      funext v; simp
    rw [this, Finsupp.mapDomain_id]
  rw [hm, coeff_rename_mapDomain _ hinj]
  congr 1
  rw [← Finsupp.mapDomain_comp]
  have : ((fun v : 𝒰.Rk n => g⁻¹ • v) ∘ fun v => g • v) = id := by
    funext v; simp
  rw [this, Finsupp.mapDomain_id]

end Poly

/-! ### The chain bound (★), proved -/

/-- **(★) holds.**  For every field `R` of prime characteristic `p` and every basis system of
bounded support, invariant chains of polynomials of degree `≤ t` have length bounded
independently of the universe size. -/
theorem chainBound_of_bounded (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p]
    (𝒰 : BasisSystem) {k : ℕ} (hk : 𝒰.Bounded k) : ClaudeC017.ChainBound R 𝒰 := by
  intro t
  obtain ⟨L, hL⟩ := chainBoundPerm p (AlgebraicClosure R) (𝒰.mon t)
    (BasisSystem.mon_bounded hk t)
  refine ⟨L, fun n W hWt hWinv hmono => ?_⟩
  -- coefficients
  let W1 : Fin (L + 2) → Submodule R ((𝒰.mon t).Rk n →₀ R) := fun i => (W i).map (cf 𝒰 t n)
  have hW1inv : ∀ i, IsInv (Representation.ofMulAction R (Sfin n) ((𝒰.mon t).Rk n)) (W1 i) := by
    rintro i g _ ⟨f, hf, rfl⟩
    change Representation.ofMulAction R (Sfin n) ((𝒰.mon t).Rk n) g (cf 𝒰 t n f) ∈ W1 i
    rw [← cf_rename]
    exact Submodule.mem_map_of_mem (hWinv i g f hf)
  have hW1mono : StrictMono W1 := by
    intro i j hij
    refine lt_of_le_of_ne (Submodule.map_mono (hmono hij).le) fun heq => ?_
    apply not_le_of_gt (hmono hij)
    intro f hf
    have hmem : cf 𝒰 t n f ∈ W1 i := by
      change cf 𝒰 t n f ∈ W1 i
      rw [heq]
      exact Submodule.mem_map_of_mem hf
    obtain ⟨u, hu, hfu⟩ := hmem
    have hdiff : f - u ∈ restrictTotalDegree (𝒰.Rk n) R t := sub_mem (hWt j hf) (hWt i hu)
    have h0 : cf 𝒰 t n (f - u) = 0 := by rw [map_sub, hfu, sub_self]
    have := cf_injOn hdiff h0
    rw [sub_eq_zero] at this
    rw [this]
    exact hu
  -- extension of scalars to the algebraic closure
  let W2 : Fin (L + 2) → Submodule (AlgebraicClosure R) ((𝒰.mon t).Rk n →₀ AlgebraicClosure R) :=
    fun i => extS (W1 i)
  exact hL n W2 (fun i => extS_isInv (hW1inv i)) fun i j hij => extS_strict (hW1mono hij)

end ClaudeComparison
