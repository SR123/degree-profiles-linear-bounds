/-
Stage 2, step 3: the bridge between the CONCRETE ordinary-PC closure (subspaces of `K[x]`,
`PCClosure.lean`) and the CATEGORICAL closure (`PCTransport.lean`), in the category of
`K`-vector spaces.

For a degree `d ≥ 1` and a linear map `v₀` from some vector space into `P_{≤ d}`, the datum

  `W = P_{≤ d}`, `L = P_{≤ d-1} ↪ W`, `M = X ⊗ L → W` (multiplication), `U = K → W` (`1`),
  `V₀ → W` (`v₀`),  `T (S → L) = (X ⊗ S → X ⊗ L)`

is a `PCDatum` in `ModuleCat K`.  Proved, with no external hypothesis:

* `rng_next`     : the image of the categorical successor stage is `step d` of the image;
* `rng_stage`    : if the image of `v₀` is the span `V₀` of the axioms of degree `≤ d`, then
                   the image of the `j`-th categorical stage is the `j`-th stage `V j` of the
                   actual closure;
* `constMem_iff` : the categorical membership predicate `c ≫ coker(v_j) = 0` holds iff
                   `1 ∈ V j`;
* `comp_cokernel_π_eq_zero_iff` : the corresponding statement for a single map, used for the
                   NS certificate map.
-/
import DegreeProfilesReview.PCTransport
import DegreeProfilesReview.PCTensorForm
import DegreeProfilesReview.Nullstellensatz
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Kernels

open CategoryTheory CategoryTheory.Limits MvPolynomial TensorProduct

namespace DegreeProfilesReview.Concrete

open DegreeProfilesReview.PC DegreeProfilesReview.Transport

/-! ### Kernels and cokernels of vector spaces -/

section Vect

variable {K : Type} [Field K]

theorem range_kernel_ι {G H : ModuleCat.{0} K} (f : G ⟶ H) :
    LinearMap.range (kernel.ι f).hom = LinearMap.ker f.hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (kernel.condition f)) y
  · intro hx
    refine ⟨(ModuleCat.kernelIsoKer f).inv.hom ⟨x, hx⟩, ?_⟩
    exact LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (ModuleCat.kernelIsoKer_inv_kernel_ι f)) ⟨x, hx⟩

theorem ker_cokernel_π {G H : ModuleCat.{0} K} (f : G ⟶ H) :
    LinearMap.ker (cokernel.π f).hom = LinearMap.range f.hom := by
  ext x
  rw [LinearMap.mem_ker]
  have h2 : (ModuleCat.cokernelIsoRangeQuotient f).hom.hom ((cokernel.π f).hom x) =
      (LinearMap.range f.hom).mkQ x :=
    LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom f)) x
  constructor
  · intro hx
    rw [hx, map_zero] at h2
    exact (Submodule.Quotient.mk_eq_zero _).mp h2.symm
  · intro hx
    have h3 : (LinearMap.range f.hom).mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [h3] at h2
    have h4 : (ModuleCat.cokernelIsoRangeQuotient f).inv.hom
        ((ModuleCat.cokernelIsoRangeQuotient f).hom.hom ((cokernel.π f).hom x)) =
        (cokernel.π f).hom x :=
      LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (ModuleCat.cokernelIsoRangeQuotient f).hom_inv_id)
        ((cokernel.π f).hom x)
    rw [← h4, h2, map_zero]

/-- `c ≫ coker f = 0` iff the image of `c` lies in the image of `f`. -/
theorem comp_cokernel_π_eq_zero_iff {A B C : ModuleCat.{0} K} (c : C ⟶ B) (f : A ⟶ B) :
    c ≫ cokernel.π f = 0 ↔ LinearMap.range c.hom ≤ LinearMap.range f.hom := by
  rw [← ker_cokernel_π f]
  constructor
  · intro h
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x
  · intro h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have := h ⟨x, rfl⟩
    rw [LinearMap.mem_ker] at this
    exact this

end Vect

/-! ### The concrete datum -/

section Datum

variable {K : Type} [Field K] {σ : Type}

/-- `P_{≤ d}` as a subspace. -/
abbrev Pd (σ : Type) (K : Type) [Field K] (d : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictTotalDegree σ K d

theorem Pd_mono {d d' : ℕ} (h : d ≤ d') : Pd σ K d ≤ Pd σ K d' := by
  intro f hf
  rw [mem_restrictTotalDegree] at hf ⊢
  omega

theorem lowDeg_eq {d : ℕ} (hd : 1 ≤ d) : lowDeg σ K d = Pd σ K (d - 1) := by
  unfold lowDeg
  rw [if_neg (by omega)]

/-- The inclusion `P_{≤ d-1} → P_{≤ d}`. -/
noncomputable def inclLow (σ : Type) (K : Type) [Field K] (d : ℕ) :
    Pd σ K (d - 1) →ₗ[K] Pd σ K d :=
  Submodule.inclusion (Pd_mono (Nat.sub_le d 1))

theorem mu_lTensor_mem {d : ℕ} (hd : 1 ≤ d) (x : VarSpace σ K ⊗[K] Pd σ K (d - 1)) :
    muRestrict (Pd σ K (d - 1)) x ∈ Pd σ K d := by
  have h1 : muRestrict (Pd σ K (d - 1)) x ∈ LinearMap.range (muRestrict (Pd σ K (d - 1))) :=
    ⟨x, rfl⟩
  rw [range_muRestrict] at h1
  have h2 : mulStep (Pd σ K (d - 1)) ≤ Pd σ K d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, f, hf, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree]
    apply totalDegree_X_mul_lowDeg i
    rw [lowDeg_eq hd]
    exact hf
  exact h2 h1

/-- Multiplication `X ⊗ P_{≤ d-1} → P_{≤ d}`. -/
noncomputable def mulLow (σ : Type) (K : Type) [Field K] {d : ℕ} (hd : 1 ≤ d) :
    VarSpace σ K ⊗[K] Pd σ K (d - 1) →ₗ[K] Pd σ K d :=
  LinearMap.codRestrict (Pd σ K d) (muRestrict (Pd σ K (d - 1))) (mu_lTensor_mem hd)

theorem one_mem_Pd (d : ℕ) : (1 : MvPolynomial σ K) ∈ Pd σ K d := by
  rw [mem_restrictTotalDegree, totalDegree_one]
  exact Nat.zero_le _

/-- The constant `1`, as a map `K → P_{≤ d}`. -/
noncomputable def constMap (σ : Type) (K : Type) [Field K] (d : ℕ) : K →ₗ[K] Pd σ K d :=
  LinearMap.toSpanSingleton K (Pd σ K d) ⟨1, one_mem_Pd d⟩

/-- The PC datum of the actual polynomial spaces, in the category of `K`-vector spaces. -/
noncomputable def datum (σ : Type) (K : Type) [Field K] {d : ℕ} (hd : 1 ≤ d)
    {V0mod : Type} [AddCommGroup V0mod] [Module K V0mod] (v0 : V0mod →ₗ[K] Pd σ K d) :
    PCDatum (ModuleCat.{0} K) where
  W := ModuleCat.of K (Pd σ K d)
  L := ModuleCat.of K (Pd σ K (d - 1))
  M := ModuleCat.of K (VarSpace σ K ⊗[K] Pd σ K (d - 1))
  U := ModuleCat.of K K
  V₀ := ModuleCat.of K V0mod
  ℓ := ModuleCat.ofHom (inclLow σ K d)
  μ := ModuleCat.ofHom (mulLow σ K hd)
  v₀ := ModuleCat.ofHom v0
  c := ModuleCat.ofHom (constMap σ K d)
  T := fun {_} s _ => Over.mk (ModuleCat.ofHom (LinearMap.lTensor (VarSpace σ K) s.hom))

/-- The image of multiplication restricted along an arbitrary linear map into `K[x]`. -/
theorem range_mu_lTensor {S : Type*} [AddCommGroup S] [Module K S]
    (g : S →ₗ[K] MvPolynomial σ K) :
    LinearMap.range (mu σ K ∘ₗ LinearMap.lTensor (VarSpace σ K) g) =
      mulStep (LinearMap.range g) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul c s =>
      rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, mu, TensorProduct.lift.tmul, varMul,
        Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
      apply Submodule.sum_mem
      intro i _
      rw [LinearMap.smul_apply]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, g s, ⟨s, rfl⟩, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, _, ⟨s, rfl⟩, rfl⟩
    refine ⟨Finsupp.single i 1 ⊗ₜ s, ?_⟩
    rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, mu, TensorProduct.lift.tmul,
      varMul_single]

variable {d : ℕ} (hd : 1 ≤ d) {V0mod : Type} [AddCommGroup V0mod] [Module K V0mod]
  (v0 : V0mod →ₗ[K] Pd σ K d)

/-- The image of an embedded stage, as a subspace of `K[x]`. -/
noncomputable def rng (v : Over (datum σ K hd v0).W) : Submodule K (MvPolynomial σ K) :=
  (LinearMap.range v.hom.hom).map (Pd σ K d).subtype

theorem rng_le (v : Over (datum σ K hd v0).W) : rng hd v0 v ≤ Pd σ K d := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

/-- One categorical step is one step of the actual closure. -/
theorem rng_next (v : Over (datum σ K hd v0).W) :
    rng hd v0 ((datum σ K hd v0).next v) = step d (rng hd v0 v) := by
  -- the quotient map and its kernel
  have hker : LinearMap.ker ((datum σ K hd v0).quot v).hom = LinearMap.range v.hom.hom :=
    ker_cokernel_π v.hom
  -- the embedded intersection
  have hinter : LinearMap.range ((datum σ K hd v0).inter v).hom =
      (LinearMap.range v.hom.hom).comap (inclLow σ K d) := by
    unfold PCDatum.inter
    rw [range_kernel_ι, ModuleCat.hom_comp, LinearMap.ker_comp, hker]
    rfl
  have hS : LinearMap.range
      ((Pd σ K (d - 1)).subtype ∘ₗ ((datum σ K hd v0).inter v).hom) =
        rng hd v0 v ⊓ lowDeg σ K d := by
    rw [LinearMap.range_comp, hinter, lowDeg_eq hd]
    ext f
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨_, hl, rfl⟩, l.2⟩
    · rintro ⟨⟨w, hw, hwf⟩, hfL⟩
      refine ⟨⟨f, hfL⟩, ?_, rfl⟩
      show inclLow σ K d ⟨f, hfL⟩ ∈ LinearMap.range v.hom.hom
      have : inclLow σ K d ⟨f, hfL⟩ = w := Subtype.ext hwf.symm
      rw [this]
      exact hw
  -- the image of restricted multiplication, inside `K[x]`
  have hmul : (LinearMap.range ((datum σ K hd v0).mulMap v).hom).map (Pd σ K d).subtype =
      mulStep (rng hd v0 v ⊓ lowDeg σ K d) := by
    have e1 : (Pd σ K d).subtype ∘ₗ ((datum σ K hd v0).mulMap v).hom =
        mu σ K ∘ₗ LinearMap.lTensor (VarSpace σ K)
          ((Pd σ K (d - 1)).subtype ∘ₗ ((datum σ K hd v0).inter v).hom) := by
      rw [LinearMap.lTensor_comp]
      rfl
    rw [← LinearMap.range_comp, e1, range_mu_lTensor, hS]
  -- the new stage
  have hnext : LinearMap.range ((datum σ K hd v0).next v).hom.hom =
      LinearMap.range ((datum σ K hd v0).mulMap v).hom ⊔ LinearMap.range v.hom.hom := by
    unfold PCDatum.next
    rw [Over.mk_hom, range_kernel_ι, ModuleCat.hom_comp, LinearMap.ker_comp, ker_cokernel_π,
      ModuleCat.hom_comp, LinearMap.range_comp, Submodule.comap_map_eq, hker]
  unfold rng
  rw [hnext, Submodule.map_sup, hmul, sup_comm]
  rfl

variable (Γ : Set (MvPolynomial σ K))

/-- The images of the categorical stages are the stages of the actual closure. -/
theorem rng_stage (h0 : (LinearMap.range v0).map (Pd σ K d).subtype = V0 Γ d) (j : ℕ) :
    rng hd v0 ((datum σ K hd v0).stage j) = V Γ d j := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    have e : (datum σ K hd v0).stage (j + 1) =
        (datum σ K hd v0).next ((datum σ K hd v0).stage j) := rfl
    rw [e, rng_next, ih]
    rfl

theorem one_mem_map_iff (R : Submodule K (Pd σ K d)) :
    (1 : MvPolynomial σ K) ∈ R.map (Pd σ K d).subtype ↔
      (⟨1, one_mem_Pd d⟩ : Pd σ K d) ∈ R := by
  constructor
  · rintro ⟨x, hx, hx1⟩
    have : x = ⟨1, one_mem_Pd d⟩ := Subtype.ext hx1
    rwa [← this]
  · intro h
    exact ⟨_, h, rfl⟩

theorem range_constMap_le_iff (R : Submodule K (Pd σ K d)) :
    LinearMap.range (constMap σ K d) ≤ R ↔ (⟨1, one_mem_Pd d⟩ : Pd σ K d) ∈ R := by
  constructor
  · intro h
    apply h
    exact ⟨1, by simp [constMap]⟩
  · rintro h _ ⟨a, rfl⟩
    have : constMap σ K d a = a • (⟨1, one_mem_Pd d⟩ : Pd σ K d) := by simp [constMap]
    rw [this]
    exact R.smul_mem a h

/-- **Bridge for PC.**  Categorical membership of the constant in the `j`-th stage is
membership of `1` in the `j`-th stage of the actual closure. -/
theorem constMem_iff (h0 : (LinearMap.range v0).map (Pd σ K d).subtype = V0 Γ d) (j : ℕ) :
    (datum σ K hd v0).ConstMem j ↔ (1 : MvPolynomial σ K) ∈ V Γ d j := by
  unfold PCDatum.ConstMem PCDatum.quot
  rw [comp_cokernel_π_eq_zero_iff, ← rng_stage hd v0 Γ h0 j]
  unfold rng
  rw [one_mem_map_iff]
  exact range_constMap_le_iff _

/-- **Bridge for NS.**  For a linear map `A` into `P_{≤ d}` whose image is the certificate
span, `K → P_{≤d} → coker A` vanishes iff `1` lies in the certificate span. -/
theorem nsMem_iff {Cmod : Type} [AddCommGroup Cmod] [Module K Cmod] (A : Cmod →ₗ[K] Pd σ K d)
    (hA : (LinearMap.range A).map (Pd σ K d).subtype = NS.NSspan Γ d) :
    ModuleCat.ofHom (constMap σ K d) ≫ cokernel.π (ModuleCat.ofHom A) = 0 ↔
      (1 : MvPolynomial σ K) ∈ NS.NSspan Γ d := by
  rw [comp_cokernel_π_eq_zero_iff, ← hA, one_mem_map_iff]
  exact range_constMap_le_iff _

end Datum

end DegreeProfilesReview.Concrete
