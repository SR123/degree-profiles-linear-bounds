/-
Prompt 04: the closure step in its tensor-product form.

`X` is the vector space freely spanned by the variables, `μ : X ⊗ K[x] → K[x]` is
multiplication, and for a subspace `S` the restricted multiplication is
`μ ∘ (X ⊗ S → X ⊗ K[x])`.  Its image is exactly `mulStep S = span {X i * f | f ∈ S}`.
Hence `step d V = V ⊔ im (μ restricted to X ⊗ (V ⊓ L))`, literally the manuscript's recursion.
-/
import DegreeProfilesReview.PCClosure
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open MvPolynomial TensorProduct

namespace DegreeProfilesReview.PC

variable {σ : Type*} {K : Type*} [Field K]

noncomputable section

/-- The space freely spanned by the variables. -/
abbrev VarSpace (σ : Type*) (K : Type*) [Field K] := σ →₀ K

/-- Multiplication as a bilinear map `X × K[x] → K[x]`, `(e_i, f) ↦ X i * f`. -/
def varMul (σ : Type*) (K : Type*) [Field K] :
    VarSpace σ K →ₗ[K] MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  Finsupp.linearCombination K (fun i : σ => LinearMap.mulLeft K (X i : MvPolynomial σ K))

theorem varMul_single (i : σ) (f : MvPolynomial σ K) :
    varMul σ K (Finsupp.single i 1) f = X i * f := by
  simp [varMul]

/-- `μ : X ⊗ K[x] → K[x]`. -/
def mu (σ : Type*) (K : Type*) [Field K] :
    VarSpace σ K ⊗[K] MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  TensorProduct.lift (varMul σ K)

/-- Restricted multiplication `X ⊗ S → K[x]`. -/
def muRestrict (S : Submodule K (MvPolynomial σ K)) :
    VarSpace σ K ⊗[K] S →ₗ[K] MvPolynomial σ K :=
  mu σ K ∘ₗ LinearMap.lTensor (VarSpace σ K) S.subtype

theorem muRestrict_tmul (S : Submodule K (MvPolynomial σ K)) (c : VarSpace σ K) (f : S) :
    muRestrict S (c ⊗ₜ f) = varMul σ K c (f : MvPolynomial σ K) := by
  simp [muRestrict, mu]

/-- The image of restricted multiplication is `span {X i * f | f ∈ S}`. -/
theorem range_muRestrict (S : Submodule K (MvPolynomial σ K)) :
    LinearMap.range (muRestrict S) = mulStep S := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul c f =>
      rw [muRestrict_tmul, varMul, Finsupp.linearCombination_apply, Finsupp.sum,
        LinearMap.sum_apply]
      apply Submodule.sum_mem
      intro i _
      rw [LinearMap.smul_apply]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, f, f.2, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, f, hf, rfl⟩
    refine ⟨Finsupp.single i 1 ⊗ₜ ⟨f, hf⟩, ?_⟩
    rw [muRestrict_tmul, varMul_single]

/-- The closure step in the manuscript's form. -/
theorem step_eq_tensor (d : ℕ) (V : Submodule K (MvPolynomial σ K)) :
    step d V = V ⊔ LinearMap.range (muRestrict (V ⊓ lowDeg σ K d)) := by
  rw [range_muRestrict]
  rfl

end

end DegreeProfilesReview.PC
