/-
Stage 2, step 5b: the compatible maps.

For a template `T`, a degree `d ≥ 1`, a universe size `t` and an `M4`-structure `P` on a
category `B` (support bound `r = k d + s`):

* `catDatum`   — the PC datum INSIDE `B`: the five permutation modules, the four morphisms
                 given by the invariant matrices, and `T s = (X ⊗ S ⟶ X ⊗ L)` from
                 `M4.tens`.
* `ωCompat`    — the underlying-space functor `ω` carries `catDatum` to the concrete datum of
                 actual polynomial spaces (`ConcreteDatum.lean`).  All five comparison
                 isomorphisms and all five compatibilities are CONSTRUCTED/PROVED here.
* `ΦCompat`    — for an `M5`-structure, `Φ` carries the rank-`N` datum to the rank-`n` datum.
* `pc_stage_iff`, `ns_iff` — hence categorical membership of the constant at stage `j`
                 (resp. in the image of the certificate map) is membership of `1` in the
                 `j`-th stage of the actual closure (resp. in the actual NS span).

No field of `PCCompat` is assumed.
-/
import DegreeProfilesReview.TemplateMatrices
import DegreeProfilesReview.DeletionInterface

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits MonoidalCategory MvPolynomial TensorProduct

namespace DegreeProfilesReview.Deletion.M4

open DegreeProfilesReview.Uniform

variable {K : Type} [Field K] {r t : ℕ} {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (P : M4.{v₂, v₃, u₂, u₃} K r t B)

/-- A square of actual linear maps gives a square in `ModuleCat` for the underlying map of
`mat a`. -/
theorem sq_of_realise {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (a : InvMatrix K 𝒰 𝒱) {X' Y' : Type} [AddCommGroup X'] [Module K X'] [AddCommGroup Y']
    [Module K Y'] (eU : (𝒰.Rk t →₀ K) ≃ₗ[K] X') (eV : (𝒱.Rk t →₀ K) ≃ₗ[K] Y')
    (f : X' →ₗ[K] Y') (h : eV.toLinearMap ∘ₗ a.realise t = f ∘ₗ eU.toLinearMap) :
    P.ω.map (P.mat hU hV a) ≫ (P.basis 𝒱 hV ≪≫ eV.toModuleIso).hom =
      (P.basis 𝒰 hU ≪≫ eU.toModuleIso).hom ≫ ModuleCat.ofHom f := by
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc, P.mat_spec, Category.assoc,
    Category.assoc]
  congr 1
  show ModuleCat.ofHom (a.realise t) ≫ ModuleCat.ofHom eV.toLinearMap =
    ModuleCat.ofHom eU.toLinearMap ≫ ModuleCat.ofHom f
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, h]

end DegreeProfilesReview.Deletion.M4

namespace DegreeProfilesReview.Uniform.Template

open DegreeProfilesReview.Deletion DegreeProfilesReview.Transport DegreeProfilesReview.Concrete
open DegreeProfilesReview.PC BasisSystem

variable {K : Type} [Field K] (T : Template K) {d : ℕ} (hd : 1 ≤ d)

section Rank

variable {t : ℕ} {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (P : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) t B)

/-- The PC datum inside `B`. -/
noncomputable def catDatum : PCDatum B where
  W := P.perm (T.Var.mon d) (T.mon_bounded' d)
  L := P.perm (T.Var.mon (d - 1)) (T.low_bounded d)
  M := P.perm (T.Var.prod (T.Var.mon (d - 1))) (T.mul_bounded d hd)
  U := P.perm BasisSystem.unit (BasisSystem.unit_bounded _)
  V₀ := P.perm (T.axSys d) (T.ax_bounded' d)
  ℓ := P.mat _ _ (T.inclM d)
  μ := P.mat _ _ (T.mulM d)
  v₀ := P.mat _ _ (T.axM d)
  c := P.mat _ _ (T.constM d)
  T := fun {_} s _ =>
    Over.mk (P.tens (T.var_bounded' d hd) (T.low_bounded d) (T.mul_bounded d hd) s)

/-- The concrete datum of actual polynomial spaces at size `t`. -/
noncomputable def concDatum (t : ℕ) : PCDatum (ModuleCat.{0} K) :=
  Concrete.datum (T.Var.Rk t) K hd (T.axMap d t)

/-- The basis of `X ⊗ P_{≤ d-1}` indexed by pairs (variable, monomial). -/
noncomputable def mulBasis (t : ℕ) :
    ((T.Var.prod (T.Var.mon (d - 1))).Rk t →₀ K) ≃ₗ[K]
      VarSpace (T.Var.Rk t) K ⊗[K] Pd (T.Var.Rk t) K (d - 1) :=
  (finsuppTensorFinsupp' K (T.Var.Rk t) {m : T.Var.Rk t →₀ ℕ // mdeg m ≤ d - 1}).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl K _) (monBasis (T.Var.Rk t) K (d - 1))

theorem mulBasis_coe (t : ℕ) :
    (T.mulBasis (d := d) t).toLinearMap =
      LinearMap.lTensor (VarSpace (T.Var.Rk t) K)
          (monBasis (T.Var.Rk t) K (d - 1)).toLinearMap ∘ₗ
        (finsuppTensorFinsupp' K (T.Var.Rk t)
          {m : T.Var.Rk t →₀ ℕ // mdeg m ≤ d - 1}).symm.toLinearMap := rfl

theorem mulBasis_hom (t : ℕ) :
    (T.mulBasis (d := d) t).toModuleIso.hom =
      (prodBasis K (T.Var.Rk t) ((T.Var.mon (d - 1)).Rk t)).inv ≫
        (ModuleCat.of K (T.Var.Rk t →₀ K) ◁
          (monBasis (T.Var.Rk t) K (d - 1)).toModuleIso.hom) := rfl

/-- **The underlying-space functor carries the categorical datum to the actual one.** -/
noncomputable def ωCompat : PCCompat P.ω (T.catDatum hd P) (T.concDatum hd t) where
  αW := P.basis _ _ ≪≫ (monBasis (T.Var.Rk t) K d).toModuleIso
  αL := P.basis _ _ ≪≫ (monBasis (T.Var.Rk t) K (d - 1)).toModuleIso
  αM := P.basis _ _ ≪≫ (T.mulBasis t).toModuleIso
  αU := P.basis _ _ ≪≫ (unitEquiv (K := K) t).toModuleIso
  αV₀ := P.basis _ _ ≪≫ (LinearEquiv.refl K _).toModuleIso
  hℓ := P.sq_of_realise _ _ (T.inclM d) _ _ _ (T.inclM_realise d t)
  hμ := P.sq_of_realise _ _ (T.mulM d) _ _ _ (by
    rw [mulBasis_coe]; exact T.mulM_realise d t hd)
  hv₀ := P.sq_of_realise _ _ (T.axM d) _ _ _ (T.axM_realise d t)
  hc := P.sq_of_realise _ _ (T.constM d) _ _ _ (T.constM_realise d t)
  hT := fun {S} s _ {S'} s' _ e hs => by
    obtain ⟨eT, heT⟩ := P.tens_ω_spec (T.var_bounded' d hd) (T.low_bounded d)
      (T.mul_bounded d hd) s (monBasis (T.Var.Rk t) K (d - 1)).toModuleIso s' e hs
    refine ⟨eT, ?_⟩
    show P.ω.map (P.tens (T.var_bounded' d hd) (T.low_bounded d) (T.mul_bounded d hd) s) ≫
      (P.basis _ _).hom ≫ (T.mulBasis (d := d) t).toModuleIso.hom =
        eT.hom ≫ (ModuleCat.of K (T.Var.Rk t →₀ K) ◁ s')
    rw [mulBasis_hom]
    exact heT

/-- **Bridge, PC.**  Beyond `n₀`: the constant lies in the `j`-th categorical stage iff `1`
lies in the `j`-th stage of the actual closure of the instance at size `t`. -/
theorem pc_stage_iff (ht : T.n0 ≤ t) (j : ℕ) :
    (T.catDatum hd P).ConstMem j ↔
      (1 : MvPolynomial (T.Var.Rk t) K) ∈ PC.V (T.inst t) d j := by
  have h1 := const_mem_iff P.ω (T.ωCompat hd P) j
  have h2 := Concrete.constMem_iff hd (T.axMap d t) (T.inst t) (T.range_axMap d ht) j
  exact h1.trans h2

/-- **Bridge, NS.**  Beyond `n₀`: the constant maps to zero in the cokernel of the categorical
certificate map iff `1` lies in the actual NS span of the instance at size `t`. -/
theorem ns_iff (ht : T.n0 ≤ t) :
    P.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (T.constM d) ≫
        cokernel.π (P.mat (T.cert_bounded d) (T.mon_bounded' d) (T.certM d)) = 0 ↔
      (1 : MvPolynomial (T.Var.Rk t) K) ∈ NS.NSspan (T.inst t) d := by
  have hA := P.sq_of_realise (T.cert_bounded d) (T.mon_bounded' d) (T.certM d)
    (LinearEquiv.refl K _) (monBasis (T.Var.Rk t) K d) (T.certMap d t) (T.certM_realise d t)
  have hj := P.sq_of_realise (BasisSystem.unit_bounded _) (T.mon_bounded' d) (T.constM d)
    (unitEquiv (K := K) t) (monBasis (T.Var.Rk t) K d) (constMap (T.Var.Rk t) K d)
    (T.constM_realise d t)
  have h1 := image_membership_iff P.ω
    (P.mat (T.cert_bounded d) (T.mon_bounded' d) (T.certM d))
    (P.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (T.constM d))
    (ModuleCat.ofHom (T.certMap d t)) (ModuleCat.ofHom (constMap (T.Var.Rk t) K d))
    _ _ _ hA hj
  have h2 := Concrete.nsMem_iff (T.inst t) (T.certMap d t) (T.range_certMap d ht)
  exact h1.trans h2

end Rank

section Deletion

variable {N n : ℕ}
  {BN : Type u₂} [Category.{v₂} BN] [Abelian BN] {Bn : Type u₂} [Category.{v₂} Bn] [Abelian Bn]
  {PN : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) N BN}
  {Pn : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) n Bn} {Φ : BN ⥤ Bn}
  (m5 : M5.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ)

/-- **`Φ` carries the rank-`N` datum to the rank-`n` datum.** -/
noncomputable def ΦCompat : PCCompat Φ (T.catDatum hd PN) (T.catDatum hd Pn) where
  αW := m5.δ _ _
  αL := m5.δ _ _
  αM := m5.δ _ _
  αU := m5.δ _ _
  αV₀ := m5.δ _ _
  hℓ := m5.δ_mat _ _ _
  hμ := m5.δ_mat _ _ _
  hv₀ := m5.δ_mat _ _ _
  hc := m5.δ_mat _ _ _
  hT := fun {_} s _ {_} s' _ e hs =>
    m5.tens_Φ_spec (T.var_bounded' d hd) (T.low_bounded d) (T.mul_bounded d hd) s s' e hs

end Deletion

end DegreeProfilesReview.Uniform.Template
