/-
Stage 5, step 6: the narrowed input M5 (`M5w`), PROVED for the actual representation categories
and the SHIFTED CYCLIC functor.  This is the analogue of `ConcreteM5.lean` for the functor that
replaces `V ↦ im (V^A → V_A)` (which Stage 4 showed cannot be an equivalence on the intended
classes once `r ≥ p`).

Setting: `N = n + q`, `q = p^a`; `A = (ℤ/p)^a` acts regularly on the block `{n, …, N-1}` and
trivially elsewhere (`blockφ`, the homomorphism underlying `elemAbBlock`); `σ_1, …, σ_a` are the
images of the standard basis; `K` has characteristic `p`; `c : Fin a → K` is generic (linearly
independent over the prime field); the support bound satisfies `r < q` (the STRICT range).

* `Ψhat p a n c : Rep K (S_N) ⥤ Rep K (S_n)`,
      `V ↦ ker z / (ker z ∩ range z)`,   `z = ∑ c_i (σ_i - 1)`,
  with the residual action of `S_n`.
* `shiftFixedData` — the points of `𝒰_N` fixed by `A` are exactly `𝒰_n`, and the remaining part
  of `K[𝒰_N] ⊗ Y` is acyclic for `z` for EVERY `Y` (from `ShiftedElemAb.nonfixedAcyclic`; no
  freeness of the non-fixed orbits is used).
* `δ'`      : `Ψhat (K[𝒰_N]) ≅ K[𝒰_n]`;
* `δ'_mat`  : naturality for EVERY relabelling-invariant matrix;
* `κ'`      : `Ψhat (K[𝒰_N] ⊗ Y) ≅ K[𝒰_n] ⊗ Ψhat Y` for every representation `Y`, naturally;
* `δ'_prod` : compatibility with `K[𝒰] ⊗ K[𝒱] = K[𝒰 × 𝒱]`.

`toM5w` assembles these into an `M5w`-structure for two `SchurClass`es `SN`, `Sn`, given only
that `Ψhat` maps `SN` into `Sn`.  No field of `M5w` is assumed.  Nothing is assumed about
exactness or monoidality of `Ψhat`.
-/
import DegreeProfilesReview.ShiftedFunctor
import DegreeProfilesReview.ShiftedElemAb
import DegreeProfilesReview.BlockGroupExample

open CategoryTheory MonoidalCategory TensorProduct

namespace DegreeProfilesReview.ShiftedM5

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Del
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor
open DegreeProfilesReview.ConcreteM4 DegreeProfilesReview.ConcreteM5 DegreeProfilesReview.Deletion

/-! ### The block group as a homomorphism, and its generators -/

section Block

variable (p a n : ℕ) [Fact p.Prime]

/-- The homomorphism `(ℤ/p)^a → S_{n+p^a}` underlying `elemAbBlock`. -/
noncomputable def blockφ : ElemAb p a →* Sfin (n + p ^ a) :=
  (blockHom p a n).codRestrict (Sfin (n + p ^ a)) (blockHom_mem_Sfin p a n)

theorem blockφ_mem (v : ElemAb p a) : blockφ p a n v ∈ (elemAbBlock p a n).A :=
  Subgroup.mem_subgroupOf.mpr ⟨v, rfl⟩

theorem exists_of_mem {g : Sfin (n + p ^ a)} (hg : g ∈ (elemAbBlock p a n).A) :
    ∃ v : ElemAb p a, blockφ p a n v = g := by
  obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hg
  exact ⟨v, Subtype.ext hv⟩

/-- The generators `σ_1, …, σ_a`. -/
noncomputable def σgen : Fin a → Sfin (n + p ^ a) := gen (blockφ p a n)

theorem σgen_mem (k : Fin a) : σgen p a n k ∈ (elemAbBlock p a n).A := blockφ_mem p a n _

/-- `S_n` commutes with the generators. -/
theorem hcommΨ (g : Sfin n) (k : Fin a) :
    incl n (p ^ a) g * σgen p a n k = σgen p a n k * incl n (p ^ a) g :=
  hcomm (elemAbBlock p a n) g _ (σgen_mem p a n k)

end Block

/-! ### Fixed points of bounded basis systems -/

section Fixed

variable {p a n : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] {c : Fin a → K}
  (hc : Generic p c) {r : ℕ} (hrq : r < p ^ a) {𝒰 : BasisSystem} (hU : 𝒰.Bounded r)

/-- **The fixed points of `𝒰_N` are `𝒰_n`, and the rest is acyclic for `z`.** -/
noncomputable def shiftFixedData :
    ShiftFixedData (σgen p a n) c (𝒰.Rk (n + p ^ a)) (𝒰.Rk n) where
  j := inclRk 𝒰 (Nat.le_add_right n (p ^ a))
  inj := inclRk_injective 𝒰 _
  fix := fun f k => (fixedData (K := K) (elemAbBlock p a n) hrq hU).fix f _ (σgen_mem p a n k)
  acyc := fun Y _ _ σ => by
    apply nonfixedAcyclic (blockφ p a n) σ _ hc
    intro x hx
    obtain ⟨g, hg, hne⟩ := exists_moves (elemAbBlock p a n) hrq hU x hx
    obtain ⟨v, rfl⟩ := exists_of_mem p a n hg
    exact ⟨Multiplicative.toAdd v, hne⟩

theorem shiftFixedData_j :
    (shiftFixedData (n := n) hc hrq hU).j = inclRk 𝒰 (Nat.le_add_right n (p ^ a)) := rfl

end Fixed

/-! ### The shifted cyclic functor and the M5 identifications -/

section Functor

variable (p a n : ℕ) [Fact p.Prime] {K : Type} [Field K] (c : Fin a → K)

/-- **The shifted cyclic functor** `Rep K (S_{n+p^a}) ⥤ Rep K (S_n)`. -/
noncomputable def Ψhat : Rep K (Sfin (n + p ^ a)) ⥤ Rep K (Sfin n) :=
  scFunctor (σgen p a n) c (incl n (p ^ a)) (hcommΨ p a n)

variable {p a n c} [CharP K p] (hc : Generic p c) {r : ℕ} (hrq : r < p ^ a)

/-- `Ψhat (K[𝒰_N]) ≅ K[𝒰_n]`. -/
noncomputable def δ' {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) :
    (Ψhat p a n c).obj (permRep K 𝒰 (n + p ^ a)) ≅ permRep K 𝒰 n :=
  scPermIso (shiftFixedData hc hrq hU) (fun g f => incl_smul g f)

/-- `Ψhat (K[𝒰_N] ⊗ Y) ≅ K[𝒰_n] ⊗ Ψhat Y`. -/
noncomputable def κ' {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) (Y : Rep K (Sfin (n + p ^ a))) :
    (Ψhat p a n c).obj (permRep K 𝒰 (n + p ^ a) ⊗ Y) ≅ permRep K 𝒰 n ⊗ (Ψhat p a n c).obj Y :=
  scTensIso (shiftFixedData hc hrq hU) (fun g f => incl_smul g f) Y

theorem κ'_nat {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) {Y Y' : Rep K (Sfin (n + p ^ a))}
    (f : Y ⟶ Y') :
    (Ψhat p a n c).map (permRep K 𝒰 (n + p ^ a) ◁ f) ≫ (κ' hc hrq hU Y').hom =
      (κ' hc hrq hU Y).hom ≫ (permRep K 𝒰 n ◁ (Ψhat p a n c).map f) :=
  scTensIso_natural (shiftFixedData hc hrq hU) (fun g f => incl_smul g f) f

/-- **Naturality for invariant matrices.** -/
theorem δ'_mat {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (m : InvMatrix K 𝒰 𝒱) :
    (Ψhat p a n c).map (matHom m (n + p ^ a)) ≫ (δ' hc hrq hV).hom =
      (δ' hc hrq hU).hom ≫ matHom m n := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  refine permScEquiv_natural (shiftFixedData hc hrq hU) (shiftFixedData hc hrq hV)
    (m.realise (n + p ^ a)) (hom_sequivariant (σgen p a n) (matHom m (n + p ^ a)))
    (m.realise n) ?_
  intro f f'
  rw [InvMatrix.realise_single_apply, InvMatrix.realise_single_apply, shiftFixedData_j,
    shiftFixedData_j, up_inclRk, up_inclRk]

open Classical in
/-- Product compatibility, in the direction in which all maps are explicit on basis vectors:
`e_(x,y) ↦ e_x ⊗ e_y ↦ e_x ⊗ [e_y] ↦ [e_x ⊗ e_y]` equals `e_(x,y) ↦ [e_(x,y)] ↦ [e_x ⊗ e_y]`. -/
theorem δ'_prod_inv {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (hUV : (𝒰.prod 𝒱).Bounded r) :
    (permProdIso (K := K) 𝒰 𝒱 n).inv ≫ (permRep K 𝒰 n ◁ (δ' hc hrq hV).inv) ≫
        (κ' hc hrq hU (permRep K 𝒱 (n + p ^ a))).inv =
      (δ' hc hrq hUV).inv ≫ (Ψhat p a n c).map (permProdIso (K := K) 𝒰 𝒱 (n + p ^ a)).inv := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  rintro ⟨x, y⟩
  apply LinearMap.ext_ring
  show (tensScEquiv (Representation.ofMulAction K (Sfin (n + p ^ a)) (𝒱.Rk (n + p ^ a)))
      (shiftFixedData hc hrq hU)).symm
      (LinearMap.lTensor (𝒰.Rk n →₀ K) (permScEquiv (shiftFixedData hc hrq hV)).symm.toLinearMap
        ((finsuppTensorFinsupp' K (𝒰.Rk n) (𝒱.Rk n)).symm (Finsupp.single (x, y) 1))) =
    scMap c (finsuppTensorFinsupp' K (𝒰.Rk (n + p ^ a)) (𝒱.Rk (n + p ^ a))).symm.toLinearMap
      (hom_sequivariant (σgen p a n) (permProdIso (K := K) 𝒰 𝒱 (n + p ^ a)).inv)
      ((permScEquiv (shiftFixedData hc hrq hUV)).symm (Finsupp.single (x, y) 1))
  rw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, permScEquiv_symm_single, tensScEquiv_symm_tmul,
    permScEquiv_symm_single, scMap_scMk]
  apply scMk_congr
  rw [LinearEquiv.coe_coe, shiftFixedData_j, shiftFixedData_j, shiftFixedData_j, inclRk_prod]
  exact (finsuppTensorFinsupp'_symm_single_eq_single_one_tmul K (𝒰.Rk (n + p ^ a))
    (𝒱.Rk (n + p ^ a)) (_, _) 1).symm

/-- **Compatibility with products.** -/
theorem δ'_prod {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (hUV : (𝒰.prod 𝒱).Bounded r) :
    (Ψhat p a n c).map (permProdIso (K := K) 𝒰 𝒱 (n + p ^ a)).hom ≫ (δ' hc hrq hUV).hom =
      (κ' hc hrq hU (permRep K 𝒱 (n + p ^ a))).hom ≫ (permRep K 𝒰 n ◁ (δ' hc hrq hV).hom) ≫
        (permProdIso (K := K) 𝒰 𝒱 n).hom := by
  have h := δ'_prod_inv (K := K) (n := n) hc hrq hU hV hUV
  let L : permRep K (𝒰.prod 𝒱) n ≅
      (Ψhat p a n c).obj (permRep K 𝒰 (n + p ^ a) ⊗ permRep K 𝒱 (n + p ^ a)) :=
    (permProdIso (K := K) 𝒰 𝒱 n).symm ≪≫ whiskerLeftIso (permRep K 𝒰 n) (δ' hc hrq hV).symm ≪≫
      (κ' hc hrq hU (permRep K 𝒱 (n + p ^ a))).symm
  let R : permRep K (𝒰.prod 𝒱) n ≅
      (Ψhat p a n c).obj (permRep K 𝒰 (n + p ^ a) ⊗ permRep K 𝒱 (n + p ^ a)) :=
    (δ' hc hrq hUV).symm ≪≫ ((Ψhat p a n c).mapIso (permProdIso (K := K) 𝒰 𝒱 (n + p ^ a))).symm
  have hLR : L = R := Iso.ext h
  have hinv : L.inv = R.inv := by rw [hLR]
  simpa [L, R] using hinv.symm

end Functor

/-! ### Assembly: the narrowed M5 for two Schur classes -/

section Assemble

variable {p a n : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] {c : Fin a → K}
  (hc : Generic p c) {r : ℕ} (hrq : r < p ^ a)
  (SN : SchurClass K r (n + p ^ a)) (Sn : SchurClass K r n)
  (hΨ : ∀ X, SN.P X → Sn.P ((Ψhat p a n c).obj X))

/-- The shifted cyclic functor restricted to the two classes. -/
noncomputable def Ψ : SN.B ⥤ Sn.B :=
  Sn.P.lift (SN.P.ι ⋙ Ψhat p a n c) fun X => hΨ X.obj X.property

/-- **M5 (narrowed), constructed for the shifted cyclic functor.**  Every field is a theorem of
this development. -/
noncomputable def toM5w : M5w.{0, 0, 0, 1, 1, 1} SN.toM4 Sn.toM4 (Ψ SN Sn hΨ) where
  𝒯 := Rep K (Sfin n)
  J := 𝟭 _
  Φhat := Ψhat p a n c
  γ := Iso.refl _
  δ := fun _ h => Sn.P.isoMk (δ' hc hrq h)
  δ_mat := fun {_ _} hU hV m => δ'_mat hc hrq hU hV m
  κ := fun {_} hU Y => κ' hc hrq hU Y
  κ_nat := fun {_} hU {_ _} f => κ'_nat hc hrq hU f
  δ_prod := fun {𝒰 𝒱} hU hV hUV => by
    have h := δ'_prod (K := K) (n := n) hc hrq hU hV hUV
    simp only [Iso.refl_hom, NatTrans.id_app, Functor.id_map, Category.id_comp,
      Functor.LaxMonoidal.id_μ, Functor.id_obj]
    exact h

end Assemble

end DegreeProfilesReview.ShiftedM5
