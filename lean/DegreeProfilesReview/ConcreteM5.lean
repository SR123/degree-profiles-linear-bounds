/-
Stage 3, step 6: the input M5 (in its narrowed form `M5w`), PROVED for the actual
representation categories and the actual deletion functor.

Setting: `N = n + q`; `blk.A ≤ S_N` is a `p`-subgroup fixing the labels `< n` and acting
transitively on the deleted block `{n, …, N-1}` (`BlockGroup`); `K` has characteristic `p`; the
support bound satisfies `r < q` (the STRICT range).

* `Φhat blk : Rep K (S_N) ⥤ Rep K (S_n)` is the deletion functor `V ↦ im (V^A → V_A)` with the
  residual action of `S_n`.
* `fixedData` — for a basis system of support `≤ r < q`, the `A`-fixed points of `𝒰_N` are
  exactly `𝒰_n` (a fixed object whose support met the block would contain the whole block),
  and every other `A`-orbit has cardinality divisible by `p`.
* `δ'`      : `Φhat (K[𝒰_N]) ≅ K[𝒰_n]`;
* `δ'_mat`  : naturality for EVERY relabelling-invariant matrix: `Φhat` sends the map with
              matrix `a` at rank `N` to the map with the same matrix at rank `n`;
* `κ'`      : `Φhat (K[𝒰_N] ⊗ Y) ≅ K[𝒰_n] ⊗ Φhat Y` for every representation `Y`, naturally;
* `δ'_prod` : compatibility with `K[𝒰] ⊗ K[𝒱] = K[𝒰 × 𝒱]`.

`toM5w` assembles these into an `M5w`-structure for two `SchurClass`es `SN`, `Sn`, given only
that `Φhat` maps `SN` into `Sn` (`hΦ`).  No field of `M5w` is assumed.

Nothing here is assumed about exactness or monoidality of `Φhat`, and nothing about closure
of the classes under tensor products.
-/
import DegreeProfilesReview.DeletionFunctor
import DegreeProfilesReview.ConcreteM4
import DegreeProfilesReview.WeakInterface

open CategoryTheory MonoidalCategory TensorProduct

namespace DegreeProfilesReview.ConcreteM5

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Del
open DegreeProfilesReview.DelFunctor DegreeProfilesReview.ConcreteM4 DegreeProfilesReview.Deletion

/-! ### The group acting on the deleted block -/

/-- A `p`-subgroup of `S_{n+q}` that fixes every label `< n` and is transitive on the block
`{n, …, n+q-1}`.  (For the source theory one takes the regular elementary abelian group of
order `q = p^a`; only the three properties below are used here.) -/
structure BlockGroup (p n q : ℕ) where
  A : Subgroup (Sfin (n + q))
  fixes_low : ∀ a ∈ A, ∀ k, k < n → a.1 k = k
  trans : ∀ x y, n ≤ x → x < n + q → n ≤ y → y < n + q → ∃ a ∈ A, a.1 x = y
  pgroup : IsPGroup p A

variable {p n q : ℕ} (blk : BlockGroup p n q)

/-- `S_n ⊆ S_{n+q}`. -/
def incl (n q : ℕ) : Sfin n →* Sfin (n + q) := Subgroup.inclusion (Sfin_mono (Nat.le_add_right n q))

theorem incl_val (g : Sfin n) : (incl n q g).1 = g.1 := rfl

/-- `S_n` commutes with the block group. -/
theorem hcomm (g : Sfin n) (a : Sfin (n + q)) (ha : a ∈ blk.A) : incl n q g * a = a * incl n q g := by
  apply Subtype.ext
  apply Equiv.ext
  intro k
  show g.1 (a.1 k) = a.1 (g.1 k)
  by_cases hk : k < n
  · rw [blk.fixes_low a ha k hk, blk.fixes_low a ha _ (Sfin_lt g.2 hk)]
  · rw [not_lt] at hk
    have hak : n ≤ a.1 k := by
      by_contra h
      rw [not_le] at h
      have h1 := blk.fixes_low a ha _ h
      have h2 : a.1 k = k := a.1.injective h1
      omega
    rw [g.2 k hk, g.2 _ hak]

/-! ### Fixed points of bounded basis systems -/

section Fixed

variable {K : Type} [Field K] [Fact p.Prime] [CharP K p] {r : ℕ} (hrq : r < q)
  {𝒰 : BasisSystem} (hU : 𝒰.Bounded r)

omit [Fact p.Prime] in
include hrq hU in
/-- An object of rank `N` that is not of rank `n` is moved by the block group. -/
theorem exists_moves (x : 𝒰.Rk (n + q))
    (hx : x ∉ Set.range (inclRk 𝒰 (Nat.le_add_right n q))) : ∃ a ∈ blk.A, a • x ≠ x := by
  by_contra hcon
  push_neg at hcon
  rw [mem_range_inclRk] at hx
  obtain ⟨k, hk, hkn⟩ := Finset.not_subset.mp hx
  rw [Finset.mem_range, not_lt] at hkn
  have hkN : k < n + q := Finset.mem_range.mp (𝒰.supp_up _ x hk)
  -- the whole block lies in the support
  have hsub : Finset.Ico n (n + q) ⊆ 𝒰.supp (𝒰.up _ x) := by
    intro y hy
    rw [Finset.mem_Ico] at hy
    obtain ⟨a, ha, hay⟩ := blk.trans k y hkn hkN hy.1 hy.2
    have h1 : 𝒰.supp (𝒰.up _ (a • x)) = (𝒰.supp (𝒰.up _ x)).image a.1 := by
      rw [up_smul, 𝒰.supp_smul]
    rw [hcon a ha] at h1
    rw [h1, ← hay]
    exact Finset.mem_image_of_mem _ hk
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have := hU (𝒰.up _ x)
  omega

/-- **The fixed points of `𝒰_N` under the block group are `𝒰_n`**, and the other orbits have
cardinality zero in `K`. -/
noncomputable def fixedData : FixedData K blk.A (𝒰.Rk (n + q)) (𝒰.Rk n) where
  j := inclRk 𝒰 (Nat.le_add_right n q)
  inj := inclRk_injective 𝒰 _
  fix := fun f a ha => by
    apply 𝒰.up_inj
    rw [up_smul, up_inclRk]
    apply 𝒰.fixed
    intro x hx
    exact blk.fixes_low a ha x (Finset.mem_range.mp (𝒰.supp_up n f hx))
  orb := fun x hx =>
    orbit_card_eq_zero blk.A blk.pgroup x (exists_moves blk hrq hU x hx)

theorem fixedData_j : (fixedData (K := K) blk hrq hU).j = inclRk 𝒰 (Nat.le_add_right n q) := rfl

end Fixed

/-! ### The deletion functor and the M5 identifications -/

section Functor

variable (K : Type) [Field K]

/-- **The deletion functor** `Rep K (S_{n+q}) ⥤ Rep K (S_n)`. -/
noncomputable def Φhat : Rep K (Sfin (n + q)) ⥤ Rep K (Sfin n) :=
  delFunctor blk.A (incl n q) (fun g a ha => hcomm blk g a ha)

variable {K} [Fact p.Prime] [CharP K p] {r : ℕ} (hrq : r < q)

theorem incl_smul {𝒰 : BasisSystem} (g : Sfin n) (f : 𝒰.Rk n) :
    inclRk 𝒰 (Nat.le_add_right n q) (g • f) = incl n q g • inclRk 𝒰 (Nat.le_add_right n q) f :=
  inclRk_smul 𝒰 _ g f

/-- `Φhat (K[𝒰_N]) ≅ K[𝒰_n]`. -/
noncomputable def δ' {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) :
    (Φhat blk K).obj (permRep K 𝒰 (n + q)) ≅ permRep K 𝒰 n :=
  delPermIso (fixedData blk hrq hU) (fun g f => incl_smul g f)

/-- `Φhat (K[𝒰_N] ⊗ Y) ≅ K[𝒰_n] ⊗ Φhat Y`. -/
noncomputable def κ' {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) (Y : Rep K (Sfin (n + q))) :
    (Φhat blk K).obj (permRep K 𝒰 (n + q) ⊗ Y) ≅ permRep K 𝒰 n ⊗ (Φhat blk K).obj Y :=
  delTensIso (fixedData blk hrq hU) (fun g f => incl_smul g f) Y

theorem κ'_nat {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) {Y Y' : Rep K (Sfin (n + q))}
    (f : Y ⟶ Y') :
    (Φhat blk K).map (permRep K 𝒰 (n + q) ◁ f) ≫ (κ' blk hrq hU Y').hom =
      (κ' blk hrq hU Y).hom ≫ (permRep K 𝒰 n ◁ (Φhat blk K).map f) :=
  delTensIso_natural (fixedData blk hrq hU) (fun g f => incl_smul g f) f

/-- **Naturality for invariant matrices.** -/
theorem δ'_mat {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (a : InvMatrix K 𝒰 𝒱) :
    (Φhat blk K).map (matHom a (n + q)) ≫ (δ' blk hrq hV).hom =
      (δ' blk hrq hU).hom ≫ matHom a n := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  refine permDelEquiv_natural (fixedData blk hrq hU) (fixedData blk hrq hV) (a.realise (n + q))
    (hom_aequivariant blk.A (matHom a (n + q))) (a.realise n) ?_
  intro f f'
  rw [InvMatrix.realise_single_apply, InvMatrix.realise_single_apply, fixedData_j, fixedData_j,
    up_inclRk, up_inclRk]

open Classical in
/-- Product compatibility, in the direction in which all maps are explicit on basis vectors:
`e_(x,y) ↦ e_x ⊗ e_y ↦ e_x ⊗ [e_y] ↦ [e_x ⊗ e_y]` equals `e_(x,y) ↦ [e_(x,y)] ↦ [e_x ⊗ e_y]`. -/
theorem δ'_prod_inv {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (hUV : (𝒰.prod 𝒱).Bounded r) :
    (permProdIso (K := K) 𝒰 𝒱 n).inv ≫ (permRep K 𝒰 n ◁ (δ' blk hrq hV).inv) ≫
        (κ' blk hrq hU (permRep K 𝒱 (n + q))).inv =
      (δ' blk hrq hUV).inv ≫ (Φhat blk K).map (permProdIso (K := K) 𝒰 𝒱 (n + q)).inv := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  rintro ⟨x, y⟩
  apply LinearMap.ext_ring
  show (tensDelEquiv (Representation.ofMulAction K (Sfin (n + q)) (𝒱.Rk (n + q)))
      (fixedData blk hrq hU)).symm
      (LinearMap.lTensor (𝒰.Rk n →₀ K) (permDelEquiv (fixedData blk hrq hV)).symm.toLinearMap
        ((finsuppTensorFinsupp' K (𝒰.Rk n) (𝒱.Rk n)).symm (Finsupp.single (x, y) 1))) =
    delMap (finsuppTensorFinsupp' K (𝒰.Rk (n + q)) (𝒱.Rk (n + q))).symm.toLinearMap
      (hom_aequivariant blk.A (permProdIso (K := K) 𝒰 𝒱 (n + q)).inv)
      ((permDelEquiv (fixedData blk hrq hUV)).symm (Finsupp.single (x, y) 1))
  rw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, permDelEquiv_symm_single, tensDelEquiv_symm_tmul,
    permDelEquiv_symm_single, delMap_delMk]
  apply Subtype.ext
  rw [coe_delMk, coe_delMk, LinearEquiv.coe_coe, fixedData_j, fixedData_j, fixedData_j,
    inclRk_prod]
  congr 1
  exact (finsuppTensorFinsupp'_symm_single_eq_single_one_tmul K (𝒰.Rk (n + q))
    (𝒱.Rk (n + q)) (_, _) 1).symm

/-- **Compatibility with products.** -/
theorem δ'_prod {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (hUV : (𝒰.prod 𝒱).Bounded r) :
    (Φhat blk K).map (permProdIso (K := K) 𝒰 𝒱 (n + q)).hom ≫ (δ' blk hrq hUV).hom =
      (κ' blk hrq hU (permRep K 𝒱 (n + q))).hom ≫ (permRep K 𝒰 n ◁ (δ' blk hrq hV).hom) ≫
        (permProdIso (K := K) 𝒰 𝒱 n).hom := by
  have h := δ'_prod_inv (K := K) blk hrq hU hV hUV
  let L : permRep K (𝒰.prod 𝒱) n ≅ (Φhat blk K).obj (permRep K 𝒰 (n + q) ⊗ permRep K 𝒱 (n + q)) :=
    (permProdIso (K := K) 𝒰 𝒱 n).symm ≪≫ whiskerLeftIso (permRep K 𝒰 n) (δ' blk hrq hV).symm ≪≫
      (κ' blk hrq hU (permRep K 𝒱 (n + q))).symm
  let R : permRep K (𝒰.prod 𝒱) n ≅ (Φhat blk K).obj (permRep K 𝒰 (n + q) ⊗ permRep K 𝒱 (n + q)) :=
    (δ' blk hrq hUV).symm ≪≫ ((Φhat blk K).mapIso (permProdIso (K := K) 𝒰 𝒱 (n + q))).symm
  have hLR : L = R := Iso.ext h
  have hinv : L.inv = R.inv := by rw [hLR]
  simpa [L, R] using hinv.symm

end Functor

/-! ### Assembly: the narrowed M5 for two Schur classes -/

section Assemble

variable {K : Type} [Field K] [Fact p.Prime] [CharP K p] {r : ℕ} (hrq : r < q)
  (SN : SchurClass K r (n + q)) (Sn : SchurClass K r n)
  (hΦ : ∀ X, SN.P X → Sn.P ((Φhat blk K).obj X))

/-- The deletion functor restricted to the two classes. -/
noncomputable def Φ : SN.B ⥤ Sn.B :=
  Sn.P.lift (SN.P.ι ⋙ Φhat blk K) fun X => hΦ X.obj X.property

/-- **M5 (narrowed), constructed.**  Every field is a theorem of this development. -/
noncomputable def toM5w : M5w.{0, 0, 0, 1, 1, 1} SN.toM4 Sn.toM4 (Φ blk SN Sn hΦ) where
  𝒯 := Rep K (Sfin n)
  J := 𝟭 _
  Φhat := Φhat blk K
  γ := Iso.refl _
  δ := fun _ h => Sn.P.isoMk (δ' blk hrq h)
  δ_mat := fun {_ _} hU hV a => δ'_mat blk hrq hU hV a
  κ := fun {_} hU Y => κ' blk hrq hU Y
  κ_nat := fun {_} hU {_ _} f => κ'_nat blk hrq hU f
  δ_prod := fun {𝒰 𝒱} hU hV hUV => by
    have h := δ'_prod (K := K) blk hrq hU hV hUV
    simp only [Iso.refl_hom, NatTrans.id_app, Functor.id_map, Category.id_comp,
      Functor.LaxMonoidal.id_μ, Functor.id_obj]
    exact h

end Assemble

end DegreeProfilesReview.ConcreteM5
