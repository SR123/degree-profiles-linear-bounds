/-
Stage 3, step 1: the concrete representation layer.

* `Sfin t`      — the symmetric group `S_t`, as the subgroup of permutations of `ℕ` fixing every
                  label `≥ t`.
* the action of `S_t` on the rank-`t` part `𝒰.Rk t` of a basis system (transported from the
  relabelling action on objects), and `permRep K 𝒰 t = K[𝒰_t]` as an object of `Rep K (S_t)`.
* `matHom a t`  — a relabelling-invariant matrix, restricted to rank `t`, IS `S_t`-equivariant:
                  a morphism `K[𝒰_t] ⟶ K[𝒱_t]` of representations whose underlying linear map
                  is the Stage 2 map `a.realise t`.
* `permProdIso` — `K[𝒰_t] ⊗ K[𝒱_t] ≅ K[(𝒰 × 𝒱)_t]` as representations, with underlying map
                  `e_u ⊗ e_v ↦ e_(u,v)`.
* `inclRk`      — the inclusion `𝒰_n ⊆ 𝒰_N` for `n ≤ N`, and its image.

Everything here is proved; there is no external hypothesis.
-/
import DegreeProfilesReview.BasisSystems
import Mathlib.RepresentationTheory.Rep
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import DegreeProfilesReview.DeletionInterface

open CategoryTheory MonoidalCategory

namespace DegreeProfilesReview.SymRep

open DegreeProfilesReview.Uniform

/-! ### The groups `S_t` -/

/-- `S_t` as a group of permutations of `ℕ`: those fixing every label `≥ t`. -/
def Sfin (t : ℕ) : Subgroup (Equiv.Perm ℕ) where
  carrier := {g | ∀ i, t ≤ i → g i = i}
  mul_mem' := fun {a b} ha hb i hi => by
    rw [Equiv.Perm.mul_apply, hb i hi, ha i hi]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha i hi => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

theorem mem_Sfin {t : ℕ} {g : Equiv.Perm ℕ} : g ∈ Sfin t ↔ ∀ i, t ≤ i → g i = i := Iff.rfl

theorem Sfin_mono {n N : ℕ} (h : n ≤ N) : Sfin n ≤ Sfin N :=
  fun _ hg i hi => hg i (le_trans h hi)

/-- An element of `S_t` maps `{0,…,t-1}` into itself. -/
theorem Sfin_lt {t : ℕ} {g : Equiv.Perm ℕ} (hg : g ∈ Sfin t) {i : ℕ} (hi : i < t) : g i < t := by
  by_contra h
  rw [not_lt] at h
  have h1 : g (g i) = g i := hg (g i) h
  have h2 : g i = i := g.injective h1
  omega

theorem Sfin_image_range {t : ℕ} {g : Equiv.Perm ℕ} (hg : g ∈ Sfin t) {s : Finset ℕ}
    (hs : s ⊆ Finset.range t) : s.image g ⊆ Finset.range t := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr (Sfin_lt hg (Finset.mem_range.mp (hs hi)))

/-! ### The action on rank-`t` parts -/

section Action

variable (𝒰 : BasisSystem) (t : ℕ)

theorem exists_rk_smul (g : Sfin t) (x : 𝒰.Rk t) : ∃ y, 𝒰.up t y = g.1 • 𝒰.up t x := by
  rw [𝒰.range_up, 𝒰.supp_smul]
  exact Sfin_image_range g.2 (𝒰.supp_up t x)

/-- `g • x` for `g ∈ S_t` and `x` of rank `t`. -/
noncomputable def rkSMul (g : Sfin t) (x : 𝒰.Rk t) : 𝒰.Rk t :=
  Classical.choose (exists_rk_smul 𝒰 t g x)

theorem up_rkSMul (g : Sfin t) (x : 𝒰.Rk t) :
    𝒰.up t (rkSMul 𝒰 t g x) = g.1 • 𝒰.up t x :=
  Classical.choose_spec (exists_rk_smul 𝒰 t g x)

noncomputable instance rkAction : MulAction (Sfin t) (𝒰.Rk t) where
  smul := rkSMul 𝒰 t
  one_smul := fun x => by
    apply 𝒰.up_inj t
    show 𝒰.up t (rkSMul 𝒰 t 1 x) = _
    rw [up_rkSMul]
    exact one_smul _ _
  mul_smul := fun g h x => by
    apply 𝒰.up_inj t
    show 𝒰.up t (rkSMul 𝒰 t (g * h) x) = 𝒰.up t (rkSMul 𝒰 t g (rkSMul 𝒰 t h x))
    rw [up_rkSMul, up_rkSMul, up_rkSMul]
    exact mul_smul g.1 h.1 _

variable {𝒰 t}

theorem up_smul (g : Sfin t) (x : 𝒰.Rk t) : 𝒰.up t (g • x) = g.1 • 𝒰.up t x :=
  up_rkSMul 𝒰 t g x

theorem rkSMul_prod {𝒱 : BasisSystem} (g : Sfin t) (z : 𝒰.Rk t × 𝒱.Rk t) :
    rkSMul (𝒰.prod 𝒱) t g z = (g • z.1, g • z.2) := by
  apply (𝒰.prod 𝒱).up_inj t
  rw [up_rkSMul]
  show (g.1 • 𝒰.up t z.1, g.1 • 𝒱.up t z.2) = (𝒰.up t (g • z.1), 𝒱.up t (g • z.2))
  rw [up_smul, up_smul]

end Action

/-! ### Permutation representations -/

section Perm

variable (K : Type) [Field K]

/-- `K[𝒰_t]` as a representation of `S_t`. -/
noncomputable abbrev permRep (𝒰 : BasisSystem) (t : ℕ) : Rep K (Sfin t) :=
  Rep.ofMulAction K (Sfin t) (𝒰.Rk t)

variable {K}

/-- A relabelling-invariant matrix restricted to rank `t` commutes with `S_t`. -/
theorem realise_comm {𝒰 𝒱 : BasisSystem} (a : InvMatrix K 𝒰 𝒱) (t : ℕ) (g : Sfin t) :
    a.realise t ∘ₗ Representation.ofMulAction K (Sfin t) (𝒰.Rk t) g =
      Representation.ofMulAction K (Sfin t) (𝒱.Rk t) g ∘ₗ a.realise t := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  ext y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.lsingle_apply, Representation.ofMulAction_single, InvMatrix.realise_single_apply,
    Representation.ofMulAction_apply, InvMatrix.realise_single_apply, up_smul, up_smul]
  have h := a.inv g.1 ((g⁻¹ : Sfin t).1 • 𝒱.up t y) (𝒰.up t x)
  rw [← h, Subgroup.coe_inv, smul_inv_smul]

/-- The morphism of representations with a given invariant matrix. -/
noncomputable def matHom {𝒰 𝒱 : BasisSystem} (a : InvMatrix K 𝒰 𝒱) (t : ℕ) :
    permRep K 𝒰 t ⟶ permRep K 𝒱 t where
  hom := ModuleCat.ofHom (a.realise t)
  comm := fun g => by
    apply ModuleCat.hom_ext
    exact realise_comm a t g

theorem matHom_hom {𝒰 𝒱 : BasisSystem} (a : InvMatrix K 𝒰 𝒱) (t : ℕ) :
    (matHom a t).hom = ModuleCat.ofHom (a.realise t) := rfl

end Perm

/-! ### Products -/

section Prod

variable {K : Type} [Field K] (𝒰 𝒱 : BasisSystem) (t : ℕ)

theorem prod_comm (g : Sfin t) :
    (finsuppTensorFinsupp' K (𝒰.Rk t) (𝒱.Rk t)).toLinearMap ∘ₗ
        TensorProduct.map (Representation.ofMulAction K (Sfin t) (𝒰.Rk t) g)
          (Representation.ofMulAction K (Sfin t) (𝒱.Rk t) g) =
      Representation.ofMulAction K (Sfin t) ((𝒰.prod 𝒱).Rk t) g ∘ₗ
        (finsuppTensorFinsupp' K (𝒰.Rk t) (𝒱.Rk t)).toLinearMap := by
  apply TensorProduct.ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro y
  apply LinearMap.ext_ring
  show finsuppTensorFinsupp' K (𝒰.Rk t) (𝒱.Rk t)
      (TensorProduct.map (Representation.ofMulAction K (Sfin t) (𝒰.Rk t) g)
        (Representation.ofMulAction K (Sfin t) (𝒱.Rk t) g)
        (Finsupp.single x 1 ⊗ₜ[K] Finsupp.single y 1)) =
    Representation.ofMulAction K (Sfin t) ((𝒰.prod 𝒱).Rk t) g
      (finsuppTensorFinsupp' K (𝒰.Rk t) (𝒱.Rk t) (Finsupp.single x 1 ⊗ₜ[K] Finsupp.single y 1))
  rw [TensorProduct.map_tmul, Representation.ofMulAction_single,
    Representation.ofMulAction_single, finsuppTensorFinsupp'_single_tmul_single,
    finsuppTensorFinsupp'_single_tmul_single, Representation.ofMulAction_single]
  congr 1
  exact (rkSMul_prod g (x, y)).symm

/-- `K[𝒰_t] ⊗ K[𝒱_t] ≅ K[(𝒰 × 𝒱)_t]` as representations of `S_t`. -/
noncomputable def permProdIso :
    permRep K 𝒰 t ⊗ permRep K 𝒱 t ≅ permRep K (𝒰.prod 𝒱) t :=
  Action.mkIso (Deletion.prodBasis K (𝒰.Rk t) (𝒱.Rk t)) fun g => by
    apply ModuleCat.hom_ext
    exact prod_comm 𝒰 𝒱 t g

theorem permProdIso_hom_hom :
    (permProdIso (K := K) 𝒰 𝒱 t).hom.hom = (Deletion.prodBasis K (𝒰.Rk t) (𝒱.Rk t)).hom := rfl

end Prod

/-! ### The inclusion of ranks -/

section Incl

variable (𝒰 : BasisSystem) {n N : ℕ} (h : n ≤ N)

include h in
theorem exists_inclRk (x : 𝒰.Rk n) : ∃ y : 𝒰.Rk N, 𝒰.up N y = 𝒰.up n x := by
  rw [𝒰.range_up]
  exact (𝒰.supp_up n x).trans (Finset.range_subset_range.mpr h)

/-- `𝒰_n ⊆ 𝒰_N`. -/
noncomputable def inclRk (x : 𝒰.Rk n) : 𝒰.Rk N := Classical.choose (exists_inclRk 𝒰 h x)

theorem up_inclRk (x : 𝒰.Rk n) : 𝒰.up N (inclRk 𝒰 h x) = 𝒰.up n x :=
  Classical.choose_spec (exists_inclRk 𝒰 h x)

theorem inclRk_injective : Function.Injective (inclRk 𝒰 h) := fun x y hxy => by
  apply 𝒰.up_inj n
  rw [← up_inclRk 𝒰 h x, ← up_inclRk 𝒰 h y, hxy]

theorem mem_range_inclRk (y : 𝒰.Rk N) :
    y ∈ Set.range (inclRk 𝒰 h) ↔ 𝒰.supp (𝒰.up N y) ⊆ Finset.range n := by
  rw [← 𝒰.range_up]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (up_inclRk 𝒰 h x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, 𝒰.up_inj N (by rw [up_inclRk, hx])⟩

/-- The inclusion commutes with the action of `S_n ⊆ S_N`. -/
theorem inclRk_smul (g : Sfin n) (x : 𝒰.Rk n) :
    inclRk 𝒰 h (g • x) = (⟨g.1, Sfin_mono h g.2⟩ : Sfin N) • inclRk 𝒰 h x := by
  apply 𝒰.up_inj N
  rw [up_inclRk, up_smul, up_smul, up_inclRk]

theorem inclRk_prod {𝒱 : BasisSystem} (z : 𝒰.Rk n × 𝒱.Rk n) :
    inclRk (𝒰.prod 𝒱) h z = (inclRk 𝒰 h z.1, inclRk 𝒱 h z.2) := by
  apply (𝒰.prod 𝒱).up_inj N
  rw [up_inclRk]
  show (𝒰.up n z.1, 𝒱.up n z.2) = (𝒰.up N (inclRk 𝒰 h z.1), 𝒱.up N (inclRk 𝒱 h z.2))
  rw [up_inclRk, up_inclRk]

end Incl

end DegreeProfilesReview.SymRep
