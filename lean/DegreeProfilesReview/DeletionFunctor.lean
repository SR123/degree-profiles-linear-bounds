/-
Stage 3, step 4c: the deletion functor on categories of representations, and its behaviour on
permutation modules.

General part.  For groups `Γ ⊇ A` and `G₀ → Γ` commuting with `A`:

* `delFunctor A i hcomm : Rep K Γ ⥤ Rep K G₀`,  `V ↦ image of (V^A → V_A)`.

  This is the unit component of "restrict to `G₀ × A`, then semisimplify `A`" (the functor
  `φ₁` of Hone et al., Example 5.1.3).  It is a plain functor: no exactness and no
  monoidality is claimed for it.

For a finite `Γ`-set `X` whose `A`-fixed points are `j : F ↪ X` (`FixedData`):

* `delPermIso : delFunctor (K[X]) ≅ K[F]`;
* `delTensIso Y : delFunctor (K[X] ⊗ Y) ≅ K[F] ⊗ delFunctor Y`, natural in `Y`
  (`delTensIso_natural`).

Everything here is proved; there is no external hypothesis.
-/
import DegreeProfilesReview.DeletionTensor
import Mathlib.RepresentationTheory.Rep

open CategoryTheory MonoidalCategory TensorProduct

namespace DegreeProfilesReview.DelFunctor

open DegreeProfilesReview.Del

variable {K : Type} [Field K] {Γ G₀ : Type} [Group Γ] [Group G₀] (A : Subgroup Γ)
  (i : G₀ →* Γ) (hcomm : ∀ g, ∀ a ∈ A, i g * a = a * i g)

theorem hom_aequivariant {M N : Rep K Γ} (f : M ⟶ N) : AEquivariant A M.ρ N.ρ f.hom.hom :=
  fun a _ v => Rep.hom_comm_apply f a v

/-- **The deletion functor.** -/
noncomputable def delFunctor : Rep K Γ ⥤ Rep K G₀ where
  obj M := Rep.of (delRep A M.ρ i hcomm)
  map {M N} f :=
    { hom := ModuleCat.ofHom (delMap f.hom.hom (hom_aequivariant A f))
      comm := fun g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro d
        obtain ⟨v, hv, rfl⟩ := del_induction A M.ρ d
        show delMap f.hom.hom (hom_aequivariant A f) (delRep A M.ρ i hcomm g (delMk A M.ρ v hv)) =
          delRep A N.ρ i hcomm g (delMap f.hom.hom (hom_aequivariant A f) (delMk A M.ρ v hv))
        rw [delRep_delMk, delMap_delMk, delMap_delMk, delRep_delMk]
        apply Subtype.ext
        rw [coe_delMk, coe_delMk, Rep.hom_comm_apply] }
  map_id M := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    obtain ⟨v, hv, rfl⟩ := del_induction A M.ρ d
    rfl
  map_comp f g := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    obtain ⟨v, hv, rfl⟩ := del_induction A _ d
    rfl

theorem delFunctor_map_delMk {M N : Rep K Γ} (f : M ⟶ N) (v : M.V) (hv : v ∈ inv A M.ρ) :
    ((delFunctor A i hcomm).map f).hom.hom (delMk A M.ρ v hv) =
      delMk A N.ρ (f.hom.hom v) (map_mem_inv (hom_aequivariant A f) hv) := rfl

/-! ### Permutation modules and tensoring with them -/

section Perm

variable {A i hcomm}
variable {X F : Type} [MulAction Γ X] [Finite X] [MulAction G₀ F] (D : FixedData K A X F)
  (hj : ∀ (g : G₀) (f : F), D.j (g • f) = i g • D.j f)

include hj in
theorem permDelEquiv_comm (g : G₀) (d : del A (Representation.ofMulAction K Γ X)) :
    permDelEquiv D (delRep A (Representation.ofMulAction K Γ X) i hcomm g d) =
      Representation.ofMulAction K G₀ F g (permDelEquiv D d) := by
  apply (permDelEquiv D).symm.injective
  rw [LinearEquiv.symm_apply_apply, permDelEquiv_symm_equivariant D i hcomm hj,
    LinearEquiv.symm_apply_apply]

/-- **The deletion of `K[X]` is `K[F]`**, as representations of `G₀`. -/
noncomputable def delPermIso :
    (delFunctor A i hcomm).obj (Rep.ofMulAction K Γ X) ≅ Rep.ofMulAction K G₀ F :=
  Action.mkIso (permDelEquiv D).toModuleIso fun g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    exact permDelEquiv_comm D hj g d

theorem delPermIso_hom_apply (d : del A (Representation.ofMulAction K Γ X)) :
    (delPermIso (hcomm := hcomm) D hj).hom.hom.hom d = permDelEquiv D d := rfl

theorem delPermIso_inv_apply (v : F →₀ K) :
    (delPermIso (hcomm := hcomm) D hj).inv.hom.hom v = (permDelEquiv D).symm v := rfl

open Classical in
include hj in
theorem tensDelEquiv_comm (Y : Rep K Γ) (g : G₀)
    (d : del A (V := (X →₀ K) ⊗[K] Y.V) ((Representation.ofMulAction K Γ X).tprod Y.ρ)) :
    tensDelEquiv Y.ρ D (delRep A (V := (X →₀ K) ⊗[K] Y.V)
        ((Representation.ofMulAction K Γ X).tprod Y.ρ) i hcomm g d) =
      ((Representation.ofMulAction K G₀ F).tprod (delRep A Y.ρ i hcomm)) g
        (tensDelEquiv Y.ρ D d) := by
  apply (tensDelEquiv Y.ρ D).symm.injective
  rw [LinearEquiv.symm_apply_apply, tensDelEquiv_symm_equivariant D i hcomm hj,
    LinearEquiv.symm_apply_apply]

open Classical in
/-- **The deletion commutes with tensoring by `K[X]`**: `del (K[X] ⊗ Y) ≅ K[F] ⊗ del Y`. -/
noncomputable def delTensIso (Y : Rep K Γ) :
    (delFunctor A i hcomm).obj (Rep.ofMulAction K Γ X ⊗ Y) ≅
      Rep.ofMulAction K G₀ F ⊗ (delFunctor A i hcomm).obj Y :=
  Action.mkIso (tensDelEquiv Y.ρ D).toModuleIso fun g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    exact tensDelEquiv_comm D hj Y g d

open Classical in
theorem delTensIso_inv_apply (Y : Rep K Γ) (t : (F →₀ K) ⊗[K] del A Y.ρ) :
    (delTensIso (hcomm := hcomm) D hj Y).inv.hom.hom t = (tensDelEquiv Y.ρ D).symm t := rfl

open Classical in
/-- Naturality of `delTensIso` in `Y`. -/
theorem delTensIso_natural {Y Y' : Rep K Γ} (f : Y ⟶ Y') :
    (delFunctor A i hcomm).map (Rep.ofMulAction K Γ X ◁ f) ≫ (delTensIso D hj Y').hom =
      (delTensIso D hj Y).hom ≫ (Rep.ofMulAction K G₀ F ◁ (delFunctor A i hcomm).map f) := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact (tensDelEquiv_symm_natural D Y.ρ Y'.ρ f.hom.hom (hom_aequivariant A f) t).symm

end Perm

end DegreeProfilesReview.DelFunctor
