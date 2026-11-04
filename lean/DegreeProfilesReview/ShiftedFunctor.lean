/-
Stage 5, step 5: the shifted cyclic functor on categories of representations, and its behaviour
on permutation modules.  This is the analogue of `DeletionFunctor.lean`.

General part.  For a group `Γ`, elements `s : ι → Γ`, scalars `c : ι → K` and `G₀ → Γ` commuting
with every `s i`:

* `scFunctor s c i hcomm : Rep K Γ ⥤ Rep K G₀`,  `V ↦ ker z / (ker z ∩ range z)`,
  `z = ∑ c i • (s i - 1)`.

  For an elementary abelian `p`-group with basis `s` and generic `c` this is the unit component
  of the functor of Hone et al., Definition 8.3.1 / Theorem 8.3.3.  It is a plain functor: no
  exactness and no monoidality is claimed for it here.

For a finite `Γ`-set `X` with fixed-point data `D : ShiftFixedData s c X F`:

* `scPermIso : scFunctor (K[X]) ≅ K[F]`;
* `scTensIso Y : scFunctor (K[X] ⊗ Y) ≅ K[F] ⊗ scFunctor Y`, natural in `Y`
  (`scTensIso_natural`).

Everything here is proved; there is no external hypothesis.
-/
import DegreeProfilesReview.ShiftedTensor
import Mathlib.RepresentationTheory.Rep

open CategoryTheory MonoidalCategory TensorProduct

namespace DegreeProfilesReview.ShiftedFunctor

open DegreeProfilesReview.Del DegreeProfilesReview.Shifted

variable {K : Type} [Field K] {Γ G₀ : Type} [Group Γ] [Group G₀] {ι : Type} [Fintype ι]
  (s : ι → Γ) (c : ι → K) (i : G₀ →* Γ) (hcomm : ∀ g k, i g * s k = s k * i g)

omit [Fintype ι] in
theorem hom_sequivariant {M N : Rep K Γ} (f : M ⟶ N) : SEquivariant s M.ρ N.ρ f.hom.hom :=
  fun k v => Rep.hom_comm_apply f (s k) v

/-- The value of the shifted cyclic functor on an object. -/
noncomputable def scObj (M : Rep K Γ) : Rep K G₀ := Rep.of (scRep s c M.ρ i hcomm)

/-- The value of the shifted cyclic functor on a morphism. -/
noncomputable def scHom {M N : Rep K Γ} (f : M ⟶ N) :
    scObj s c i hcomm M ⟶ scObj s c i hcomm N where
  hom := ModuleCat.ofHom (scMap c f.hom.hom (hom_sequivariant s f))
  comm := fun g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    obtain ⟨v, hv, rfl⟩ := sc_induction s c M.ρ d
    show scMap c f.hom.hom (hom_sequivariant s f) (scRep s c M.ρ i hcomm g (scMk s c M.ρ v hv)) =
      scRep s c N.ρ i hcomm g (scMap c f.hom.hom (hom_sequivariant s f) (scMk s c M.ρ v hv))
    rw [scRep_scMk, scMap_scMk, scMap_scMk, scRep_scMk]
    apply scMk_congr
    exact Rep.hom_comm_apply f (i g) v

theorem scHom_scMk {M N : Rep K Γ} (f : M ⟶ N) (v : M.V)
    (hv : v ∈ LinearMap.ker (zOp s c M.ρ)) :
    (scHom s c i hcomm f).hom.hom (scMk s c M.ρ v hv) =
      scMk s c N.ρ (f.hom.hom v) (map_mem_ker c (hom_sequivariant s f) hv) := rfl

theorem scHom_ext {M : Rep K Γ} {N : Rep K G₀} (a b : scObj s c i hcomm M ⟶ N)
    (h : ∀ v hv, a.hom.hom (scMk s c M.ρ v hv) = b.hom.hom (scMk s c M.ρ v hv)) : a = b := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro d
  obtain ⟨v, hv, hd⟩ := sc_induction s c M.ρ d
  rw [hd]
  exact h v hv

/-- **The shifted cyclic functor.** -/
noncomputable def scFunctor : Rep K Γ ⥤ Rep K G₀ where
  obj M := scObj s c i hcomm M
  map f := scHom s c i hcomm f
  map_id M := by
    apply scHom_ext
    intro v hv
    exact (scHom_scMk s c i hcomm (𝟙 M) v hv).trans (scMk_congr s c M.ρ rfl _ hv)
  map_comp {M N P} f g := by
    apply scHom_ext
    intro v hv
    exact (scHom_scMk s c i hcomm (f ≫ g) v hv).trans
      ((scMk_congr s c P.ρ rfl _ (map_mem_ker c (hom_sequivariant s g)
          (map_mem_ker c (hom_sequivariant s f) hv))).trans
        ((scHom_scMk s c i hcomm g (f.hom.hom v) (map_mem_ker c (hom_sequivariant s f) hv)).symm.trans
          (congrArg (scHom s c i hcomm g).hom.hom (scHom_scMk s c i hcomm f v hv).symm)))

theorem scFunctor_map_scMk {M N : Rep K Γ} (f : M ⟶ N) (v : M.V)
    (hv : v ∈ LinearMap.ker (zOp s c M.ρ)) :
    ((scFunctor s c i hcomm).map f).hom.hom (scMk s c M.ρ v hv) =
      scMk s c N.ρ (f.hom.hom v) (map_mem_ker c (hom_sequivariant s f) hv) := rfl

/-! ### Permutation modules and tensoring with them -/

section Perm

variable {s c i hcomm}
variable {X F : Type} [MulAction Γ X] [Finite X] [MulAction G₀ F] (D : ShiftFixedData s c X F)
  (hj : ∀ (g : G₀) (f : F), D.j (g • f) = i g • D.j f)

include hj in
theorem permScEquiv_comm (g : G₀) (d : sc s c (Representation.ofMulAction K Γ X)) :
    permScEquiv D (scRep s c (Representation.ofMulAction K Γ X) i hcomm g d) =
      Representation.ofMulAction K G₀ F g (permScEquiv D d) := by
  apply (permScEquiv D).symm.injective
  rw [LinearEquiv.symm_apply_apply, permScEquiv_symm_equivariant D i hcomm hj,
    LinearEquiv.symm_apply_apply]

/-- **The shifted cyclic functor sends `K[X]` to `K[F]`**, as representations of `G₀`. -/
noncomputable def scPermIso :
    (scFunctor s c i hcomm).obj (Rep.ofMulAction K Γ X) ≅ Rep.ofMulAction K G₀ F :=
  Action.mkIso (permScEquiv D).toModuleIso fun g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    exact permScEquiv_comm D hj g d

theorem scPermIso_hom_apply (d : sc s c (Representation.ofMulAction K Γ X)) :
    (scPermIso (hcomm := hcomm) D hj).hom.hom.hom d = permScEquiv D d := rfl

theorem scPermIso_inv_apply (v : F →₀ K) :
    (scPermIso (hcomm := hcomm) D hj).inv.hom.hom v = (permScEquiv D).symm v := rfl

open Classical in
include hj in
theorem tensScEquiv_comm (Y : Rep K Γ) (g : G₀)
    (d : sc s c (V := (X →₀ K) ⊗[K] Y.V) ((Representation.ofMulAction K Γ X).tprod Y.ρ)) :
    tensScEquiv Y.ρ D (scRep s c (V := (X →₀ K) ⊗[K] Y.V)
        ((Representation.ofMulAction K Γ X).tprod Y.ρ) i hcomm g d) =
      ((Representation.ofMulAction K G₀ F).tprod (scRep s c Y.ρ i hcomm)) g
        (tensScEquiv Y.ρ D d) := by
  apply (tensScEquiv Y.ρ D).symm.injective
  rw [LinearEquiv.symm_apply_apply, tensScEquiv_symm_equivariant D i hcomm hj,
    LinearEquiv.symm_apply_apply]

open Classical in
/-- **The shifted cyclic functor commutes with tensoring by `K[X]`**:
`sc (K[X] ⊗ Y) ≅ K[F] ⊗ sc Y`. -/
noncomputable def scTensIso (Y : Rep K Γ) :
    (scFunctor s c i hcomm).obj (Rep.ofMulAction K Γ X ⊗ Y) ≅
      Rep.ofMulAction K G₀ F ⊗ (scFunctor s c i hcomm).obj Y :=
  Action.mkIso (tensScEquiv Y.ρ D).toModuleIso fun g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    exact tensScEquiv_comm D hj Y g d

open Classical in
theorem scTensIso_inv_apply (Y : Rep K Γ) (t : (F →₀ K) ⊗[K] sc s c Y.ρ) :
    (scTensIso (hcomm := hcomm) D hj Y).inv.hom.hom t = (tensScEquiv Y.ρ D).symm t := rfl

open Classical in
/-- Naturality of `scTensIso` in `Y`. -/
theorem scTensIso_natural {Y Y' : Rep K Γ} (f : Y ⟶ Y') :
    (scFunctor s c i hcomm).map (Rep.ofMulAction K Γ X ◁ f) ≫ (scTensIso D hj Y').hom =
      (scTensIso D hj Y).hom ≫ (Rep.ofMulAction K G₀ F ◁ (scFunctor s c i hcomm).map f) := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact (tensScEquiv_symm_natural D Y.ρ Y'.ρ f.hom.hom (hom_sequivariant s f) t).symm

end Perm

end DegreeProfilesReview.ShiftedFunctor
