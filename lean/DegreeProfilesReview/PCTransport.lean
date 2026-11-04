/-
Prompt 04 (b): the abstract transport theorem for the embedded PC closure.

Setting.  `𝒜`, `ℬ` abelian categories, `F : 𝒜 ⥤ ℬ` a functor that preserves zero morphisms,
finite limits and finite colimits (i.e. is exact).  A *PC datum* in an abelian category is

  `W` (polynomials of degree ≤ d),  `ℓ : L ⟶ W` (degree ≤ d-1),  `μ : M ⟶ W`
  (multiplication, `M = X ⊗ L`),  `v₀ : V₀ ⟶ W` (axiom span),  `c : U ⟶ W` (the constant),
  and an assignment `T` sending a monomorphism `s : S ⟶ L` to an object over `M`
  (in the application `T s = (X ⊗ S ⟶ X ⊗ L)`).

The closure step is written with kernels and cokernels only, keeping *actual embeddings*:

  `π  = coker v            : W ⟶ W/V`
  `ι  = ker (ℓ ≫ π)        : V ∩ L ⟶ L`          (the embedded intersection)
  `m  = T(ι) ≫ μ           : X ⊗ (V ∩ L) ⟶ W`     (restricted multiplication)
  `v⁺ = ker (π ≫ coker (m ≫ π)) : V + im m ⟶ W`.

`Submodule` sanity lemmas at the end check that, for vector spaces, these two formulas are
literally `V ⊓ L` (as a subspace of `L`) and `V ⊔ range m`.

Main results (no `sorry`, no axioms beyond the standard ones):
* `stage_iso`: if the two data are compatible with `F` (structure `PCCompat`, whose fields are
  the explicit comparison isomorphisms, the commuting squares, and the compatibility of `F`
  with `T` on monomorphisms into `L`), then `F` carries every embedded stage
  `V_j ⟶ W` to the embedded stage `V'_j ⟶ W'`.
* `const_mem_iff`: if moreover `F` is faithful, `c` lies in `V_j` (i.e. `c ≫ coker v_j = 0`)
  iff `c'` lies in `V'_j`.

What is NOT proved here: that the concrete functor `Φ` of the manuscript satisfies the
hypotheses.  `PCCompat` is an explicit hypothesis register, not a proof; see `DEPENDENCIES.md`.
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic

open CategoryTheory CategoryTheory.Limits

namespace DegreeProfilesReview.Transport

universe v v' u u'

/-! ### Transport of kernels and cokernels along a functor preserving them -/

section KerCoker

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]
variable {ℬ : Type u'} [Category.{v'} ℬ] [HasZeroMorphisms ℬ]
variable (F : 𝒜 ⥤ ℬ) [F.PreservesZeroMorphisms]

/-- If `F` preserves the kernel of `f`, and `F f` is identified with `f'` by isomorphisms,
then `F (ker f) ≅ ker f'` compatibly with the embeddings. -/
theorem kernel_transport {X Y : 𝒜} (f : X ⟶ Y) [HasKernel f]
    [PreservesLimit (parallelPair f 0) F]
    {X' Y' : ℬ} (f' : X' ⟶ Y') [HasKernel f'] (x : F.obj X ≅ X') (y : F.obj Y ≅ Y')
    (w : F.map f ≫ y.hom = x.hom ≫ f') :
    ∃ k : F.obj (kernel f) ≅ kernel f', F.map (kernel.ι f) ≫ x.hom = k.hom ≫ kernel.ι f' := by
  refine ⟨PreservesKernel.iso F f ≪≫ kernel.mapIso (F.map f) f' x y w, ?_⟩
  simp [PreservesKernel.iso_hom]

/-- Dual statement for cokernels. -/
theorem cokernel_transport {X Y : 𝒜} (f : X ⟶ Y) [HasCokernel f]
    [PreservesColimit (parallelPair f 0) F]
    {X' Y' : ℬ} (f' : X' ⟶ Y') [HasCokernel f'] (x : F.obj X ≅ X') (y : F.obj Y ≅ Y')
    (w : F.map f ≫ y.hom = x.hom ≫ f') :
    ∃ q : F.obj (cokernel f) ≅ cokernel f',
      F.map (cokernel.π f) ≫ q.hom = y.hom ≫ cokernel.π f' := by
  refine ⟨PreservesCokernel.iso F f ≪≫ cokernel.mapIso (F.map f) f' x y w, ?_⟩
  simp

end KerCoker

/-! ### PC data and the embedded closure -/

/-- The categorical data of the degree-`d` PC closure. -/
structure PCDatum (𝒜 : Type u) [Category.{v} 𝒜] where
  (W L M U V₀ : 𝒜)
  ℓ : L ⟶ W
  μ : M ⟶ W
  v₀ : V₀ ⟶ W
  c : U ⟶ W
  /-- `T s = (X ⊗ S ⟶ X ⊗ L)` for a monomorphism `s : S ⟶ L`. -/
  T : ∀ {S : 𝒜} (s : S ⟶ L) [Mono s], Over M

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ]

namespace PCDatum

variable (D : PCDatum 𝒜)

/-- `π = coker v : W ⟶ W/V`. -/
noncomputable def quot (v : Over D.W) : D.W ⟶ cokernel v.hom := cokernel.π v.hom

/-- The embedded intersection `V ∩ L ⟶ L`, as the kernel of `L ⟶ W ⟶ W/V`. -/
noncomputable def inter (v : Over D.W) : kernel (D.ℓ ≫ D.quot v) ⟶ D.L :=
  kernel.ι (D.ℓ ≫ D.quot v)

instance (v : Over D.W) : Mono (D.inter v) := by
  unfold inter; infer_instance

/-- Restricted multiplication `X ⊗ (V ∩ L) ⟶ X ⊗ L ⟶ W`. -/
noncomputable def mulMap (v : Over D.W) : (D.T (D.inter v)).left ⟶ D.W :=
  (D.T (D.inter v)).hom ≫ D.μ

/-- One closure step `V ↦ V + im(μ|_{X ⊗ (V ∩ L)})`, as an embedded object over `W`. -/
noncomputable def next (v : Over D.W) : Over D.W :=
  Over.mk (kernel.ι (D.quot v ≫ cokernel.π (D.mulMap v ≫ D.quot v)))

/-- The closure chain, as embedded objects over `W`. -/
noncomputable def stage : ℕ → Over D.W
  | 0 => Over.mk D.v₀
  | j + 1 => D.next (stage j)

/-- "`c` lies in the `j`-th stage": the composite `U ⟶ W ⟶ W / V_j` vanishes. -/
def ConstMem (j : ℕ) : Prop := D.c ≫ D.quot (D.stage j) = 0

end PCDatum

/-- Compatibility of two PC data with a functor: comparison isomorphisms, commuting squares,
and compatibility with the assignments `T` on monomorphisms into `L`.  Every field is an
explicit hypothesis of the transport theorem. -/
structure PCCompat (F : 𝒜 ⥤ ℬ) (D : PCDatum 𝒜) (D' : PCDatum ℬ) where
  αW : F.obj D.W ≅ D'.W
  αL : F.obj D.L ≅ D'.L
  αM : F.obj D.M ≅ D'.M
  αU : F.obj D.U ≅ D'.U
  αV₀ : F.obj D.V₀ ≅ D'.V₀
  hℓ : F.map D.ℓ ≫ αW.hom = αL.hom ≫ D'.ℓ
  hμ : F.map D.μ ≫ αW.hom = αM.hom ≫ D'.μ
  hv₀ : F.map D.v₀ ≫ αW.hom = αV₀.hom ≫ D'.v₀
  hc : F.map D.c ≫ αW.hom = αU.hom ≫ D'.c
  hT : ∀ {S : 𝒜} (s : S ⟶ D.L) [Mono s] {S' : ℬ} (s' : S' ⟶ D'.L) [Mono s']
    (e : F.obj S ≅ S'), F.map s ≫ αL.hom = e.hom ≫ s' →
    ∃ eT : F.obj (D.T s).left ≅ (D'.T s').left,
      F.map (D.T s).hom ≫ αM.hom = eT.hom ≫ (D'.T s').hom

section Main

variable (F : 𝒜 ⥤ ℬ) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]
variable {D : PCDatum 𝒜} {D' : PCDatum ℬ}

/-- One step of the induction: compatible embedded subobjects have compatible successors,
and compatible quotient maps. -/
theorem next_iso (h : PCCompat F D D') (v : Over D.W) (v' : Over D'.W)
    (β : F.obj v.left ≅ v'.left) (hβ : F.map v.hom ≫ h.αW.hom = β.hom ≫ v'.hom) :
    ∃ β' : F.obj (D.next v).left ≅ (D'.next v').left,
      F.map (D.next v).hom ≫ h.αW.hom = β'.hom ≫ (D'.next v').hom := by
  -- 1. the quotients `W/V`
  obtain ⟨q, hq⟩ := cokernel_transport F v.hom v'.hom β h.αW hβ
  -- 2. the embedded intersections
  have w2 : F.map (D.ℓ ≫ D.quot v) ≫ q.hom = h.αL.hom ≫ (D'.ℓ ≫ D'.quot v') := by
    unfold PCDatum.quot
    rw [F.map_comp, Category.assoc, hq, ← Category.assoc, h.hℓ, Category.assoc]
  obtain ⟨eI, heI⟩ := kernel_transport F (D.ℓ ≫ D.quot v) (D'.ℓ ≫ D'.quot v') h.αL q w2
  -- 3. compatibility with `T`
  obtain ⟨eT, heT⟩ := h.hT (D.inter v) (D'.inter v') eI heI
  -- 4. restricted multiplication
  have w4 : F.map (D.mulMap v ≫ D.quot v) ≫ q.hom = eT.hom ≫ (D'.mulMap v' ≫ D'.quot v') := by
    unfold PCDatum.mulMap PCDatum.quot
    rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc, hq, ← Category.assoc (F.map D.μ),
      h.hμ, Category.assoc, ← Category.assoc (F.map _), heT]
    simp only [Category.assoc]
  obtain ⟨q₂, hq₂⟩ := cokernel_transport F (D.mulMap v ≫ D.quot v) (D'.mulMap v' ≫ D'.quot v')
    eT q w4
  -- 5. the new embedded subobject
  have w5 : F.map (D.quot v ≫ cokernel.π (D.mulMap v ≫ D.quot v)) ≫ q₂.hom =
      h.αW.hom ≫ (D'.quot v' ≫ cokernel.π (D'.mulMap v' ≫ D'.quot v')) := by
    rw [F.map_comp, Category.assoc, hq₂, ← Category.assoc, show F.map (D.quot v) ≫ q.hom =
      h.αW.hom ≫ D'.quot v' from hq, Category.assoc]
  exact kernel_transport F _ _ h.αW q₂ w5

/-- **Abstract transport of the embedded PC closure.**  For every `j`, `F` carries the
embedded stage `V_j ⟶ W` to the embedded stage `V'_j ⟶ W'`. -/
theorem stage_iso (h : PCCompat F D D') (j : ℕ) :
    ∃ β : F.obj (D.stage j).left ≅ (D'.stage j).left,
      F.map (D.stage j).hom ≫ h.αW.hom = β.hom ≫ (D'.stage j).hom := by
  induction j with
  | zero => exact ⟨h.αV₀, h.hv₀⟩
  | succ j ih =>
    obtain ⟨β, hβ⟩ := ih
    exact next_iso F h _ _ β hβ

/-- **Membership of the constant transfers and is reflected** (faithfulness is used only for
the reflection). -/
theorem const_mem_iff [F.Faithful] (h : PCCompat F D D') (j : ℕ) :
    D.ConstMem j ↔ D'.ConstMem j := by
  obtain ⟨β, hβ⟩ := stage_iso F h j
  obtain ⟨q, hq⟩ := cokernel_transport F (D.stage j).hom (D'.stage j).hom β h.αW hβ
  have key : F.map (D.c ≫ D.quot (D.stage j)) ≫ q.hom =
      h.αU.hom ≫ (D'.c ≫ D'.quot (D'.stage j)) := by
    rw [F.map_comp, Category.assoc, show F.map (D.quot (D.stage j)) ≫ q.hom =
      h.αW.hom ≫ D'.quot (D'.stage j) from hq, ← Category.assoc, h.hc, Category.assoc]
  unfold PCDatum.ConstMem
  constructor
  · intro h0
    rw [h0, F.map_zero, zero_comp] at key
    have : h.αU.hom ≫ (D'.c ≫ D'.quot (D'.stage j)) = h.αU.hom ≫ 0 := by
      rw [← key, comp_zero]
    exact (cancel_epi h.αU.hom).mp this
  · intro h0
    rw [h0, comp_zero] at key
    have h1 : F.map (D.c ≫ D.quot (D.stage j)) = 0 := by
      have : F.map (D.c ≫ D.quot (D.stage j)) ≫ q.hom = 0 ≫ q.hom := by rw [key, zero_comp]
      exact (cancel_mono q.hom).mp this
    apply F.map_injective
    rw [h1, F.map_zero]

/-- At a common stage beyond both stabilisation indices the statement is the transfer of
degree-bounded refutability; this corollary just packages two indices. -/
theorem const_mem_iff_of_le [F.Faithful] (h : PCCompat F D D') {j₁ j₂ : ℕ}
    (h₁ : ∀ j, j₁ ≤ j → (D.ConstMem j ↔ D.ConstMem j₁))
    (h₂ : ∀ j, j₂ ≤ j → (D'.ConstMem j ↔ D'.ConstMem j₂)) :
    D.ConstMem j₁ ↔ D'.ConstMem j₂ := by
  rw [← h₁ (max j₁ j₂) (le_max_left _ _), ← h₂ (max j₁ j₂) (le_max_right _ _)]
  exact const_mem_iff F h _

end Main

/-! ### NS: image membership transfers (manuscript `lem:image`, abstract form) -/

section ImageMembership

variable (F : 𝒜 ⥤ ℬ) [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] [F.Faithful]

/-- "`j(1) ∈ im A`" is the vanishing of `K ⟶ V ⟶ coker A`.  If `F` preserves the cokernel of
`A`, is faithful, and carries `(A, j)` to `(A', j')` compatibly, then membership holds for
`(A, j)` iff it holds for `(A', j')`.  No invariant preimage of `j(1)` is asserted. -/
theorem image_membership_iff {Uo Vo Ko : 𝒜} (A : Uo ⟶ Vo) (j : Ko ⟶ Vo)
    {Uo' Vo' Ko' : ℬ} (A' : Uo' ⟶ Vo') (j' : Ko' ⟶ Vo')
    (αU : F.obj Uo ≅ Uo') (αV : F.obj Vo ≅ Vo') (αK : F.obj Ko ≅ Ko')
    (hA : F.map A ≫ αV.hom = αU.hom ≫ A') (hj : F.map j ≫ αV.hom = αK.hom ≫ j') :
    j ≫ cokernel.π A = 0 ↔ j' ≫ cokernel.π A' = 0 := by
  obtain ⟨q, hq⟩ := cokernel_transport F A A' αU αV hA
  have key : F.map (j ≫ cokernel.π A) ≫ q.hom = αK.hom ≫ (j' ≫ cokernel.π A') := by
    rw [F.map_comp, Category.assoc, hq, ← Category.assoc, hj, Category.assoc]
  constructor
  · intro h0
    rw [h0, F.map_zero, zero_comp] at key
    have : αK.hom ≫ (j' ≫ cokernel.π A') = αK.hom ≫ 0 := by rw [← key, comp_zero]
    exact (cancel_epi αK.hom).mp this
  · intro h0
    rw [h0, comp_zero] at key
    have h1 : F.map (j ≫ cokernel.π A) = 0 := by
      have : F.map (j ≫ cokernel.π A) ≫ q.hom = 0 ≫ q.hom := by rw [key, zero_comp]
      exact (cancel_mono q.hom).mp this
    apply F.map_injective
    rw [h1, F.map_zero]

end ImageMembership

/-! ### Sanity lemmas: for vector spaces the two formulas are `V ⊓ L` and `V ⊔ range m` -/

section Sanity

variable {K : Type*} [Field K] {Wm Lm Mm : Type*}
  [AddCommGroup Wm] [Module K Wm] [AddCommGroup Lm] [Module K Lm] [AddCommGroup Mm] [Module K Mm]

/-- `ker (L ⟶ W ⟶ W/V)` is the preimage of `V` in `L`, i.e. `V ∩ L` as a subspace of `L`. -/
theorem ker_inter_eq (V : Submodule K Wm) (ℓ : Lm →ₗ[K] Wm) :
    LinearMap.ker (V.mkQ ∘ₗ ℓ) = V.comap ℓ := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]

/-- `ker (W ⟶ W/V ⟶ (W/V)/π(im m))` is `V + im m`. -/
theorem ker_sum_eq (V : Submodule K Wm) (m : Mm →ₗ[K] Wm) :
    LinearMap.ker ((LinearMap.range (V.mkQ ∘ₗ m)).mkQ ∘ₗ V.mkQ) = V ⊔ LinearMap.range m := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, LinearMap.range_comp, Submodule.comap_map_mkQ]

end Sanity

end DegreeProfilesReview.Transport
