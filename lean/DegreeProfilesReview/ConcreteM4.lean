/-
Stage 3, step 3: the input M4 of Stage 2, CONSTRUCTED for the actual representation categories.

Let `P` be a class of representations of `S_t` over `K` (a `SchurClass`) that
  (a) is closed under ambient subobjects, ambient quotients and binary direct sums, and
  (b) contains the permutation module `K[𝒰_t]` of every basis system of support `≤ r`.
Then `SchurClass.toM4` is an `M4`-structure on the full subcategory `B = P.FullSubcategory`:

* `B` is abelian and its inclusion into `Rep K (S_t)` is exact and fully faithful
  (`ClosedSubcategory.lean`);
* `ω` is the underlying vector space; `Ω` is the forgetful functor on all representations, with
  mathlib's monoidal structure; `β` is the identity;
* `perm 𝒰 = K[𝒰_t]`, `basis` is the identity, `mat a` is the morphism `matHom a t` whose
  underlying linear map is literally the Stage 2 map `a.realise t`;
* `prodIso` is `K[𝒰_t] ⊗ K[𝒱_t] ≅ K[(𝒰 × 𝒱)_t]`, basis element to basis element;
* `sub s` is the ambient tensor product `K[𝒰_t] ⊗ S`, which lies in `P` because it embeds in
  `K[𝒰_t] ⊗ K[𝒱_t] ≅ K[(𝒰 × 𝒱)_t] ∈ P` (tensoring over a field is exact) and `P` is closed
  under ambient subobjects.

No field of `M4` is assumed.  What remains external for M4 is exactly (a) and (b) for the
intended class (the sign-twisted Schur image of the bounded-tail polynomial functors).
No closure of `P` under tensor products is assumed or used.
-/
import DegreeProfilesReview.SymRep
import DegreeProfilesReview.ClosedSubcategory
import DegreeProfilesReview.DeletionInterface
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.RingTheory.Flat.Basic

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DegreeProfilesReview.ConcreteM4

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ClosedSub
open DegreeProfilesReview.Deletion

/-- A class of representations of `S_t` that is closed under ambient subobjects, quotients and
binary direct sums and contains the permutation modules of support `≤ r`. -/
structure SchurClass (K : Type) [Field K] (r t : ℕ) where
  P : ObjectProperty (Rep K (Sfin t))
  [exact : IsExactClass P]
  perm_mem : ∀ 𝒰 : BasisSystem, 𝒰.Bounded r → P (permRep K 𝒰 t)

attribute [instance] SchurClass.exact

variable {K : Type} [Field K] {r t : ℕ}

/-- Tensoring a monomorphism of representations with a fixed representation on the left gives
a monomorphism (vector spaces over a field are flat). -/
theorem mono_whiskerLeft (X : Rep K (Sfin t)) {Y Z : Rep K (Sfin t)} (s : Y ⟶ Z) [Mono s] :
    Mono (X ◁ s) := by
  rw [Rep.mono_iff_injective]
  have hs : Function.Injective s.hom.hom := (Rep.mono_iff_injective s).mp inferInstance
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := X.V) s.hom.hom hs

namespace SchurClass

variable (S : SchurClass K r t)

/-- The category `B_t`. -/
abbrev B : Type 1 := S.P.FullSubcategory

/-- `K[𝒰_t] ⊗ S` lies in the class: it is an ambient subobject of `K[(𝒰 × 𝒱)_t]`. -/
theorem sub_mem {𝒰 𝒱 : BasisSystem} (hV : 𝒱.Bounded r) (hUV : (𝒰.prod 𝒱).Bounded r)
    {Y : S.B} (s : Y ⟶ (⟨permRep K 𝒱 t, S.perm_mem 𝒱 hV⟩ : S.B)) [Mono s] :
    S.P (permRep K 𝒰 t ⊗ Y.obj) := by
  haveI : Mono (S.P.ι.map s) := inferInstance
  haveI : Mono (permRep K 𝒰 t ◁ S.P.ι.map s) := mono_whiskerLeft _ _
  exact S.P.prop_of_mono ((permRep K 𝒰 t ◁ S.P.ι.map s) ≫ (permProdIso 𝒰 𝒱 t).hom)
    (S.perm_mem _ hUV)

/-- **M4, constructed.** -/
noncomputable def toM4 : M4.{0, 0, 1, 1} K r t S.B where
  ω := S.P.ι ⋙ Action.forget (ModuleCat.{0} K) (Sfin t)
  ω_lim := comp_preservesFiniteLimits _ _
  ω_colim := comp_preservesFiniteColimits _ _
  R := Rep K (Sfin t)
  ι := S.P.ι
  Ω := Action.forget (ModuleCat.{0} K) (Sfin t)
  β := Iso.refl _
  perm := fun 𝒰 h => ⟨permRep K 𝒰 t, S.perm_mem 𝒰 h⟩
  basis := fun _ _ => Iso.refl _
  mat := fun _ _ a => matHom a t
  mat_spec := fun _ _ a => by
    rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  prodIso := fun {𝒰 𝒱} _ _ _ => permProdIso 𝒰 𝒱 t
  prodIso_spec := fun {𝒰 𝒱} _ _ _ => by
    simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp,
      Action.forget_μ, MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight]
    rfl
  sub := fun {𝒰 𝒱} _ hV hUV {Y} s _ => ⟨permRep K 𝒰 t ⊗ Y.obj, S.sub_mem hV hUV s⟩
  subIso := fun _ _ _ _ _ => Iso.refl _

end SchurClass

/-- The underlying linear map of `mat a` in the constructed `M4` is literally the Stage 2 map
`a.realise t`. -/
theorem SchurClass.toM4_ω_mat (S : SchurClass K r t) {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r)
    (hV : 𝒱.Bounded r) (a : InvMatrix K 𝒰 𝒱) :
    S.toM4.ω.map (S.toM4.mat hU hV a) = ModuleCat.ofHom (a.realise t) := rfl

universe v' u'

/-- **Closure is derived, not assumed, for a Schur-type image.**  Let `F` be an exact functor
from an abelian category to `Rep K (S_t)` with a right adjoint whose counit is invertible (for
the Schur functor: source §7.3), and let `S` be a class closed under subobjects, quotients and
binary sums (a Serre class).  If the essential image of `S` contains the permutation modules of
support `≤ r`, it is a `SchurClass`: its closure under AMBIENT subobjects and quotients is the
stage-1 theorem `ImageClosure`. -/
noncomputable def SchurClass.ofAdjunction {Pol : Type u'} [Category.{v'} Pol] [Abelian Pol]
    (F : Pol ⥤ Rep K (Sfin t)) (G : Rep K (Sfin t) ⥤ Pol) (adj : F ⊣ G) [IsIso adj.counit]
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ObjectProperty Pol) [IsExactClass S]
    (hperm : ∀ 𝒰 : BasisSystem, 𝒰.Bounded r →
      ∃ X, S X ∧ Nonempty (F.obj X ≅ permRep K 𝒰 t)) : SchurClass K r t :=
  haveI := image_isExactClass F G adj S
  { P := ImageClosure.image F S
    perm_mem := hperm }

end DegreeProfilesReview.ConcreteM4
