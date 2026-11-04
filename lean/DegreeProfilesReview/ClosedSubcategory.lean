/-
Stage 3, step 2: a class of objects of an abelian category that is closed under ambient
subobjects, ambient quotients and binary direct sums (and is nonempty) spans a full
subcategory which is ABELIAN, and whose inclusion is EXACT (and fully faithful).

This is the categorical content of "the bounded-tail Schur image is an abelian subcategory
with ambient kernels and cokernels".  It is proved here for an arbitrary abelian category;
the hypothesis is the closure of the class, which for a Schur-type image follows from the
stage-1 lemmas of `ImageClosure.lean` (see `image_isExactClass`).

Main declarations:
* `IsExactClass P`                 — the closure hypothesis;
* `abelianFullSubcategory P`       — the abelian structure;
* `ι_preservesFiniteLimits`, `ι_preservesFiniteColimits` — exactness of the inclusion;
* `image_isExactClass`             — the essential image of a Serre-type class under an exact
                                     functor with fully faithful right adjoint is such a class.
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.ObjectProperty.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import DegreeProfilesReview.ImageClosure

universe v v' u u'

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace DegreeProfilesReview.ClosedSub

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A nonempty class of objects closed under ambient subobjects, quotients and binary direct
sums. -/
class IsExactClass (P : ObjectProperty C) : Prop extends
    P.IsClosedUnderSubobjects, P.IsClosedUnderQuotients where
  biprod : ∀ {X Y : C}, P X → P Y → P (X ⊞ Y)
  nonempty : ∃ X, P X

variable (P : ObjectProperty C) [IsExactClass P]

theorem prop_zero : P (0 : C) := by
  obtain ⟨X, hX⟩ := IsExactClass.nonempty (P := P)
  exact P.prop_of_mono (0 : (0 : C) ⟶ X) hX

instance : P.IsClosedUnderLimitsOfShape WalkingParallelPair where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    haveI : Mono (h.π.app WalkingParallelPair.zero) := by
      constructor
      intro Z a b hab
      apply h.isLimit.hom_ext
      intro j
      cases j with
      | zero => exact hab
      | one =>
        have e := h.π.naturality WalkingParallelPairHom.left
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at e
        rw [e, ← Category.assoc, ← Category.assoc, hab]
    exact P.prop_of_mono (h.π.app WalkingParallelPair.zero) (h.prop_diag_obj _)

instance : P.IsClosedUnderColimitsOfShape WalkingParallelPair where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    haveI : Epi (h.ι.app WalkingParallelPair.one) := by
      constructor
      intro Z a b hab
      apply h.isColimit.hom_ext
      intro j
      cases j with
      | one => exact hab
      | zero =>
        have e := h.ι.naturality WalkingParallelPairHom.left
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at e
        rw [← e, Category.assoc, Category.assoc, hab]
    exact P.prop_of_epi (h.ι.app WalkingParallelPair.one) (h.prop_diag_obj _)

instance : P.IsClosedUnderLimitsOfShape (Discrete WalkingPair) where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    let A := h.diag.obj ⟨WalkingPair.left⟩
    let B := h.diag.obj ⟨WalkingPair.right⟩
    let f : X ⟶ A ⊞ B := biprod.lift (h.π.app ⟨WalkingPair.left⟩) (h.π.app ⟨WalkingPair.right⟩)
    haveI : Mono f := by
      constructor
      intro Z a b hab
      apply h.isLimit.hom_ext
      rintro ⟨j⟩
      cases j with
      | left =>
        have := congrArg (fun k => k ≫ (biprod.fst : A ⊞ B ⟶ A)) hab
        simpa [f] using this
      | right =>
        have := congrArg (fun k => k ≫ (biprod.snd : A ⊞ B ⟶ B)) hab
        simpa [f] using this
    exact P.prop_of_mono f (IsExactClass.biprod (h.prop_diag_obj _) (h.prop_diag_obj _))

instance : P.IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    haveI : Mono (0 : X ⟶ (0 : C)) :=
      ⟨fun a b _ => h.isLimit.hom_ext fun j => j.as.elim⟩
    exact P.prop_of_mono (0 : X ⟶ (0 : C)) (prop_zero P)

/-! ### The abelian structure and exactness of the inclusion -/

instance : HasFiniteProducts P.FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The full subcategory on an exact class is abelian. -/
noncomputable instance abelianFullSubcategory : Abelian P.FullSubcategory := by
  haveI : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    have iso := Abelian.PreservesCoimageImageComparison.iso P.ι f
    haveI : IsIso (P.ι.map (Abelian.coimageImageComparison f)) := by
      rw [Arrow.isIso_iff_isIso_of_isIso iso.hom]
      infer_instance
    exact isIso_of_fully_faithful P.ι _
  exact Abelian.ofCoimageImageComparisonIsIso

/-- The inclusion of the full subcategory on an exact class preserves finite limits. -/
instance ι_preservesFiniteLimits : PreservesFiniteLimits P.ι :=
  Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- The inclusion of the full subcategory on an exact class preserves finite colimits. -/
instance ι_preservesFiniteColimits : PreservesFiniteColimits P.ι :=
  Functor.preservesFiniteColimits_of_preservesCokernels P.ι

end DegreeProfilesReview.ClosedSub

namespace DegreeProfilesReview.ClosedSub

/-! ### Schur-type images are exact classes -/

variable {C : Type u} [Category.{v} C] [Abelian C]
  {Pol : Type u'} [Category.{v'} Pol] [Abelian Pol]

/-- The essential image of an exact class `S` under an exact functor `F` whose right adjoint has
invertible counit is an exact class: closed under AMBIENT subobjects and quotients (stage 1,
`ImageClosure`), and under binary direct sums. -/
theorem image_isExactClass (F : Pol ⥤ C) (G : C ⥤ Pol) (adj : F ⊣ G) [IsIso adj.counit]
    [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ObjectProperty Pol) [IsExactClass S] : IsExactClass (ImageClosure.image F S) where
  prop_of_mono := fun i _ h => ImageClosure.image_closed_under_subobjects F G adj S i h
  prop_of_epi := fun p _ h => ImageClosure.image_closed_under_quotients F G adj S p h
  biprod := by
    rintro Y₁ Y₂ ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₂, h₂, ⟨e₂⟩⟩
    haveI : PreservesBinaryBiproduct X₁ X₂ F :=
      Limits.preservesBinaryBiproduct_of_preservesBinaryProduct F
    exact ⟨X₁ ⊞ X₂, IsExactClass.biprod h₁ h₂, ⟨F.mapBiprod X₁ X₂ ≪≫ biprod.mapIso e₁ e₂⟩⟩
  nonempty := by
    obtain ⟨X, hX⟩ := IsExactClass.nonempty (P := S)
    exact ⟨F.obj X, X, hX, ⟨Iso.refl _⟩⟩

end DegreeProfilesReview.ClosedSub
