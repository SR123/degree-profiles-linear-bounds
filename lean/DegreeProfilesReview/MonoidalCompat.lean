/-
Prompt 04, item 7 (naturality of the monoidal comparison on subobject inclusions).

For a monoidal functor `F` and comparison isomorphisms `αX : F X ≅ X'`, `αL : F L ≅ L'`,
`e : F S ≅ S'` compatible with `s : S ⟶ L` and `s' : S' ⟶ L'`, the canonical comparison
`F (X ⊗ S) ≅ X' ⊗ S'` is compatible with `X ◁ s` and `X' ◁ s'`.  This is exactly the field
`hT` of `Transport.PCCompat` when `T s = (X ⊗ S ⟶ X ⊗ L)` and `αM` is the canonical
comparison `F (X ⊗ L) ≅ X' ⊗ L'`.

The statement lives in the ambient monoidal categories; it uses only naturality of the
cotensorator, not exactness.
-/
import Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory MonoidalCategory

namespace DegreeProfilesReview.MonoidalCompat

universe v v' u u'

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

/-- The canonical comparison `F (X ⊗ S) ≅ X' ⊗ S'`. -/
noncomputable def tensorComparison {X S : C} {X' S' : D} (αX : F.obj X ≅ X')
    (e : F.obj S ≅ S') : F.obj (X ⊗ S) ≅ X' ⊗ S' :=
  (Functor.Monoidal.μIso F X S).symm ≪≫ tensorIso αX e

theorem tensorComparison_hom {X S : C} {X' S' : D} (αX : F.obj X ≅ X') (e : F.obj S ≅ S') :
    (tensorComparison F αX e).hom = Functor.OplaxMonoidal.δ F X S ≫ (αX.hom ⊗ₘ e.hom) := rfl

/-- Naturality of the comparison with respect to a (subobject) inclusion `s : S ⟶ L`. -/
theorem whiskerLeft_compat {X S L : C} {X' S' L' : D} (αX : F.obj X ≅ X')
    (αL : F.obj L ≅ L') (e : F.obj S ≅ S') (s : S ⟶ L) (s' : S' ⟶ L')
    (h : F.map s ≫ αL.hom = e.hom ≫ s') :
    F.map (X ◁ s) ≫ (tensorComparison F αX αL).hom =
      (tensorComparison F αX e).hom ≫ (X' ◁ s') := by
  rw [tensorComparison_hom, tensorComparison_hom, ← Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural_right, Category.assoc, Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, h]

end DegreeProfilesReview.MonoidalCompat
