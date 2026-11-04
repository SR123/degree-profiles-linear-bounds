/- A smaller sufficient input for constant membership transport.
   This proves an abstract reduction, not exactness of the shifted functor. -/
import DegreeProfilesReview.PCTransport
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace ExactnessHandoff

universe v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Preserving monomorphisms detects zero maps from a surviving simple object.
    No faithfulness or fullness of F is required. -/
theorem map_eq_zero_iff_from_simple (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesMonomorphisms] {S X : C} [Simple S]
    (hS : ¬ IsZero (F.obj S)) (f : S ⟶ X) : F.map f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    by_contra hn
    haveI : Mono f := mono_of_nonzero_from_simple hn
    exact hS (IsZero.of_mono_eq_zero (F.map f) hf)
  · intro hf
    rw [hf, F.map_zero]

open DegreeProfilesReview.Transport

/-- The existing PC stage transport needs only exactness and a surviving simple
    constant source to reflect refutability. -/
theorem const_mem_iff_of_simple (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P : PCDatum C} {Q : PCDatum D} [Simple P.U]
    (hU : ¬ IsZero (F.obj P.U)) (h : PCCompat F P Q) (j : ℕ) :
    P.ConstMem j ↔ Q.ConstMem j := by
  obtain ⟨β, hβ⟩ := stage_iso F h j
  obtain ⟨q, hq⟩ := cokernel_transport F (P.stage j).hom (Q.stage j).hom β h.αW hβ
  have key : F.map (P.c ≫ P.quot (P.stage j)) ≫ q.hom =
      h.αU.hom ≫ (Q.c ≫ Q.quot (Q.stage j)) := by
    rw [F.map_comp, Category.assoc, show F.map (P.quot (P.stage j)) ≫ q.hom =
      h.αW.hom ≫ Q.quot (Q.stage j) from hq, ← Category.assoc, h.hc, Category.assoc]
  unfold PCDatum.ConstMem
  constructor
  · intro h0
    rw [h0, F.map_zero, zero_comp] at key
    apply (cancel_epi h.αU.hom).mp
    rw [← key, comp_zero]
  · intro h0
    rw [h0, comp_zero] at key
    apply (map_eq_zero_iff_from_simple F hU _).mp
    apply (cancel_mono q.hom).mp
    rw [key, zero_comp]

/-- The NS image-membership test has the same smaller sufficient input. -/
theorem image_membership_iff_of_simple (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesMonomorphisms] [PreservesFiniteColimits F]
    {U V S : C} [Simple S] (hS : ¬ IsZero (F.obj S))
    (A : U ⟶ V) (j : S ⟶ V) {U' V' S' : D} (A' : U' ⟶ V') (j' : S' ⟶ V')
    (αU : F.obj U ≅ U') (αV : F.obj V ≅ V') (αS : F.obj S ≅ S')
    (hA : F.map A ≫ αV.hom = αU.hom ≫ A')
    (hj : F.map j ≫ αV.hom = αS.hom ≫ j') :
    j ≫ cokernel.π A = 0 ↔ j' ≫ cokernel.π A' = 0 := by
  obtain ⟨q, hq⟩ := cokernel_transport F A A' αU αV hA
  have key : F.map (j ≫ cokernel.π A) ≫ q.hom = αS.hom ≫ (j' ≫ cokernel.π A') := by
    rw [F.map_comp, Category.assoc, hq, ← Category.assoc, hj, Category.assoc]
  constructor
  · intro h0
    rw [h0, F.map_zero, zero_comp] at key
    apply (cancel_epi αS.hom).mp
    rw [← key, comp_zero]
  · intro h0
    rw [h0, comp_zero] at key
    apply (map_eq_zero_iff_from_simple F hS _).mp
    apply (cancel_mono q.hom).mp
    rw [key, zero_comp]

end ExactnessHandoff
