/- Cycle 013: additivity of the actual shifted functor and its canonical restriction. -/
import ShiftedPreservation
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

set_option autoImplicit false
open CategoryTheory
namespace SelfContainedCycle013
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor
open DegreeProfilesReview.ShiftedM5 SelfContainedCycle004

variable {K Γ G : Type} [Field K] [Group Γ] [Group G] {ι : Type} [Fintype ι]

instance scFunctor_additive (s : ι → Γ) (c : ι → K) (i : G →* Γ)
    (hcomm : ∀ g k, i g * s k = s k * i g) :
    (scFunctor s c i hcomm).Additive where
  map_add {X Y f g} := by
    apply scHom_ext
    intro v hv
    apply Subtype.ext
    change (LinearMap.range (zOp s c Y.ρ)).mkQ (f.hom.hom v + g.hom.hom v) =
      (LinearMap.range (zOp s c Y.ρ)).mkQ (f.hom.hom v) +
        (LinearMap.range (zOp s c Y.ρ)).mkQ (g.hom.hom v)
    exact map_add _ _ _

instance Ψhat_additive (p a n : ℕ) [Fact p.Prime] (c : Fin a → K) :
    (Ψhat p a n c).Additive := scFunctor_additive _ _ _ _

instance canonicalΨ_additive (p a n r : ℕ) [Fact p.Prime] (c : Fin a → K) :
    (canonicalΨ p a n r c).Additive where
  map_add {X Y f g} := by
    change (Ψhat p a n c).map (f + g) = (Ψhat p a n c).map f + (Ψhat p a n c).map g
    exact Functor.map_add _

end SelfContainedCycle013
