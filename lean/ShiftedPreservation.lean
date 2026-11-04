/-
Cycle 004: the actual shifted-cyclic functor preserves the canonical classes.
This proves object preservation, not exactness or equivalence.
-/
import RestrictionRelations
import DegreeProfilesReview.ShiftedM5

set_option autoImplicit false
open CategoryTheory
namespace SelfContainedCycle004
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor
open SelfContainedCycle003

section General
variable {K Γ G : Type} [Field K] [Group Γ] [Group G] {ι : Type} [Fintype ι]
  (s : ι → Γ) (c : ι → K) (i : G →* Γ) (hcomm : ∀ g k, i g * s k = s k * i g)
  (M : Rep K Γ)

/-- A commuting group acts on the ambient cokernel of the shifted operator. -/
noncomputable def shiftedCokernel : Rep K G :=
  Rep.quotient ((Action.res (ModuleCat K) i).obj M) (LinearMap.range (zOp s c M.ρ))
    (fun g => range_le_comap c (sequivariant_of_comm s M.ρ i hcomm g))

noncomputable def shiftedQuotientMap :
    (Action.res (ModuleCat K) i).obj M ⟶ shiftedCokernel s c i hcomm M :=
  Rep.mkQ _ _ _

instance shiftedQuotientMap_epi : Epi (shiftedQuotientMap s c i hcomm M) := by
  rw [Rep.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

/-- The shifted object is an actual subrepresentation of that ambient cokernel. -/
noncomputable def shiftedInclusion :
    scObj s c i hcomm M ⟶ shiftedCokernel s c i hcomm M where
  hom := ModuleCat.ofHom (sc s c M.ρ).subtype
  comm := fun g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro d
    rfl

instance shiftedInclusion_mono : Mono (shiftedInclusion s c i hcomm M) := by
  rw [Rep.mono_iff_injective]
  exact Subtype.val_injective

/-- Every annihilator condition passes from restriction to the shifted subquotient. -/
theorem shifted_annihilated (I : Set (MonoidAlgebra K G))
    (hM : AnnihilatedClass I ((Action.res (ModuleCat K) i).obj M)) :
    AnnihilatedClass I (scObj s c i hcomm M) :=
  annihilated_subobject I (shiftedInclusion s c i hcomm M)
    (annihilated_quotient I (shiftedQuotientMap s c i hcomm M) hM)
end General

variable {K : Type} [Field K] {n N r : ℕ} {ι : Type} [Fintype ι]

/-- No stability or characteristic assumptions are required for object preservation. -/
theorem canonical_shifted (h : n ≤ N) (s : ι → Sfin N) (c : ι → K)
    (hcomm : ∀ g k, rankIncl h g * s k = s k * rankIncl h g)
    (M : Rep K (Sfin N)) (hM : CanonicalClass K r N M) :
    CanonicalClass K r n (scObj s c (rankIncl h) hcomm M) :=
  shifted_annihilated s c (rankIncl h) hcomm M (TupleRelations K r n)
    (canonical_restrict h r M hM)

/-- Object preservation for the exact functor used by Stage 5's endpoint. -/
theorem canonical_Ψhat (p a n r : ℕ) [Fact p.Prime] (c : Fin a → K)
    (M : Rep K (Sfin (n + p ^ a))) (hM : CanonicalClass K r (n + p ^ a) M) :
    CanonicalClass K r n ((DegreeProfilesReview.ShiftedM5.Ψhat p a n c).obj M) :=
  canonical_shifted (Nat.le_add_right n (p ^ a)) (DegreeProfilesReview.ShiftedM5.σgen p a n)
    c (DegreeProfilesReview.ShiftedM5.hcommΨ p a n) M hM

/-- The actual functor between the canonical categories, with object preservation proved. -/
noncomputable def canonicalΨ (p a n r : ℕ) [Fact p.Prime] (c : Fin a → K) :=
  DegreeProfilesReview.ShiftedM5.Ψ (canonicalSchurClass K r (n + p ^ a))
    (canonicalSchurClass K r n) (canonical_Ψhat p a n r c)

/-- The narrowed M5 interface, now with concrete classes and no object-preservation premise.
The genuine characteristic, genericity and strict support hypotheses are retained. -/
noncomputable def canonicalM5w {p a n r : ℕ} [Fact p.Prime] [CharP K p]
    {c : Fin a → K} (hc : Generic p c) (hrq : r < p ^ a) :=
  DegreeProfilesReview.ShiftedM5.toM5w hc hrq
    (canonicalSchurClass K r (n + p ^ a)) (canonicalSchurClass K r n)
    (canonical_Ψhat p a n r c)

end SelfContainedCycle004
