/- The finite normalization has actual group-algebra instances. -/
import ResidualSplitting
import Mathlib.Algebra.MonoidAlgebra.Basic

set_option autoImplicit false
namespace SelfContainedCycle017

variable {K G : Type*} [Field K] [Finite K] [Group G] [Finite G]

/-- Actual finite-group algebra: no matrix inverse is substituted for an algebra element. -/
theorem groupAlgebra_adjustment (z a : MonoidAlgebra K G) :
    ∃ k : ℕ, 0 < k ∧ adjusted z a k*z*adjusted z a k=adjusted z a k := by
  letI : Finite (MonoidAlgebra K G) := Finite.of_injective
    (fun f : MonoidAlgebra K G => (f : G → K))
    (by intro f g h; ext x; exact congrFun h x)
  exact finite_adjustment z a

/-- The SAME normalized element preserves a smaller representation's relation,
    while every larger representation has a split residual whenever Z has
    a position-equivariant auxiliary inverse there. -/
theorem normalized_two_representations
    {S T : Type*} [Ring S] [Ring T]
    (ρ : MonoidAlgebra K G →+* S) (τ : MonoidAlgebra K G →+* T)
    (z a : MonoidAlgebra K G) (hsmall : ρ z*ρ a*ρ z=ρ z)
    (d : T) (hd : τ z*d*τ z=τ z) :
    ∃ k : ℕ, 0 < k ∧
      ρ z*ρ (adjusted z a k)*ρ z=ρ z ∧
      residual (τ z) (τ (adjusted z a k))*d*
        residual (τ z) (τ (adjusted z a k)) =
          residual (τ z) (τ (adjusted z a k)) := by
  obtain ⟨k,hk,hb⟩ := groupAlgebra_adjustment z a
  refine ⟨k,hk,adjusted_preserves_representation ρ z a hsmall k,?_⟩
  apply residual_inner _ _ d _ hd
  simpa only [map_mul] using congrArg τ hb

end SelfContainedCycle017
