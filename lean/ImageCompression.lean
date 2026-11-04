/- Cycle 009: turn proved coordinate identities into an algebra-action inner inverse. -/
import PolynomialInnerInverse

set_option autoImplicit false
namespace SelfContainedCycle009
open SelfContainedCycle008

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Only reconstruction on image(z) is needed; no invertibility of an ambient map. -/
theorem compressed_image_injective (z a : Module.End K V)
    (E : W →ₗ[K] V) (L : V →ₗ[K] W) (B : Module.End K W)
    (hz : E.comp (L.comp z) = z)
    (hb : L.comp ((z*a).comp E) = B) (hi : Function.Injective B) :
    Function.Injective (imageStep z a) := by
  have he (x : LinearMap.range z) : E (L x) = x := by
    obtain ⟨v, hv⟩ := x.2
    rw [← hv]
    exact LinearMap.congr_fun hz v
  intro x y hxy
  have hval := congrArg (fun v : LinearMap.range z => L v) hxy
  have hB : B (L x) = B (L y) := by
    rw [← hb]
    change L (z (a (E (L x)))) = L (z (a (E (L y))))
    simpa only [he] using hval
  apply Subtype.ext
  have hL := hi hB
  simpa only [he] using congrArg E hL

/-- The same group-algebra expression works in this action, without algebra faithfulness.
The actual coordinate identities must be proved before this lemma can be applied. -/
theorem action_innerInverse_of_compression {A : Type} [Ring A] [Algebra K A]
    [FiniteDimensional K V] (ρ : A →ₐ[K] Module.End K V) (z a : A)
    (E : W →ₗ[K] V) (L : V →ₗ[K] W) (B : Module.End K W)
    (hz : E.comp (L.comp (ρ z)) = ρ z)
    (hb : L.comp ((ρ z*ρ a).comp E) = B) (hi : Function.Injective B) :
    ∃ b : A, ρ z * ρ b * ρ z = ρ z := by
  have hj := compressed_image_injective (ρ z) (ρ a) E L B hz hb hi
  obtain ⟨P,h0,hP⟩ := imageStep_polynomial (ρ z) (ρ a) hj
  exact ⟨polynomialInverse z a P, polynomial_action_innerInverse ρ z a P h0 hP⟩

end SelfContainedCycle009
