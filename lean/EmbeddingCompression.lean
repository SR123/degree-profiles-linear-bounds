/- Cycle 010: reflect image-step injectivity through a compatible injective embedding. -/
import ImageCompression

set_option autoImplicit false
namespace SelfContainedCycle010
open SelfContainedCycle008
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem imageStep_injective_of_embedding (z a : Module.End K V) (Z A : Module.End K W)
    (J : V →ₗ[K] W) (hJ : Function.Injective J)
    (hz : ∀ v, J (z v) = Z (J v)) (ha : ∀ v, J (a v) = A (J v))
    (hi : Function.Injective (imageStep Z A)) : Function.Injective (imageStep z a) := by
  let R : LinearMap.range z → LinearMap.range Z := fun x =>
    ⟨J x, by
      obtain ⟨v,hv⟩ := x.2
      refine ⟨J v, ?_⟩
      rw [← hz, hv]⟩
  intro x y hxy
  have hv : Z (A (J x)) = Z (A (J y)) := by
    rw [← ha, ← hz, ← ha, ← hz]
    exact congrArg J (congrArg (fun v : LinearMap.range z => (v : V)) hxy)
  have hR : imageStep Z A (R x) = imageStep Z A (R y) := Subtype.ext hv
  apply Subtype.ext
  apply hJ
  exact congrArg (fun v : LinearMap.range Z => (v : W)) (hi hR)

end SelfContainedCycle010
