/- Cycle 013: exactness transports through natural idempotent range models. -/
import HomologyProjection
import Mathlib.Algebra.Exact

set_option autoImplicit false
namespace SelfContainedCycle013
variable {K X Y Z A B C : Type} [Field K]
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
variable [AddCommGroup Z] [Module K Z] [AddCommGroup A] [Module K A]
variable [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

/-- The range restriction of a natural idempotent preserves exact sequences.
    The model maps and their compatibility are explicit; no categorical equivalence is used. -/
theorem exact_of_projector_models (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (F : A →ₗ[K] B) (G : B →ₗ[K] C) (pX : Module.End K X)
    (pY : Module.End K Y) (pZ : Module.End K Z)
    (eX : A ≃ₗ[K] LinearMap.range pX) (eY : B ≃ₗ[K] LinearMap.range pY)
    (eZ : C ≃ₗ[K] LinearMap.range pZ)
    (hidem : pY*pY=pY) (hpf : ∀ x, f (pX x)=pY (f x))
    (hF : ∀ x, (eY (F x) : Y)=f (eX x))
    (hG : ∀ y, (eZ (G y) : Z)=g (eY y)) (hex : Function.Exact f g) :
    Function.Exact F G := by
  intro y
  constructor
  · intro hy
    have hk : g (eY y)=0 := by
      rw [← hG,hy,map_zero]
      rfl
    obtain ⟨x,hx⟩ := (hex _).mp hk
    refine ⟨eX.symm ⟨pX x,⟨x,rfl⟩⟩, ?_⟩
    apply eY.injective
    apply Subtype.ext
    rw [hF,eX.apply_symm_apply]
    change f (pX x)=(eY y : Y)
    rw [hpf,hx]
    obtain ⟨v,hv⟩ := (eY y).2
    rw [← hv]
    exact congrArg (fun L : Module.End K Y => L v) hidem
  · rintro ⟨x,rfl⟩
    apply eZ.injective
    apply Subtype.ext
    rw [hG,hF,map_zero]
    exact (hex _).mpr ⟨(eX x : X),rfl⟩

end SelfContainedCycle013
