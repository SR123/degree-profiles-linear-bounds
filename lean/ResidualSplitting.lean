/- Cycle 017: a normalized partial inverse leaves a split residual.
   The splitting is auxiliary; membership in a permutation action algebra
   must still be obtained using the separate bin-compression argument. -/
import ReflexiveAdjustment

set_option autoImplicit false
namespace SelfContainedCycle017
variable {R : Type*} [Ring R]

def residual (z b : R) : R := z-z*b*z

/-- Outer normalization is the missing hypothesis in the failed raw recursion. -/
theorem residual_inner (z b d : R) (hb : b*z*b=b) (hd : z*d*z=z) :
    residual z b*d*residual z b = residual z b := by
  have h : (z-z*b*z)*d*(z-z*b*z) =
      z*d*z-z*b*(z*d*z)-(z*d*z)*b*z+z*b*(z*d*z)*b*z := by noncomm_ring
  unfold residual
  rw [h,hd]
  have hbb : z*b*z*b*z=z*b*z := by
    calc
      z*b*z*b*z = z*(b*z*b)*z := by noncomm_ring
      _ = z*b*z := by rw [hb]
  rw [hbb]
  abel

theorem residual_sq (z b : R) (hz : z*z=0) : residual z b*residual z b=0 := by
  have h : (z-z*b*z)*(z-z*b*z) = z*z-z*b*(z*z)-(z*z)*b*z+z*b*(z*z)*b*z := by noncomm_ring
  simp [residual,h,hz]

theorem residual_commute (z b s : R) (hz : Commute z s) (hb : Commute b s) :
    Commute (residual z b) s := hz.sub_left ((hz.mul_left hb).mul_left hz)

theorem residual_projector (z b d : R) (hb : b*z*b=b) (hd : z*d*z=z) :
    IsIdempotentElem (residual z b*d) := by
  change residual z b*d*(residual z b*d)=residual z b*d
  rw [←mul_assoc,residual_inner z b d hb hd]

/-- The final correction remains a ring expression in the original data. -/
theorem residual_lift (z b c : R)
    (hc : residual z b*c*residual z b=residual z b) :
    z*(b+(1-b*z)*c*(1-z*b))*z=z := by
  have h : z*(b+(1-b*z)*c*(1-z*b))*z = z*b*z+residual z b*c*residual z b := by
    unfold residual; noncomm_ring
  rw [h,hc]
  simp [residual]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An explicit position-equivariant retraction onto the residual image. -/
def residualRetraction (z b d : Module.End K V) : V →ₗ[K] LinearMap.range (residual z b) where
  toFun v := ⟨residual z b (d v), ⟨d v,rfl⟩⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

theorem residualRetraction_subtype (z b d : Module.End K V)
    (hb : b*z*b=b) (hd : z*d*z=z) :
    (residualRetraction z b d).comp (LinearMap.range (residual z b)).subtype = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨v,w,rfl⟩
  apply Subtype.ext
  exact congrArg (fun f : Module.End K V => f w) (residual_inner z b d hb hd)

theorem residual_projector_commute (z b d s : R)
    (hz : Commute z s) (hb : Commute b s) (hd : Commute d s) :
    Commute (residual z b*d) s := (residual_commute z b s hz hb).mul_left hd

/-- Localized residuals use the actual inclusion/projection compression. -/
theorem compression_inner
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (i : Q →ₗ[K] V) (p : V →ₗ[K] Q)
    (y c : Module.End K V) (y₀ d : Module.End K Q)
    (hy : y = i.comp (y₀.comp p)) (hc : p.comp (c.comp i)=d)
    (hd : y₀*d*y₀=y₀) : y*c*y=y := by
  apply LinearMap.ext
  intro v
  have hh := congrArg (fun f : Module.End K Q => f (p v)) hd
  have hh' (w : Q) : p (c (i w))=d w := congrArg (fun f : Module.End K Q => f w) hc
  change y (c (y v))=y v
  simp only [hy,LinearMap.comp_apply,hh']
  exact congrArg i hh

end SelfContainedCycle017
