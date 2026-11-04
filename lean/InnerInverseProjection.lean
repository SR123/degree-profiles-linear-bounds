/- Cycle 012: a square-zero inner inverse gives a homology projection. -/
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Ring.Commute

set_option autoImplicit false
namespace SelfContainedCycle012
variable {A : Type*} [Ring A]

def normalInverse (z b : A) : A := (b*z)*b*(1-b*z)
def homologyProjector (z b : A) : A := 1-normalInverse z b*z-z*normalInverse z b

variable (z b : A)

theorem bz_idempotent (hb : z*b*z=z) : (b*z)*(b*z)=b*z := by
  calc
    (b*z)*(b*z)=b*(z*b*z) := by noncomm_ring
    _=b*z := by rw [hb]

theorem bz_mul_z (hz : z*z=0) : (b*z)*z=0 := by rw [mul_assoc,hz,mul_zero]

theorem z_mul_bz (hb : z*b*z=z) : z*(b*z)=z := by rw [← mul_assoc,hb]

theorem normalInverse_mul_z (hz : z*z=0) (hb : z*b*z=z) : normalInverse z b*z=b*z := by
  unfold normalInverse
  rw [mul_assoc _ _ z,sub_mul,one_mul,bz_mul_z z b hz,sub_zero,mul_assoc]
  exact bz_idempotent z b hb

theorem z_normalInverse_z (hz : z*z=0) (hb : z*b*z=z) : z*normalInverse z b*z=z := by
  rw [mul_assoc,normalInverse_mul_z z b hz hb,z_mul_bz z b hb]

theorem normalInverse_sq (hb : z*b*z=z) : normalInverse z b*normalInverse z b=0 := by
  have he : (1-b*z)*(b*z)=0 := by
    rw [sub_mul,one_mul,bz_idempotent z b hb,sub_self]
  calc
    normalInverse z b*normalInverse z b =
      ((b*z)*b)*((1-b*z)*(b*z))*b*(1-b*z) := by unfold normalInverse; noncomm_ring
    _=0 := by rw [he]; simp

theorem normalInverse_z_normalInverse (hz : z*z=0) (hb : z*b*z=z) : normalInverse z b*z*normalInverse z b=normalInverse z b := by
  rw [normalInverse_mul_z z b hz hb]
  unfold normalInverse
  rw [← mul_assoc,← mul_assoc,bz_idempotent z b hb]

theorem projector_mul_z (hz : z*z=0) (hb : z*b*z=z) : homologyProjector z b*z=0 := by
  unfold homologyProjector
  rw [sub_mul,sub_mul,one_mul,mul_assoc _ z z,hz,mul_zero,
    z_normalInverse_z z b hz hb,sub_zero,sub_self]

theorem z_mul_projector (hz : z*z=0) (hb : z*b*z=z) : z*homologyProjector z b=0 := by
  unfold homologyProjector
  rw [mul_sub,mul_sub,mul_one,← mul_assoc,z_normalInverse_z z b hz hb,
    ← mul_assoc z z,hz,zero_mul,sub_self,sub_zero]

theorem projector_idempotent (hz : z*z=0) (hb : z*b*z=z) : homologyProjector z b*homologyProjector z b=homologyProjector z b := by
  have hc := normalInverse_sq z b hb
  have hzc := z_normalInverse_z z b hz hb
  have hcz := normalInverse_z_normalInverse z b hz hb
  have he : (normalInverse z b*z)*(normalInverse z b*z)=normalInverse z b*z := by
    rw [← mul_assoc, hcz]
  have hf : (z*normalInverse z b)*(z*normalInverse z b)=z*normalInverse z b := by
    rw [← mul_assoc,hzc]
  have hef : (normalInverse z b*z)*(z*normalInverse z b)=0 := by
    rw [mul_assoc,← mul_assoc z z,hz,zero_mul,mul_zero]
  have hfe : (z*normalInverse z b)*(normalInverse z b*z)=0 := by
    rw [mul_assoc,← mul_assoc _ _ z,hc,zero_mul,mul_zero]
  calc
    homologyProjector z b*homologyProjector z b =
      1-2•(normalInverse z b*z)-2•(z*normalInverse z b)+
      (normalInverse z b*z)*(normalInverse z b*z)+
      (normalInverse z b*z)*(z*normalInverse z b)+
      (z*normalInverse z b)*(normalInverse z b*z)+
      (z*normalInverse z b)*(z*normalInverse z b) := by unfold homologyProjector; noncomm_ring
    _=homologyProjector z b := by rw [he,hf,hef,hfe]; unfold homologyProjector; noncomm_ring


/-- Multiplication of compressed operators; b need not commute with h or k. -/
theorem compressed_mul (hz : z*z=0) (hb : z*b*z=z) (h k : A)
    (hh : h*z=z*h) (hk : k*z=z*k) :
    (homologyProjector z b*h*homologyProjector z b)*
      (homologyProjector z b*k*homologyProjector z b) =
        homologyProjector z b*h*k*homologyProjector z b := by
  let p := homologyProjector z b
  let c := normalInverse z b
  have hp : p*p=p := projector_idempotent z b hz hb
  have hpz : p*z=0 := projector_mul_z z b hz hb
  have hzp : z*p=0 := z_mul_projector z b hz hb
  have h1 : p*h*c*z*k*p=0 := by
    calc
      p*h*c*z*k*p = p*h*c*(z*k)*p := by noncomm_ring
      _ = p*h*c*(k*z)*p := by rw [hk]
      _ = p*h*c*k*(z*p) := by noncomm_ring
      _ = 0 := by rw [hzp]; simp
  have h2 : p*h*z*c*k*p=0 := by
    calc
      p*h*z*c*k*p = p*(h*z)*c*k*p := by noncomm_ring
      _ = p*(z*h)*c*k*p := by rw [hh]
      _ = (p*z)*h*c*k*p := by noncomm_ring
      _ = 0 := by rw [hpz]; simp
  change (p*h*p)*(p*k*p)=p*h*k*p
  calc
    (p*h*p)*(p*k*p)=p*h*(p*p)*k*p := by noncomm_ring
    _=p*h*p*k*p := by rw [hp]
    _=p*h*(1-c*z-z*c)*k*p := rfl
    _=p*h*k*p-p*h*c*z*k*p-p*h*z*c*k*p := by noncomm_ring
    _=p*h*k*p := by rw [h1,h2]; simp

end SelfContainedCycle012
