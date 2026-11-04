/- Cycle 012: actual quotient maps and a natural projection onto homology. -/
import InnerInverseProjection
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false
namespace SelfContainedCycle012
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

abbrev homology (z : Module.End K V) : Submodule K (V ⧸ LinearMap.range z) :=
  (LinearMap.ker z).map (LinearMap.range z).mkQ

def homologyMk (z : Module.End K V) (v : V) (hv : z v=0) : homology z :=
  ⟨(LinearMap.range z).mkQ v, Submodule.mem_map_of_mem hv⟩

theorem homology_induction (z : Module.End K V) (d : homology z) :
    ∃ v hv, d=homologyMk z v hv := by
  obtain ⟨_,⟨v,hv,rfl⟩⟩ := d
  exact ⟨v,hv,rfl⟩

variable (z b : Module.End K V) (hz : z*z=0) (hb : z*b*z=z)
include hz hb

def homologyLift : V ⧸ LinearMap.range z →ₗ[K] LinearMap.range (homologyProjector z b) :=
  (LinearMap.range z).liftQ (homologyProjector z b).rangeRestrict (by
    rintro _ ⟨v,rfl⟩
    apply Subtype.ext
    exact congrArg (fun L : Module.End K V => L v) (projector_mul_z z b hz hb))

def homologyToRange : homology z →ₗ[K] LinearMap.range (homologyProjector z b) :=
  (homologyLift z b hz hb).comp (homology z).subtype

@[simp] theorem homologyToRange_mk (v : V) (hv : z v=0) :
    (homologyToRange z b hz hb (homologyMk z v hv) : V) = homologyProjector z b v := rfl

theorem range_projector_in_ker (x : LinearMap.range (homologyProjector z b)) : z x=0 := by
  obtain ⟨v,hv⟩ := x.2
  rw [← hv]
  exact congrArg (fun L : Module.End K V => L v) (z_mul_projector z b hz hb)

def rangeToHomology : LinearMap.range (homologyProjector z b) →ₗ[K] homology z :=
  (((LinearMap.range z).mkQ).comp (LinearMap.range (homologyProjector z b)).subtype).codRestrict
    (homology z) (fun x => Submodule.mem_map_of_mem (range_projector_in_ker z b hz hb x))

theorem rangeToHomology_eq (x : LinearMap.range (homologyProjector z b)) :
    rangeToHomology z b hz hb x = homologyMk z x (range_projector_in_ker z b hz hb x) := rfl

omit hz hb in
theorem projector_on_kernel (v : V) (hv : z v=0) :
    homologyProjector z b v = v-z (normalInverse z b v) := by
  simp only [homologyProjector,LinearMap.sub_apply,Module.End.one_apply,Module.End.mul_apply,
    hv,map_zero,sub_zero]

theorem homology_roundtrip (d : homology z) :
    rangeToHomology z b hz hb (homologyToRange z b hz hb d)=d := by
  obtain ⟨v,hv,rfl⟩ := homology_induction z d
  apply Subtype.ext
  change (LinearMap.range z).mkQ (homologyProjector z b v)=(LinearMap.range z).mkQ v
  rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq]
  refine ⟨-normalInverse z b v, ?_⟩
  rw [map_neg,projector_on_kernel z b v hv]
  abel

theorem range_roundtrip (x : LinearMap.range (homologyProjector z b)) :
    homologyToRange z b hz hb (rangeToHomology z b hz hb x)=x := by
  apply Subtype.ext
  change homologyProjector z b x=x
  obtain ⟨v,hv⟩ := x.2
  rw [← hv]
  exact congrArg (fun L : Module.End K V => L v) (projector_idempotent z b hz hb)

/-- A genuine linear equivalence defined using quotient maps and their explicit inverse. -/
def homologyEquiv : homology z ≃ₗ[K] LinearMap.range (homologyProjector z b) :=
  { homologyToRange z b hz hb with
    invFun := rangeToHomology z b hz hb
    left_inv := homology_roundtrip z b hz hb
    right_inv := range_roundtrip z b hz hb }

/-- A zero projector really annihilates the shifted quotient. -/
theorem homology_subsingleton_of_projector_zero (hp : homologyProjector z b=0) :
    Subsingleton (homology z) := by
  refine ⟨fun x y => (homologyEquiv z b hz hb).injective ?_⟩
  apply Subtype.ext
  have hx := ((homologyEquiv z b hz hb) x).2
  have hy := ((homologyEquiv z b hz hb) y).2
  simp only [hp,LinearMap.range_zero,Submodule.mem_bot] at hx hy
  exact hx.trans hy.symm

omit hz hb in
/-- Any map intertwining z and its chosen inverse also intertwines the same projector. -/
theorem projector_natural (z' b' : Module.End K W) (f : V →ₗ[K] W)
    (hfz : ∀ v, f (z v)=z' (f v)) (hfb : ∀ v, f (b v)=b' (f v)) (v : V) :
    f (homologyProjector z b v)=homologyProjector z' b' (f v) := by
  simp only [homologyProjector,normalInverse,LinearMap.sub_apply,Module.End.one_apply,
    Module.End.mul_apply,map_sub,hfz,hfb]

end SelfContainedCycle012
