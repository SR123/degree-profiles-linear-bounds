/- Cycle 012: identify Stage 5's actual shifted quotient and its compressed residual action. -/
import HomologyProjection
import DegreeProfilesReview.ShiftedFunctor

set_option autoImplicit false
open CategoryTheory
namespace SelfContainedCycle012
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor
variable {K Γ G ι V W : Type} [Field K] [Group Γ] [Group G] [Fintype ι]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (s : ι → Γ) (c : ι → K) (ρ : Representation K Γ V)
  (b : Module.End K V) (hz : zOp s c ρ*zOp s c ρ=0) (hb : zOp s c ρ*b*zOp s c ρ=zOp s c ρ)

def scProjectionEquiv : sc s c ρ ≃ₗ[K] LinearMap.range (homologyProjector (zOp s c ρ) b) :=
  homologyEquiv (zOp s c ρ) b hz hb

@[simp] theorem scProjectionEquiv_mk (v : V) (hv : v ∈ LinearMap.ker (zOp s c ρ)) :
    (scProjectionEquiv s c ρ b hz hb (scMk s c ρ v hv) : V)=homologyProjector (zOp s c ρ) b v := rfl

/-- Naturality is for the original quotient map, with explicit common-witness compatibility. -/
theorem scProjection_natural (σ : Representation K Γ W) (b' : Module.End K W)
    (hz' : zOp s c σ*zOp s c σ=0) (hb' : zOp s c σ*b'*zOp s c σ=zOp s c σ)
    (f : V →ₗ[K] W) (hf : SEquivariant s ρ σ f) (hfb : ∀ v, f (b v)=b' (f v))
    (d : sc s c ρ) :
    (scProjectionEquiv s c σ b' hz' hb' (scMap c f hf d) : W) =
      f (scProjectionEquiv s c ρ b hz hb d) := by
  obtain ⟨v,hv,rfl⟩ := sc_induction s c ρ d
  rw [scMap_scMk,scProjectionEquiv_mk,scProjectionEquiv_mk]
  exact (projector_natural (zOp s c ρ) b (zOp s c σ) b' f (hf.zOp_comm c) hfb v).symm

variable (i : G →* Γ) (hcomm : ∀ g k, i g*s k=s k*i g)

/-- Transport is defined from the proved equivalence and original residual representation. -/
def scProjectedRep : Representation K G (LinearMap.range (homologyProjector (zOp s c ρ) b)) :=
  ((scProjectionEquiv s c ρ b hz hb).conjRingEquiv.toMonoidHom).comp (scRep s c ρ i hcomm)

/-- The actual transported action is p h p on pV; b and p need not commute with h. -/
theorem scProjectedRep_apply (g : G) (x : LinearMap.range (homologyProjector (zOp s c ρ) b)) :
    (scProjectedRep s c ρ b hz hb i hcomm g x : V) =
      homologyProjector (zOp s c ρ) b (ρ (i g) x) := by
  change (scProjectionEquiv s c ρ b hz hb
    (scRep s c ρ i hcomm g ((scProjectionEquiv s c ρ b hz hb).symm x)) : V)=_
  have hi : (scProjectionEquiv s c ρ b hz hb).symm x =
      scMk s c ρ x (range_projector_in_ker (zOp s c ρ) b hz hb x) := rfl
  rw [hi,scRep_scMk,scProjectionEquiv_mk]

theorem scProjection_equivariant (g : G) (d : sc s c ρ) :
    scProjectionEquiv s c ρ b hz hb (scRep s c ρ i hcomm g d) =
      scProjectedRep s c ρ b hz hb i hcomm g (scProjectionEquiv s c ρ b hz hb d) := by
  change _ = scProjectionEquiv s c ρ b hz hb
    (scRep s c ρ i hcomm g ((scProjectionEquiv s c ρ b hz hb).symm
      (scProjectionEquiv s c ρ b hz hb d)))
  rw [LinearEquiv.symm_apply_apply]

end SelfContainedCycle012
