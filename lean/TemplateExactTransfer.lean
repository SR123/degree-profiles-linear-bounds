/- Cycle 013: actual-template transfer from exactness, without equivalence. -/
import MinimalTransfer
import DegreeProfilesReview.WeakInterface
import Mathlib.Algebra.Category.ModuleCat.Simple

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace SelfContainedCycle013
open DegreeProfilesReview.Uniform DegreeProfilesReview.Deletion
open DegreeProfilesReview.Transport

universe v vR u uR
variable {K : Type} [Field K] {r t : ℕ}
variable {B : Type u} [Category.{v} B] [Abelian B]

/-- Simplicity descends along a faithful exact underlying-space functor. -/
theorem simple_of_simple_underlying (F : B ⥤ ModuleCat.{0} K)
    [F.Faithful] [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    {S : B} [Simple (F.obj S)] : Simple S where
  mono_isIso_iff_nonzero f _ := by
    constructor
    · intro hf hz
      haveI := hf
      have hn := (Simple.mono_isIso_iff_nonzero (F.map f)).mp (by infer_instance)
      exact hn (by rw [hz, F.map_zero])
    · intro hf
      have hn : F.map f ≠ 0 := by
        intro h
        exact hf (F.zero_of_map_zero f h)
      haveI : IsIso (F.map f) := isIso_of_mono_of_nonzero hn
      haveI : Epi f := Functor.epi_of_epi_map F (by infer_instance)
      exact isIso_of_mono_of_epi f

/-- The actual constant object of every M4 realization is simple. -/
theorem unit_simple (P : M4.{v, vR, u, uR} K r t B) :
    Simple (P.perm BasisSystem.unit (BasisSystem.unit_bounded r)) := by
  haveI : Simple (ModuleCat.of K K) := inferInstance
  haveI : Simple (P.ω.obj (P.perm BasisSystem.unit (BasisSystem.unit_bounded r))) :=
    Simple.of_iso (P.basis _ _ ≪≫ (Template.unitEquiv (K := K) t).toModuleIso)
  exact simple_of_simple_underlying P.ω

section Transfer
variable {N n : ℕ} (T : Template K) {d : ℕ}
variable {BN Bn : Type 1} [Category.{0} BN] [Abelian BN] [Category.{0} Bn] [Abelian Bn]
variable {PN : M4.{0, 0, 1, 1} K (T.k*d+T.s) N BN}
variable {Pn : M4.{0, 0, 1, 1} K (T.k*d+T.s) n Bn} {F : BN ⥤ Bn}

/-- This source survives under the actual M5 comparison with the smaller constant. -/
theorem shifted_unit_nonzero (m5 : M5w.{0, 0, 0, 1, 1, 1} PN Pn F) :
    ¬ IsZero (F.obj (PN.perm BasisSystem.unit (BasisSystem.unit_bounded _))) := by
  haveI := unit_simple Pn
  intro h
  exact Simple.not_isZero _ (h.of_iso (m5.δ _ _).symm)

variable [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Actual ordinary-PC refutability transfers from exactness and the constructed M5 data. -/
theorem template_pc_step_exact (hd : 1 ≤ d) (hN : T.n0 ≤ N) (hn : T.n0 ≤ n)
    (m5 : M5w.{0, 0, 0, 1, 1, 1} PN Pn F) :
    DegreeProfilesReview.PC.Refutes (T.inst N) d ↔
      DegreeProfilesReview.PC.Refutes (T.inst n) d := by
  haveI : Simple (T.catDatum hd PN).U := unit_simple PN
  rw [DegreeProfilesReview.PC.refutes_iff_one_mem_Vinf,
    DegreeProfilesReview.PC.refutes_iff_one_mem_Vinf,
    DegreeProfilesReview.PC.mem_Vinf_iff, DegreeProfilesReview.PC.mem_Vinf_iff]
  apply exists_congr
  intro j
  rw [← T.pc_stage_iff hd PN hN j, ← T.pc_stage_iff hd Pn hn j]
  exact ExactnessHandoff.const_mem_iff_of_simple F (shifted_unit_nonzero T m5)
    (T.ΦCompatW hd m5) j

/-- Actual NS refutability transfers with the same smaller input. -/
theorem template_ns_step_exact (hN : T.n0 ≤ N) (hn : T.n0 ≤ n)
    (m5 : M5w.{0, 0, 0, 1, 1, 1} PN Pn F) :
    DegreeProfilesReview.NS.NSRefutes (T.inst N) d ↔
      DegreeProfilesReview.NS.NSRefutes (T.inst n) d := by
  haveI := unit_simple PN
  rw [DegreeProfilesReview.NS.nsRefutes_iff_one_mem_NSspan,
    DegreeProfilesReview.NS.nsRefutes_iff_one_mem_NSspan,
    ← T.ns_iff PN hN, ← T.ns_iff Pn hn]
  exact ExactnessHandoff.image_membership_iff_of_simple F (shifted_unit_nonzero T m5)
    _ _ _ _ (m5.δ _ _) (m5.δ _ _) (m5.δ _ _)
    (m5.δ_mat _ _ _) (m5.δ_mat _ _ _)

end Transfer
end SelfContainedCycle013
