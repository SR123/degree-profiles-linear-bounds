/-
Uniform consequences, Claude return 001 (5 October 2026).  Audit file.

Prints the definitions the endpoints depend on, the endpoint statements, their axioms, and
transitive-dependency checks (`#uses`, from the preserved `UDeps`).
-/
import UCExample
import UDeps

set_option autoImplicit false

open UniformConsequence UniformConsequence.Target

/-! ### Definitions -/

#print UniformConsequence.Target
#print UniformConsequence.Target.poly
#print UniformConsequence.Target.auxT
#print UniformConsequence.Target.deg
#print UniformConsequence.Target.nG
#print UniformConsequence.Target.nstar
#print UniformConsequence.Target.targetM
#print UniformConsequence.Target.Gtr
#print UniformConsequence.Target.targetMap
#print UniformConsequence.Target.concDatumG
#print UniformConsequence.Target.catDatumG
#print UniformConsequence.Target.ΦCompatGW
#print UniformConsequence.Target.ZeroDerivable
#print UniformConsequence.Target.pcProfile
#print UniformConsequence.Target.nsProfile
#print UniformConsequence.NSDerives
#print UniformConsequence.NSDerivesAdd
#print UniformConsequence.tpcDegree
#print UniformConsequence.tnsDegree
#print DegreeProfilesReview.PC.Derives
#print DegreeProfilesReview.PC.IsProof
#print DegreeProfilesReview.PC.Vinf
#print DegreeProfilesReview.NS.NSspan
#print DegreeProfilesReview.Uniform.Template.inst
#print DegreeProfilesReview.Uniform.LinearBoundsFor
#print DegreeProfilesReview.Profiles.PeriodicProfile
#print DegreeProfilesReview.Profiles.ThresholdPeriodic
#print DegreeProfilesReview.Profiles.onset
#print DegreeProfilesReview.Profiles.period
#print DegreeProfilesReview.Profiles.E
#print DegreeProfilesReview.Profiles.IsT1
#print DegreeProfilesReview.Profiles.IsT2
#print DegreeProfilesReview.Profiles.IsT3
#print DegreeProfilesReview.Profiles.IsT4
#print DegreeProfilesReview.Profiles.UpperComparison
#print ClaudeLinear.ExactnessHypothesis
#print ClaudeLinear.ShiftedExact

/-! ### Endpoint statements -/

#check @UniformConsequence.target_transfer
#check @UniformConsequence.target_transfer_derivations
#check @UniformConsequence.target_transfer_paper_range
#check @UniformConsequence.Target.target_step_of_exact
#check @UniformConsequence.Target.target_pc_step_exact
#check @UniformConsequence.Target.target_ns_step_exact
#check @UniformConsequence.Target.targetM_realise
#check @UniformConsequence.Target.targetM_transport
#check @UniformConsequence.Target.Gtr_coe
#check @UniformConsequence.Target.totalDegree_poly
#check @UniformConsequence.Target.not_mem_of_lt
#check @UniformConsequence.Target.mem_V0_zero_iff
#check @UniformConsequence.Target.pc_target_stage_iff
#check @UniformConsequence.Target.ns_target_iff
#check @UniformConsequence.nsDerives_iff_mem_NSspan
#check @UniformConsequence.nsDerivesAdd_iff_mem_NSspan
#check @UniformConsequence.mem_Vinf_map_iff
#check @UniformConsequence.mem_NSspan_map_iff
#check @UniformConsequence.uniform_inclusion
#check @UniformConsequence.uniform_derivation_comparison
#check @UniformConsequence.Target.profile_step
#check @UniformConsequence.Target.periodic_pc
#check @UniformConsequence.Target.periodic_ns
#check @UniformConsequence.Target.linearBounds_pc
#check @UniformConsequence.Target.linearBounds_ns
#check @UniformConsequence.Target.liminf_classification
#check @UniformConsequence.Target.upperComparison
#check @UniformConsequence.Target.types_agree
#check @UniformConsequence.Target.common_peaks
#check @UniformConsequence.Target.deg_le_pcProfile
#check @UniformConsequence.Target.profiles_of_γ_zero
#check @UniformConsequence.invariant_target_endpoint
#check @UniformConsequence.Example.unitAxioms_profiles
#check @UniformConsequence.Example.noAxioms_profiles
#check @UniformConsequence.Example.example_types
#check @UniformConsequence.tpcDegree_one
#check @UniformConsequence.tnsDegree_one

/-! ### Axioms -/

#print axioms UniformConsequence.target_transfer
#print axioms UniformConsequence.target_transfer_derivations
#print axioms UniformConsequence.target_transfer_paper_range
#print axioms UniformConsequence.Target.target_step_of_exact
#print axioms UniformConsequence.Target.targetM_realise
#print axioms UniformConsequence.Target.targetM_transport
#print axioms UniformConsequence.Target.Gtr_coe
#print axioms UniformConsequence.Target.totalDegree_poly
#print axioms UniformConsequence.Target.mem_V0_zero_iff
#print axioms UniformConsequence.nsDerives_iff_mem_NSspan
#print axioms UniformConsequence.nsDerivesAdd_iff_mem_NSspan
#print axioms UniformConsequence.mem_Vinf_map_iff
#print axioms UniformConsequence.mem_NSspan_map_iff
#print axioms UniformConsequence.uniform_inclusion
#print axioms UniformConsequence.uniform_derivation_comparison
#print axioms UniformConsequence.Target.linearBounds_pc
#print axioms UniformConsequence.Target.linearBounds_ns
#print axioms UniformConsequence.Target.liminf_classification
#print axioms UniformConsequence.Target.types_agree
#print axioms UniformConsequence.Target.common_peaks
#print axioms UniformConsequence.Target.deg_le_pcProfile
#print axioms UniformConsequence.invariant_target_endpoint
#print axioms UniformConsequence.Example.unitAxioms_profiles
#print axioms UniformConsequence.Example.noAxioms_profiles
#print axioms UniformConsequence.Example.example_types

/-! ### Transitive dependencies -/

-- the unconditional exactness input and its proof of FORCE are on the path
#uses UniformConsequence.target_transfer LinearFinal.exactness_linear
#uses UniformConsequence.target_transfer RForce.forceExists
#uses UniformConsequence.target_transfer SelfContainedCycle004.canonicalM5w
#uses UniformConsequence.target_transfer DegreeProfilesReview.Deletion.M5w.δ_mat
#uses UniformConsequence.target_transfer ExactnessHandoff.const_mem_iff_of_simple
#uses UniformConsequence.target_transfer ExactnessHandoff.image_membership_iff_of_simple
#uses UniformConsequence.target_transfer DegreeProfilesReview.FieldDescent.pc_derives_map_iff
-- the comparison uses the unconditional chain bound and the C017 plateau lemma
#uses UniformConsequence.invariant_target_endpoint ClaudeComparison.chainBound
#uses UniformConsequence.invariant_target_endpoint ClaudeC017.Vinf_le_of_stable
-- no sorry, and no historical hypothesis interface is an unproved premise of an endpoint
#uses UniformConsequence.invariant_target_endpoint sorryAx
#uses UniformConsequence.target_transfer sorryAx
#uses UniformConsequence.Example.example_types sorryAx
#uses UniformConsequence.invariant_target_endpoint DegreeProfilesReview.Uniform.DeletionHypothesis
#uses UniformConsequence.invariant_target_endpoint DegreeProfilesReview.Uniform.DeletionHypothesisW
#uses UniformConsequence.invariant_target_endpoint ForceInterface.ForceExists
-- `ForceExists` is the statement proved by `RForce.forceExists` (Theorem A of the forcing
-- proof); it occurs in the closure as a proved proposition, not as a premise of the endpoint.
-- The target data are the existing data with the distinguished map REPLACED; the old constant
-- matrix stays in the closure only through the unchanged fields (definitional checks below).
#uses UniformConsequence.Target.target_pc_step_exact DegreeProfilesReview.Uniform.Template.constM
#check @UniformConsequence.Target.catDatumG_c
#check @UniformConsequence.Target.concDatumG_c
#print axioms UniformConsequence.Target.catDatumG_c
