/-
Uniform consequences, Claude return 002 (5 October 2026).  Audit file for Milestones 2 and 3
(indexed target profiles; fresh-variable finite-hard targets), with the Milestone 1 endpoints
repeated for completeness.
-/
import UCIndexedClassification
import UCFreshVariable
import UDeps

set_option autoImplicit false

open UniformConsequence UniformConsequence.Indexed UniformConsequence.Fresh

/-! ### Definitions -/

#print UniformConsequence.Indexed.ITarget.pcProfile
#print UniformConsequence.Indexed.ITarget.nsProfile
#print UniformConsequence.Indexed.ITarget.nI
#print DegreeProfilesReview.Uniform.LinearBoundsFor
#print DegreeProfilesReview.Profiles.PeriodicProfile
#print DegreeProfilesReview.Profiles.UpperComparison
#print DegreeProfilesReview.Profiles.E
#print DegreeProfilesReview.Profiles.IsT1
#print DegreeProfilesReview.Profiles.IsT2
#print DegreeProfilesReview.Profiles.IsT3
#print DegreeProfilesReview.Profiles.IsT4
#print UniformConsequence.tpcDegree
#print UniformConsequence.tnsDegree
#print DegreeProfilesReview.PC.pcDegree
#print DegreeProfilesReview.NS.nsDegree
#print UniformConsequence.Fresh.lift
#print UniformConsequence.Fresh.ysubst
#print UniformConsequence.Fresh.optionSys
#print UniformConsequence.Fresh.freshVar
#print UniformConsequence.Fresh.freshTarget
#print UniformConsequence.Fresh.yExp
#print ClaudeUndec.bhat

/-! ### Endpoint statements -/

-- Milestone 1
#check @UniformConsequence.Indexed.indexed_transfer
#check @UniformConsequence.Indexed.indexed_transfer_derivations
#check @UniformConsequence.Indexed.orbit_rep_transfer
-- Milestone 2
#check @UniformConsequence.Indexed.indexed_target_endpoint
#check @UniformConsequence.Indexed.orbit_endpoint
#check @UniformConsequence.Indexed.ITarget.pcProfile_le_iff
#check @UniformConsequence.Indexed.ITarget.nsProfile_le_iff
#check @UniformConsequence.Indexed.ITarget.orbit_pcProfile_eq_rep
#check @UniformConsequence.Indexed.ITarget.orbit_nsProfile_eq_rep
#check @UniformConsequence.Indexed.ITarget.pcProfile_eq_iSup_orbit
#check @UniformConsequence.Indexed.ITarget.nsProfile_eq_iSup_orbit
#check @UniformConsequence.Indexed.ITarget.profile_step
#check @UniformConsequence.Indexed.ITarget.periodic_pc
#check @UniformConsequence.Indexed.ITarget.periodic_ns
#check @UniformConsequence.Indexed.ITarget.linearBounds_pc
#check @UniformConsequence.Indexed.ITarget.linearBounds_ns
#check @UniformConsequence.Indexed.ITarget.T2_bound
#check @UniformConsequence.Indexed.ITarget.T3_full
#check @UniformConsequence.Indexed.ITarget.liminf_classification
#check @UniformConsequence.Indexed.ITarget.upperComparison
#check @UniformConsequence.Indexed.ITarget.types_agree
#check @UniformConsequence.Indexed.ITarget.common_peaks
#check @UniformConsequence.Indexed.ITarget.maxDeg_le_pcProfile
-- Milestone 3
#check @UniformConsequence.Fresh.tpcDegree_y
#check @UniformConsequence.Fresh.tnsDegree_y
#check @UniformConsequence.Fresh.derives_ysubst
#check @UniformConsequence.Fresh.derives_y_of_refutes
#check @UniformConsequence.Fresh.y_mem_of_one_mem
#check @UniformConsequence.Fresh.extract_mem
#check @UniformConsequence.Fresh.freshVar_inst
#check @UniformConsequence.Fresh.freshVar_poly
#check @UniformConsequence.Fresh.freshTarget_poly
#check @UniformConsequence.Fresh.fresh_profiles
#check @UniformConsequence.Fresh.fresh_target_degree
#check @UniformConsequence.Fresh.bhat_fresh_window
#check @UniformConsequence.Fresh.bhat_fresh_peaks
#check @UniformConsequence.Fresh.fresh_types
#check @UniformConsequence.Fresh.bhat_fresh_T4
#print UniformConsequence.Fresh.Recur
#check @PaperAudit.bhat_window

/-! ### Axioms -/

#print axioms UniformConsequence.Indexed.indexed_transfer
#print axioms UniformConsequence.Indexed.orbit_rep_transfer
#print axioms UniformConsequence.Indexed.indexed_target_endpoint
#print axioms UniformConsequence.Indexed.orbit_endpoint
#print axioms UniformConsequence.Indexed.ITarget.orbit_pcProfile_eq_rep
#print axioms UniformConsequence.Indexed.ITarget.orbit_nsProfile_eq_rep
#print axioms UniformConsequence.Indexed.ITarget.pcProfile_eq_iSup_orbit
#print axioms UniformConsequence.Indexed.ITarget.linearBounds_pc
#print axioms UniformConsequence.Indexed.ITarget.linearBounds_ns
#print axioms UniformConsequence.Indexed.ITarget.T2_bound
#print axioms UniformConsequence.Indexed.ITarget.T3_full
#print axioms UniformConsequence.Indexed.ITarget.liminf_classification
#print axioms UniformConsequence.Indexed.ITarget.types_agree
#print axioms UniformConsequence.Indexed.ITarget.common_peaks
#print axioms UniformConsequence.Fresh.tpcDegree_y
#print axioms UniformConsequence.Fresh.tnsDegree_y
#print axioms UniformConsequence.Fresh.freshVar_inst
#print axioms UniformConsequence.Fresh.fresh_profiles
#print axioms UniformConsequence.Fresh.bhat_fresh_window
#print axioms UniformConsequence.Fresh.bhat_fresh_peaks
#print axioms UniformConsequence.Fresh.fresh_types
#print axioms UniformConsequence.Fresh.bhat_fresh_T4

/-! ### Transitive dependencies -/

-- the indexed profile endpoint uses the indexed transfer, the doubled-support detector and the
-- whole-consequence inclusion (chain bound and plateau lemma)
#uses UniformConsequence.Indexed.indexed_target_endpoint UniformConsequence.Indexed.indexed_transfer
#uses UniformConsequence.Indexed.indexed_target_endpoint ClaudeComparison.detect
#uses UniformConsequence.Indexed.indexed_target_endpoint UniformConsequence.uniform_inclusion
#uses UniformConsequence.Indexed.indexed_target_endpoint ClaudeComparison.chainBound
#uses UniformConsequence.Indexed.indexed_target_endpoint ClaudeC017.Vinf_le_of_stable
#uses UniformConsequence.Indexed.indexed_target_endpoint LinearFinal.topWitnessHypothesis_linear
-- the PC linear bounds come from the indexed PC transfer, not from the NS comparison
#uses UniformConsequence.Indexed.ITarget.linearBounds_pc UniformConsequence.Indexed.indexed_transfer
#uses UniformConsequence.Indexed.ITarget.linearBounds_pc UniformConsequence.uniform_inclusion
-- no simple-source handoff, no sorry, no historical hypothesis interface
#uses UniformConsequence.Indexed.indexed_target_endpoint ExactnessHandoff.const_mem_iff_of_simple
#uses UniformConsequence.Indexed.indexed_target_endpoint sorryAx
#uses UniformConsequence.Indexed.orbit_endpoint sorryAx
#uses UniformConsequence.Indexed.indexed_target_endpoint DegreeProfilesReview.Uniform.DeletionHypothesis
#uses UniformConsequence.Indexed.indexed_target_endpoint DegreeProfilesReview.Uniform.DeletionHypothesisW
-- the fresh-variable identities are elementary (no deletion, no exactness)
#uses UniformConsequence.Fresh.tpcDegree_y ClaudeComparison.detect
#uses UniformConsequence.Fresh.tnsDegree_y ClaudeComparison.detect
#uses UniformConsequence.Fresh.tpcDegree_y sorryAx
#uses UniformConsequence.Fresh.tnsDegree_y sorryAx
-- the instance uses the preserved witness bounds
#uses UniformConsequence.Fresh.bhat_fresh_window PaperAudit.bhat_window
#uses UniformConsequence.Fresh.bhat_fresh_window ClaudeUndec.bhat_upper
#uses UniformConsequence.Fresh.bhat_fresh_window ClaudeUndec.bhat_pc_lower
#uses UniformConsequence.Fresh.bhat_fresh_window sorryAx
#uses UniformConsequence.Fresh.bhat_fresh_peaks sorryAx
#uses UniformConsequence.Fresh.bhat_fresh_T4 ClaudeUndec.bhat_pc_type
#uses UniformConsequence.Fresh.bhat_fresh_T4 sorryAx
#uses UniformConsequence.Fresh.fresh_types sorryAx
