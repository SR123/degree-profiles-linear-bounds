/-
Uniform consequences, Claude return 002 (5 October 2026).  Audit file for Milestone 1
(bounded-support indexed-target transfer).

Prints the definitions the endpoints depend on, the endpoint statements, their axioms, and
transitive-dependency checks (`#uses`, from the preserved `UDeps`).
-/
import UCIndexedTransfer
import UDeps

set_option autoImplicit false

open UniformConsequence UniformConsequence.Indexed UniformConsequence.Indexed.ITarget

/-! ### Definitions -/

#print UniformConsequence.Indexed.ITarget
#print UniformConsequence.Indexed.inflate
#print UniformConsequence.Indexed.ITarget.aux
#print UniformConsequence.Indexed.ITarget.poly
#print UniformConsequence.Indexed.ITarget.deg
#print UniformConsequence.Indexed.ITarget.maxDeg
#print UniformConsequence.Indexed.ITarget.AllPC
#print UniformConsequence.Indexed.ITarget.AllNS
#print UniformConsequence.Indexed.ITarget.ZeroDerivable
#print UniformConsequence.Indexed.ITarget.InOrbit
#print UniformConsequence.Indexed.ITarget.orbit
#print UniformConsequence.Indexed.ITarget.supp
#print UniformConsequence.Indexed.ITarget.concDatumJ
#print UniformConsequence.Indexed.ITarget.catDatumJ
#print UniformConsequence.Indexed.ITarget.ωCompatJ
#print UniformConsequence.Indexed.ITarget.ΦCompatJW
#print UniformConsequence.Indexed.DetectsSubquotients
#print DegreeProfilesReview.Uniform.Template.axM
#print DegreeProfilesReview.Uniform.Template.axSys
#print DegreeProfilesReview.Uniform.Template.axMap
#print DegreeProfilesReview.PC.Vinf
#print DegreeProfilesReview.NS.NSspan
#print ClaudeCP.IsTopWitness

/-! ### Endpoint statements -/

#check @UniformConsequence.Indexed.indexed_transfer
#check @UniformConsequence.Indexed.indexed_transfer_written_range
#check @UniformConsequence.Indexed.indexed_transfer_derivations
#check @UniformConsequence.Indexed.orbit_rep_transfer
#check @UniformConsequence.Indexed.ITarget.all_step_of_witness
#check @UniformConsequence.Indexed.ITarget.all_pc_step_of_detects
#check @UniformConsequence.Indexed.ITarget.all_ns_step_of_detects
#check @UniformConsequence.Indexed.detects_canonical
#check @UniformConsequence.Indexed.constMem_iff_of_detects
#check @UniformConsequence.Indexed.image_membership_iff_of_detects
#check @UniformConsequence.Indexed.map_eq_zero_iff_of_detects
#check @UniformConsequence.Indexed.ITarget.J_entry
#check @UniformConsequence.Indexed.ITarget.J_realise
#check @UniformConsequence.Indexed.ITarget.J_realise_single
#check @UniformConsequence.Indexed.ITarget.J_transport
#check @UniformConsequence.Indexed.ITarget.pc_all_stage_iff
#check @UniformConsequence.Indexed.ITarget.ns_all_iff
#check @UniformConsequence.Indexed.ITarget.concMem_iff
#check @UniformConsequence.Indexed.ITarget.totalDegree_poly
#check @UniformConsequence.Indexed.ITarget.not_all_of_lt
#check @UniformConsequence.Indexed.ITarget.allPC_zero_iff
#check @UniformConsequence.Indexed.ITarget.allNS_zero_iff
#check @UniformConsequence.Indexed.ITarget.allPC_map_iff
#check @UniformConsequence.Indexed.ITarget.allNS_map_iff
#check @UniformConsequence.Indexed.ITarget.rep_iff_orbit_pc
#check @UniformConsequence.Indexed.ITarget.rep_iff_orbit_ns
#check @UniformConsequence.Indexed.ITarget.allPC_iff_forall_orbit
#check @UniformConsequence.Indexed.ITarget.allNS_iff_forall_orbit
#check @UniformConsequence.Indexed.orbit_transitive
#check @UniformConsequence.Indexed.rename_mem_Vinf
#check @UniformConsequence.Indexed.inflate_inst
#check @UniformConsequence.Indexed.inflate_axMap
#check @UniformConsequence.Indexed.inflate_certMap
#check @UniformConsequence.Indexed.ITarget.supp_eq

/-! ### Axioms -/

#print axioms UniformConsequence.Indexed.indexed_transfer
#print axioms UniformConsequence.Indexed.indexed_transfer_written_range
#print axioms UniformConsequence.Indexed.indexed_transfer_derivations
#print axioms UniformConsequence.Indexed.orbit_rep_transfer
#print axioms UniformConsequence.Indexed.ITarget.all_step_of_witness
#print axioms UniformConsequence.Indexed.detects_canonical
#print axioms UniformConsequence.Indexed.constMem_iff_of_detects
#print axioms UniformConsequence.Indexed.image_membership_iff_of_detects
#print axioms UniformConsequence.Indexed.ITarget.J_realise_single
#print axioms UniformConsequence.Indexed.ITarget.J_transport
#print axioms UniformConsequence.Indexed.ITarget.pc_all_stage_iff
#print axioms UniformConsequence.Indexed.ITarget.ns_all_iff
#print axioms UniformConsequence.Indexed.ITarget.not_all_of_lt
#print axioms UniformConsequence.Indexed.ITarget.allPC_zero_iff
#print axioms UniformConsequence.Indexed.ITarget.allNS_zero_iff
#print axioms UniformConsequence.Indexed.ITarget.rep_iff_orbit_pc
#print axioms UniformConsequence.Indexed.ITarget.rep_iff_orbit_ns
#print axioms UniformConsequence.Indexed.orbit_transitive
#print axioms UniformConsequence.Indexed.rename_mem_Vinf
#print axioms UniformConsequence.Indexed.inflate_inst

/-! ### Transitive dependencies -/

-- the unconditional linear witnesses (with their proof of FORCE), the actual shifted functor and
-- its constructed M5 data, matrix transport, the doubled-support detector and field descent
#uses UniformConsequence.Indexed.indexed_transfer LinearFinal.topWitnessHypothesis_linear
#uses UniformConsequence.Indexed.indexed_transfer RForce.forceExists
#uses UniformConsequence.Indexed.indexed_transfer SelfContainedCycle004.canonicalM5w
#uses UniformConsequence.Indexed.indexed_transfer DegreeProfilesReview.Deletion.M5w.δ_mat
#uses UniformConsequence.Indexed.indexed_transfer ClaudeComparison.detect
#uses UniformConsequence.Indexed.indexed_transfer ClaudeCP.top_preserves_finiteLimits
#uses UniformConsequence.Indexed.indexed_transfer DegreeProfilesReview.FieldDescent.pc_derives_map_iff
-- no simple-source handoff is used for the indexed transfer
#uses UniformConsequence.Indexed.indexed_transfer ExactnessHandoff.const_mem_iff_of_simple
#uses UniformConsequence.Indexed.indexed_transfer ExactnessHandoff.image_membership_iff_of_simple
-- no sorry and no historical hypothesis interface
#uses UniformConsequence.Indexed.indexed_transfer sorryAx
#uses UniformConsequence.Indexed.orbit_rep_transfer sorryAx
#uses UniformConsequence.Indexed.indexed_transfer DegreeProfilesReview.Uniform.DeletionHypothesis
#uses UniformConsequence.Indexed.indexed_transfer DegreeProfilesReview.Uniform.DeletionHypothesisW
#uses UniformConsequence.Indexed.indexed_transfer ForceInterface.ForceExists
-- the distinguished map of the indexed data is the target matrix (definitional checks)
#check @UniformConsequence.Indexed.ITarget.catDatumJ_c
#check @UniformConsequence.Indexed.ITarget.concDatumJ_c
#print axioms UniformConsequence.Indexed.ITarget.catDatumJ_c
