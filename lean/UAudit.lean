/-
Claude, 27 Sep 2026.  Audit of the undecidability formalisation: statements and axioms of every
endpoint, the definitions they rest on, and a concrete instantiation (p = 2, K = ZMod 2) showing
that the hypotheses are satisfiable.
-/
import UPCDirect
import UDeps

open ClaudeUndec

/-! ## Definitions the endpoints rest on -/

#print ClaudeUndec.Sentence
#print ClaudeUndec.IsModel
#print ClaudeUndec.HasModelOfSize
#print ClaudeUndec.WF
#print ClaudeUndec.Promised
#print ClaudeUndec.TypeSep
#print Computable
#print Partrec
#print ComputablePred
#print ClaudeUndec.NSType
#print ClaudeUndec.PCType
#print ClaudeUndec.IType
#print ClaudeUndec.Rec
#print DegreeProfilesReview.Profiles.IsT1
#print DegreeProfilesReview.Profiles.IsT2
#print DegreeProfilesReview.Profiles.IsT3
#print DegreeProfilesReview.Profiles.IsT4
#print DegreeProfilesReview.Profiles.E
#print DegreeProfilesReview.NS.NSRefutes
#print DegreeProfilesReview.NS.nsDegree
#print DegreeProfilesReview.PC.IsProof
#print DegreeProfilesReview.PC.Refutes
#print DegreeProfilesReview.PC.pcDegree
#print ClaudeUndec.join
#print ClaudeUndec.guardN
#print ClaudeUndec.guardP
#print ClaudeUndec.conj
#print ClaudeUndec.wit
#print ClaudeUndec.wrank
#print ClaudeUndec.red
#print ClaudeUndec.red2
#print ClaudeUndec.univProg
#print ClaudeUndec.theta

/-! ## Priority 1: the every-union theorem (published scope) -/

#check @undecidable_union_NS
#check @undecidable_union_PC
#check @undecidable_union_PC_direct
#check @decides_of_promise
#print axioms undecidable_union_NS
#print axioms undecidable_union_PC
#print axioms undecidable_union_PC_direct
#print axioms decides_of_promise

/-! ## Priority 2: pairs and disjoint sets (strong form) -/

#check @undecidable_pair_NS
#check @undecidable_pair_PC
#check @undecidable_disjoint_NS
#check @undecidable_disjoint_PC
#check @undecidable_pair_PC_direct
#check @undecidable_disjoint_PC_direct
#check @pairs_iff_disjoint
#check @typeSep_symm
#check @typeSep_of_computable
#check @sep_decides
#check @union_of_sep
#check @undecidable_union_NS_via_pairs
#print axioms undecidable_pair_NS
#print axioms undecidable_pair_PC
#print axioms undecidable_disjoint_NS
#print axioms undecidable_disjoint_PC
#print axioms undecidable_pair_PC_direct
#print axioms undecidable_disjoint_PC_direct
#print axioms pairs_iff_disjoint
#print axioms typeSep_symm
#print axioms typeSep_of_computable
#print axioms sep_decides
#print axioms undecidable_union_NS_via_pairs

/-! ## The guarded join -/

#check @nsDegree_join_ge
#check @nsDegree_join_le
#check @pcDegree_join_ge
#check @pcDegree_join_le
#check @join_no_model
#check @join_WF
#check @join_primrec
#check @templateParams_primrec
#check @join_cases
#print axioms nsDegree_join_ge
#print axioms nsDegree_join_le
#print axioms pcDegree_join_ge
#print axioms pcDegree_join_le
#print axioms join_no_model
#print axioms join_WF
#print axioms join_primrec
#print axioms templateParams_primrec
#print axioms join_cases

/-! ## Type calculus and witness order -/

#check @iType_sandwich
#check @iType2_mono
#check @iType3_of
#check @red2_halt
#check @red2_nonhalt
#check @red2_primrec
#check @red2_promised
#check @wit_type
#check @nsType_unique
#check @nsType_exists
#check @pcType_iff_nsType
#check @pcDegree_conj_eq_left
#check @wit_pc_type
#check @red2_pc_halt
#check @red2_pc_nonhalt
#check @bhat_refutes_B
#check @eta_pc_lower
#print axioms iType_sandwich
#print axioms iType2_mono
#print axioms iType3_of
#print axioms red2_halt
#print axioms red2_nonhalt
#print axioms red2_primrec
#print axioms red2_promised
#print axioms wit_type
#print axioms pcType_iff_nsType
#print axioms pcDegree_conj_eq_left
#print axioms wit_pc_type
#print axioms red2_pc_halt
#print axioms red2_pc_nonhalt
#print axioms bhat_refutes_B
#print axioms eta_pc_lower

/-! ## Which proven results the endpoints rest on

`#uses a b` reports whether `b` occurs in the transitive closure of constants used by `a`. -/

#uses ClaudeUndec.undecidable_pair_NS ClaudeComparison.upperComparison
#uses ClaudeUndec.undecidable_union_NS ClaudeComparison.upperComparison
#uses ClaudeUndec.undecidable_pair_PC_direct ClaudeComparison.upperComparison
#uses ClaudeUndec.undecidable_union_PC_direct ClaudeComparison.upperComparison
#uses ClaudeUndec.undecidable_pair_PC ClaudeComparison.upperComparison
#uses ClaudeUndec.undecidable_pair_NS LinearFinal.linear_classification
#uses ClaudeUndec.undecidable_pair_PC_direct LinearFinal.linear_classification
#uses ClaudeUndec.undecidable_pair_NS ComputablePred.halting_problem
#uses ClaudeUndec.undecidable_pair_NS SelfContainedCycle072.G_both_linear
#uses ClaudeUndec.undecidable_pair_NS SelfContainedCycle058.no_PCRefutes_rectangle
#uses ClaudeUndec.undecidable_pair_NS ClaudeUndec.theta_nsRefutes
#uses ClaudeUndec.undecidable_pair_NS ClaudeUndec.switch_i
#uses ClaudeUndec.undecidable_pair_NS ClaudeUndec.primrec_compiles

/-! ## Machines, the switch and universality -/

#check @switch_i
#check @no_large_model
#check @no_model_of_size
#check @theta_nsRefutes
#check @theta_eventually_bounded
#check @primrec_compiles
#check @univProg_halts_iff
#check @eval_dom_iff_halts
#check @theta_primrec
#check @univProg_primrec
#check @conj_primrec
#check @red_primrec
#check @red_promised
#check @conj_type_halt
#check @conj_type_nonhalt
#check @nsDegree_conj_eq_left
#check @hasRoot_iff
#print axioms switch_i
#print axioms no_large_model
#print axioms theta_nsRefutes
#print axioms theta_eventually_bounded
#print axioms primrec_compiles
#print axioms univProg_halts_iff
#print axioms eval_dom_iff_halts
#print axioms theta_primrec
#print axioms univProg_primrec
#print axioms conj_type_halt
#print axioms conj_type_nonhalt
#print axioms nsDegree_conj_eq_left
#print axioms hasRoot_iff

/-! ## The template parameters of the translation -/

example (φ : Sentence) (K : Type) [Field K] :
    (template φ K).k = maxVArity φ ∧ (template φ K).s = axSupp φ ∧ (template φ K).D = degD φ ∧
      (template φ K).n0 = maxVArity φ * degD φ + axSupp φ + 1 := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Non-vacuity: a concrete instance of the hypotheses -/

-- F_2, NS: no algorithm separates T4 from T3.

example : ¬ TypeSep (fun φ τ => NSType (template φ (ZMod 2)) τ) {4} {3} :=
  undecidable_pair_NS 2 (ZMod 2) 4 3 (by simp) (by simp) (by decide)

example : ¬ TypeSep (fun φ τ => PCType (template φ (ZMod 3)) τ) {1, 4} {2, 3} :=
  undecidable_disjoint_PC 3 (ZMod 3) {1, 4} {2, 3} (by intro x hx; simp at hx ⊢; omega)
    (by intro x hx; simp at hx ⊢; omega) ⟨1, by simp⟩ ⟨2, by simp⟩
    (by rw [Set.disjoint_left]; intro x hx hx'; simp at hx hx'; omega)

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

-- F_5, NS: no total computable decider of `type ∈ {T1}` versus `type ∈ {T2}` either.
example : ¬ ∃ D : Sentence → Bool, Computable D ∧
    (∀ φ, Promised φ → NSType (template φ (ZMod 5)) 1 → D φ = true) ∧
    (∀ φ, Promised φ → NSType (template φ (ZMod 5)) 2 → D φ = false) := by
  rintro ⟨D, hD, h1, h2⟩
  exact undecidable_pair_NS 5 (ZMod 5) 1 2 (by simp) (by simp) (by decide)
    (typeSep_of_computable _ _ _ D hD (fun φ hφ τ hτ ht => h1 φ hφ (hτ ▸ ht))
      (fun φ hφ τ hτ ht => h2 φ hφ (hτ ▸ ht)))

-- F_7, ordinary PC, published every-union form with A = {T2, T4}.
example : ¬ ∃ D : Sentence →. Bool, Partrec D ∧
    ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ ∃ τ ∈ ({2, 4} : Set ℕ),
      PCType (template φ (ZMod 7)) τ) :=
  undecidable_union_PC_direct 7 (ZMod 7) {2, 4} (by intro x hx; simp at hx ⊢; omega) ⟨2, by simp⟩
    ⟨1, by simp, by simp⟩
