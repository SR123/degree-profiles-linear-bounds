/-
Claude, 26 Sep 2026.  Uniform NS–PC comparison combined with the linear classification.

`CompFinal` proves the comparison from the quadratic witness theorem alone.  Here it is combined
with `LinearFinal.linear_classification` (linear onset `max(n₀, 2(kd+s)+1)`), giving agreement of
the NS and ordinary-PC types relative to the linear onset, and the common type together with
both profiles' linear bounds.

The comparison `F` is large and is not used to transfer any quantitative bound: the linear
bounds for each profile come from `LinearFinal` directly, separately for PC and for NS.
-/
import CompFinal
import LinearFinal

set_option autoImplicit false

namespace ClaudeComparison
open DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] (T : Template R)

theorem periodic_linear_pc :
    PeriodicProfile T.pcProfile (onset T.k T.s T.n0) (period p T.k T.s) :=
  (LinearFinal.linear_classification p T T.pcProfile (Set.mem_insert _ _)).1

theorem periodic_linear_ns :
    PeriodicProfile T.nsProfile (onset T.k T.s T.n0) (period p T.k T.s) :=
  (LinearFinal.linear_classification p T T.nsProfile
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))).1

include p in
/-- **Agreement of types, relative to the linear onset.** -/
theorem types_agree_linear :
    let N := onset T.k T.s T.n0
    (IsT1 T.pcProfile ↔ IsT1 T.nsProfile) ∧ (IsT2 T.pcProfile N ↔ IsT2 T.nsProfile N) ∧
    (IsT3 T.pcProfile N ↔ IsT3 T.nsProfile N) ∧ (IsT4 T.pcProfile N ↔ IsT4 T.nsProfile N) := by
  obtain ⟨F, hF, hub⟩ := upperComparison p T
  exact types_transfer (periodic_linear_pc p T) (periodic_linear_ns p T) hF
    T.pcProfile_le_nsProfile hub

include p in
/-- **The common type, relative to the linear onset.** -/
theorem common_type_linear :
    let N := onset T.k T.s T.n0
    (IsT1 T.pcProfile ∧ IsT1 T.nsProfile) ∨ (IsT2 T.pcProfile N ∧ IsT2 T.nsProfile N) ∨
    (IsT3 T.pcProfile N ∧ IsT3 T.nsProfile N) ∨ (IsT4 T.pcProfile N ∧ IsT4 T.nsProfile N) := by
  obtain ⟨e1, e2, e3, e4⟩ := types_agree_linear p T
  rcases (periodic_linear_pc p T).exactly_one with h | h | h | h
  · exact Or.inl ⟨h.1, e1.mp h.1⟩
  · exact Or.inr (Or.inl ⟨h.2.1, e2.mp h.2.1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.2.2.1, e3.mp h.2.2.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h.2.2.2, e4.mp h.2.2.2⟩))

end ClaudeComparison
