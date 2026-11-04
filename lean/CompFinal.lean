/-
Claude, 26 Sep 2026.  Uniform NS–PC comparison, final assembly (quadratic exactness route).

For every field `R` of prime characteristic `p` and every uniform template `T` over `R`:

* `chainBound`       : `ClaudeC017.ChainBound R T.Var`, the former hypothesis (★);
* `comparison`       : a monotone `F : ℕ → ℕ`, independent of `n`, with
                       `PC.Refutes (T.inst n) t → NS.NSRefutes (T.inst n) (F t)`;
* `upperComparison`  : the same, in the form used by Stage 5's `types_transfer`;
* `types_agree`, `common_type` : the actual NS and ordinary-PC profiles have the same T1–T4 type
  (for the onset of `PFinal.charP_periodic`; the types do not depend on the onset, see
  `ClaudeCP.charP_E_intrinsic`).

Dependencies: the exact-deletion input is the unconditional quadratic top-witness theorem
`ClaudeCP.topWitnessHypothesis_of_isAlgClosed` (budget `triW`), through `CompChain`.  The linear
witness theorem of `LinearFinal` is NOT used here.  Nothing is assumed: no chain bound, no
equivalence, no exactness hypothesis.

This comparison has a very large `F`; it does not transfer an `Ω(n)` NS bound to an `Ω(n)` PC
bound, and it does not identify exact degrees or recurring levels of the two profiles.
-/
import CompPoly

set_option autoImplicit false
open MvPolynomial

namespace ClaudeComparison
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.PC DegreeProfilesReview.NS ClaudeC017 ClaudeWitnessTransfer

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] (T : Template R)

include p in
/-- **(★) for the variables of every template**, unconditionally. -/
theorem chainBound : ChainBound R T.Var :=
  chainBound_of_bounded p T.Var T.var_bounded

include p in
/-- **Uniform NS–PC comparison.**  There is a monotone `F`, independent of the universe size,
such that every degree-`t` ordinary PC refutation of `T.inst n` yields an NS refutation of
degree `F t`. -/
theorem comparison :
    ∃ F : ℕ → ℕ, Monotone F ∧
      ∀ n t, DegreeProfilesReview.PC.Refutes (T.inst n) t →
        DegreeProfilesReview.NS.NSRefutes (T.inst n) (F t) := by
  choose L hL using chainBound p T
  refine ⟨fun x => x + ∑ s ∈ Finset.range (x + 1), L s, ?_, ?_⟩
  · intro x y hxy
    have : ∑ s ∈ Finset.range (x + 1), L s ≤ ∑ s ∈ Finset.range (y + 1), L s :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    simp only
    omega
  · intro n t h
    have hchain := hL t n (fun i : Fin (L t + 2) =>
        NSspan (T.inst n) (t + i) ⊓ restrictTotalDegree (T.Var.Rk n) R t)
      (fun _ => inf_le_right) (by
        intro i g f hf
        obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hf
        refine Submodule.mem_inf.mpr ⟨rename_mem_NSspan T g h1, ?_⟩
        rw [mem_restrictTotalDegree] at h2 ⊢
        exact le_trans (totalDegree_rename_le _ f) h2)
    have hLt : L t ≤ ∑ s ∈ Finset.range (t + 1), L s :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    exact (nsRefutes_of_refutes (T.inst n) hchain h).mono (by simp only; omega)

include p in
/-- The upper comparison `nsProfile ≤ F ∘ pcProfile` of Stage 5, unconditionally. -/
theorem upperComparison :
    ∃ F : ℕ → ℕ, Monotone F ∧ UpperComparison F T.pcProfile T.nsProfile :=
  upperComparison_of_chainBound T (chainBound p T)

include p in
/-- **The NS and ordinary-PC types agree**, in every prime characteristic. -/
theorem types_agree :
    let N := wOnset T.k T.s T.n0 triW
    (IsT1 T.pcProfile ↔ IsT1 T.nsProfile) ∧ (IsT2 T.pcProfile N ↔ IsT2 T.nsProfile N) ∧
    (IsT3 T.pcProfile N ↔ IsT3 T.nsProfile N) ∧ (IsT4 T.pcProfile N ↔ IsT4 T.nsProfile N) :=
  ClaudeCP.charP_types_agree p T (chainBound p T)

include p in
/-- **The common type**: exactly one of T1–T4 holds for the PC profile, and the NS profile has
the same one. -/
theorem common_type :
    let N := wOnset T.k T.s T.n0 triW
    (IsT1 T.pcProfile ∧ IsT1 T.nsProfile) ∨ (IsT2 T.pcProfile N ∧ IsT2 T.nsProfile N) ∨
    (IsT3 T.pcProfile N ∧ IsT3 T.nsProfile N) ∨ (IsT4 T.pcProfile N ∧ IsT4 T.nsProfile N) :=
  ClaudeCP.charP_common_type p T (chainBound p T)

end ClaudeComparison
