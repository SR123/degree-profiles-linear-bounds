/-
Agent B, round 6 (26 Sep 2026).  **Final assembly, CONDITIONAL ON FORCE.**

The linear onset theorem (T1–T4, PC and NS, every prime `p`), the exactness hypothesis and
Theorem A (`TopWitnessHypothesis`, budget `2r - 1`), each CONDITIONAL ONLY on R's FORCE statement
`ForceInterface.ForceExists` (Theorem A of R_referee/work/HALF_PROOF.md, being proved in Lean by
Agent R in parallel).  Nothing else is assumed.

Route: `BRealise.realisationFromForce` (Theorem B, unconditional) turns `ForceExists K M` into
realisability of every element of `Z_b` of the full board `Fin M × Fin M`; this is D's canonical
statement `HALFSq K b M` with its extra vanishing hypothesis dropped (`halfSq_of_forceExists`).
D's `ClaudeDCP.linear_of_halfSq2` / `topWitnessHypothesis_of_halfSq2` / `exactness_of_halfSq2`
(DCPFinal2, copied verbatim with DCPBridge, DCPInterface, DCPCanon, DCPHalf2, DCPFinal; md5 in
work/lean_logs/copied_round6.md5) then give the conclusions.

Main results (all CONDITIONAL on `ForceExists`, clearly labelled):
* `halfSq_of_forceExists` : `ForceExists K M → HALFSq K b M` (every `b`, any commutative ring);
* `topWitnessHypothesis_of_forceExists`, `exactness_of_forceExists`;
* **`linear_of_forceExists`** : the conclusion of `ClaudeDCP.linear_of_halfSq2`;
* `…_window` variants: `ForceExists` only for the sizes `M` that D's reduced window uses
  (`4 ≤ b`, `b + 3 ≤ M ≤ 2b - 1`, so `M ≥ 7`).
-/
import BRealise
import DCPFinal2

set_option autoImplicit false

namespace BFinalLinear

open Finset ClaudeDCP ForceInterface
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle012 SelfContainedCycle013
open ClaudeWitnessTransfer ClaudeC017 ClaudeCP ClaudeLinear

/-- **`HALFSq` from FORCE** (CONDITIONAL on `ForceExists K M`): the vanishing hypothesis of
`HALFSq` is not needed. -/
theorem halfSq_of_forceExists {K : Type*} [CommRing K] {M : ℕ} (H : ForceExists K M) (b : ℕ) :
    HALFSq K b M :=
  fun _ F hZ _ => BRealise.real_of_forceExists H b F hZ

section Final

variable (p : ℕ) [Fact p.Prime]

/-- **Theorem A (top witnesses, budget `2r - 1`), CONDITIONAL on FORCE in D's window.** -/
theorem topWitnessHypothesis_of_forceExists_window (L : Type) [Field L] [IsAlgClosed L]
    [CharP L p] (H : ∀ b M, 4 ≤ b → b + 3 ≤ M → M + 1 ≤ 2 * b → ForceExists L M) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  topWitnessHypothesis_of_halfSq2 p L fun b M h4 h1 h2 => halfSq_of_forceExists (H b M h4 h1 h2) b

/-- **Theorem A (top witnesses, budget `2r - 1`), CONDITIONAL on FORCE.** -/
theorem topWitnessHypothesis_of_forceExists (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ M, ForceExists L M) : TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  topWitnessHypothesis_of_forceExists_window p L fun _ M _ _ _ => H M

/-- **Exactness with budget `2r - 1`, CONDITIONAL on FORCE in D's window.** -/
theorem exactness_of_forceExists_window (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ b M, 4 ≤ b → b + 3 ≤ M → M + 1 ≤ 2 * b → ForceExists L M) :
    ExactnessHypothesis p L (fun r => 2 * r - 1) :=
  exactness_of_top (topWitnessHypothesis_of_forceExists_window p L H)

/-- **Exactness with budget `2r - 1`, CONDITIONAL on FORCE.** -/
theorem exactness_of_forceExists (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ M, ForceExists L M) : ExactnessHypothesis p L (fun r => 2 * r - 1) :=
  exactness_of_top (topWitnessHypothesis_of_forceExists p L H)

variable {R : Type} [Field R] [CharP R p] (T : Template R)

/-- **Linear onset (T1–T4, PC and NS, every prime), CONDITIONAL on FORCE in D's window**
(`ForceExists` over the algebraic closure of the coefficient field, for `M ≥ b + 3`,
`M ≤ 2b - 1`, `b ≥ 4`). -/
theorem linear_of_forceExists_window
    (H : ∀ b M, 4 ≤ b → b + 3 ≤ M → M + 1 ≤ 2 * b → ForceExists (AlgebraicClosure R) M) :
    ∀ h ∈ ({T.pcProfile, T.nsProfile} : Set (ℕ → ℕ∞)),
    PeriodicProfile h (onset T.k T.s T.n0) (period p T.k T.s) ∧
    ((IsT1 h ∧ ¬ IsT2 h (onset T.k T.s T.n0) ∧ ¬ IsT3 h (onset T.k T.s T.n0) ∧
        ¬ IsT4 h (onset T.k T.s T.n0)) ∨
     (¬ IsT1 h ∧ IsT2 h (onset T.k T.s T.n0) ∧ ¬ IsT3 h (onset T.k T.s T.n0) ∧
        ¬ IsT4 h (onset T.k T.s T.n0)) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h (onset T.k T.s T.n0) ∧ IsT3 h (onset T.k T.s T.n0) ∧
        ¬ IsT4 h (onset T.k T.s T.n0)) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h (onset T.k T.s T.n0) ∧ ¬ IsT3 h (onset T.k T.s T.n0) ∧
        IsT4 h (onset T.k T.s T.n0))) ∧
    (IsT2 h (onset T.k T.s T.n0) → ∀ n x : ℕ, T.n0 ≤ n → h n = (x : ℕ∞) →
      ((n : ℤ) - 2 * T.s - 1) / (2 * T.k) < (x : ℤ)) ∧
    (IsT3 h (onset T.k T.s T.n0) →
      ∃ (D : ℕ) (U : Set ℕ), U.Nonempty ∧ (∃ c, c < period p T.k T.s D ∧ c ∉ U) ∧
        ∀ n, onset T.k T.s T.n0 D ≤ n → 2 * T.k + 2 * T.s + 1 ≤ n →
          n % period p T.k T.s D ∉ U → (((n - 2 * T.s - 1) / (2 * T.k) : ℕ) : ℕ∞) < h n) ∧
    (IsT4 h (onset T.k T.s T.n0) → ∀ B : ℕ,
      ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧ d ∈ E h (onset T.k T.s T.n0) ∧ h n = (d : ℕ∞) ∧
        n ≤ (p + 2) * (T.k * d + T.s) ∧
        (n : ℚ) / ((p + 2) * T.k) - T.s / T.k ≤ d) :=
  linear_of_halfSq2 p T fun b M h4 h1 h2 => halfSq_of_forceExists (H b M h4 h1 h2) b

/-- **Linear onset (T1–T4, PC and NS, every prime), CONDITIONAL on FORCE**
(`ForceExists (AlgebraicClosure R) M` for every `M`; Agent R's target).  This is the conclusion
of `ClaudeDCP.linear_of_halfSq2` with its `HALFSq` hypothesis discharged by
`BRealise.realisationFromForce`. -/
theorem linear_of_forceExists (H : ∀ M, ForceExists (AlgebraicClosure R) M) :
    ∀ h ∈ ({T.pcProfile, T.nsProfile} : Set (ℕ → ℕ∞)),
    PeriodicProfile h (onset T.k T.s T.n0) (period p T.k T.s) ∧
    ((IsT1 h ∧ ¬ IsT2 h (onset T.k T.s T.n0) ∧ ¬ IsT3 h (onset T.k T.s T.n0) ∧
        ¬ IsT4 h (onset T.k T.s T.n0)) ∨
     (¬ IsT1 h ∧ IsT2 h (onset T.k T.s T.n0) ∧ ¬ IsT3 h (onset T.k T.s T.n0) ∧
        ¬ IsT4 h (onset T.k T.s T.n0)) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h (onset T.k T.s T.n0) ∧ IsT3 h (onset T.k T.s T.n0) ∧
        ¬ IsT4 h (onset T.k T.s T.n0)) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h (onset T.k T.s T.n0) ∧ ¬ IsT3 h (onset T.k T.s T.n0) ∧
        IsT4 h (onset T.k T.s T.n0))) ∧
    (IsT2 h (onset T.k T.s T.n0) → ∀ n x : ℕ, T.n0 ≤ n → h n = (x : ℕ∞) →
      ((n : ℤ) - 2 * T.s - 1) / (2 * T.k) < (x : ℤ)) ∧
    (IsT3 h (onset T.k T.s T.n0) →
      ∃ (D : ℕ) (U : Set ℕ), U.Nonempty ∧ (∃ c, c < period p T.k T.s D ∧ c ∉ U) ∧
        ∀ n, onset T.k T.s T.n0 D ≤ n → 2 * T.k + 2 * T.s + 1 ≤ n →
          n % period p T.k T.s D ∉ U → (((n - 2 * T.s - 1) / (2 * T.k) : ℕ) : ℕ∞) < h n) ∧
    (IsT4 h (onset T.k T.s T.n0) → ∀ B : ℕ,
      ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧ d ∈ E h (onset T.k T.s T.n0) ∧ h n = (d : ℕ∞) ∧
        n ≤ (p + 2) * (T.k * d + T.s) ∧
        (n : ℚ) / ((p + 2) * T.k) - T.s / T.k ≤ d) :=
  linear_of_forceExists_window p T fun _ M _ _ _ => H M

end Final

end BFinalLinear
