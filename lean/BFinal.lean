/-
Agent B, round 4: the conditional end-to-end statement.

**CONDITIONAL on DCP_b only** (`DCPHyp`, BTransC: every `S_b`-equivariant map `Top_b(N) → Soc_b(N)`
is induced by a tuple relation of support `b - 1`; Prop. 8 of the paper, from Bowman–Doty–Martin).
Everything else is proved: Theorem A (`topWitnessHypothesis_of_dcp`, BProp6 and the modules it
imports), then `ClaudeLinear.exactness_of_top`, `ExactnessHypothesis.mono` (`2r-1 ≤ 2r+1`) and
`ClaudeLinear.linear_of_exactness` (Stage 5's linear corollaries T1–T4 for PC and NS).

* `exactness_of_dcp` : DCP ⇒ `ExactnessHypothesis p L (fun r => 2r-1)` and hence `stableW`.
* `linear_of_dcp`    : DCP over `AlgebraicClosure R` ⇒ the linear T1–T4 statement, both profiles,
  every prime `p`.
* `linear_of_dcp'`   : the same with DCP stated as `∀ b N, 1 ≤ b → 2b+1 ≤ N → DCPHyp b N`.
-/
import BProp6
import LinearInterface

set_option autoImplicit false

namespace BExact

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle012 SelfContainedCycle013
open ClaudeWitnessTransfer ClaudeC017 ClaudeCP ClaudeLinear

section Final

variable (p : ℕ) [Fact p.Prime]

/-- **Exactness with budget `2r - 1`, CONDITIONAL only on DCP.** -/
theorem exactness_of_dcp (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ r a n : ℕ, r < p ^ a → 2 * r - 1 ≤ n → ∀ b, 1 ≤ b → b ≤ r →
      DCPHyp (K := L) b (n + p ^ a)) :
    ExactnessHypothesis p L (fun r => 2 * r - 1) :=
  exactness_of_top (topWitnessHypothesis_of_dcp p L H)

/-- The stable-range budget `2r + 1`, CONDITIONAL only on DCP. -/
theorem exactness_stableW_of_dcp (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ r a n : ℕ, r < p ^ a → 2 * r - 1 ≤ n → ∀ b, 1 ≤ b → b ≤ r →
      DCPHyp (K := L) b (n + p ^ a)) :
    ExactnessHypothesis p L stableW :=
  (exactness_of_dcp p L H).mono (fun r => by unfold stableW; omega)

variable {R : Type} [Field R] [CharP R p] (T : Template R)

/-- **Linear onset, CONDITIONAL only on DCP** (over the algebraic closure of the coefficient
field): both profiles satisfy (P) with Stage 5's onset, exactly one of T1–T4 holds, and the linear
bounds of `ClaudeLinear.linear_of_exactness` hold in T2, T3, T4.  Every prime `p`. -/
theorem linear_of_dcp
    (H : ∀ r a n : ℕ, r < p ^ a → 2 * r - 1 ≤ n → ∀ b, 1 ≤ b → b ≤ r →
      DCPHyp (K := AlgebraicClosure R) b (n + p ^ a)) :
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
  linear_of_exactness p T (exactness_stableW_of_dcp p (AlgebraicClosure R) H)

/-- The same, with DCP stated for all `N ≥ 2b + 1` (CONDITIONAL only on DCP). -/
theorem linear_of_dcp'
    (H : ∀ b N : ℕ, 1 ≤ b → 2 * b + 1 ≤ N → DCPHyp (K := AlgebraicClosure R) b N) :
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
  linear_of_dcp p T fun r a n hr hn b hb hbr => H b (n + p ^ a) hb (by omega)

end Final

end BExact
