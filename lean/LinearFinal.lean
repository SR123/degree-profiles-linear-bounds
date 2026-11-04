/-
Coordinator, 26 Sep 2026.  The unconditional linear classification.

Assembles, with no hypotheses:
* R's `RForce.forceExists` (Theorem A of the forcing proof: FORCE for the lex-first LIS, any
  commutative ring, every board size);
* B's `BFinalLinear.linear_of_forceExists` (Theorem B, the realisation of every zero-line-sum rook
  function, D's reduction of the double centraliser, B's Theorem A chain with Prop. 6, and the
  every-prime template transfer of `PTransfer`/`LinearInterface`).

Result: for every uniform template over a field of prime characteristic p, the PC and NS degree
profiles satisfy (P) with Stage 5's linear onset max(n₀, 2(kd+s)+1), exactly one of T1–T4 holds, in
T2 (and on the hard classes of T3) h(n) > ⌊(n − 2s − 1)/(2k)⌋, and in T4 there are arbitrarily large
peaks h(n) = d with n ≤ (p+2)(kd+s).
-/
import FinalLinear
import RForce

set_option autoImplicit false

namespace LinearFinal
open DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles

/-- Witnesses with the sharp budget `2r − 1`, over every algebraically closed field of
characteristic `p`. -/
theorem topWitnessHypothesis_linear (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [IsAlgClosed L]
    [CharP L p] : ClaudeCP.TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  BFinalLinear.topWitnessHypothesis_of_forceExists p L (fun M => RForce.forceExists L M)

/-- Exactness of the actual shifted functor with budget `2r − 1`. -/
theorem exactness_linear (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [IsAlgClosed L]
    [CharP L p] : ClaudeLinear.ExactnessHypothesis p L (fun r => 2 * r - 1) :=
  BFinalLinear.exactness_of_forceExists p L (fun M => RForce.forceExists L M)

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] (T : Template R)

/-- **The linear T1–T4 theorem, unconditional**, for the PC and the NS profile, every prime `p`. -/
theorem linear_classification :
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
  BFinalLinear.linear_of_forceExists p T (fun M => RForce.forceExists _ M)

end LinearFinal
