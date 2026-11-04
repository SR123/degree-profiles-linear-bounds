/-
Agent D, round 4 (26 Sep 2026).  Final assembly with B's end-to-end module `BFinal` (copied
verbatim; md5 in work/logs/copied_B_files.md5).

* `dcpHypB_iff` : `DCPHypB` (DCPInterface) is B's `DCPHyp` (`Iff.rfl`).
* `dcpHyp_of_halfSq` : B's `DCPHyp b N` (`1 ≤ b ≤ N`) from the canonical OPEN statement `HALFSq`
  in the window `3 ≤ b' ≤ b`, `b' + 2 ≤ M ≤ 2b' - 1`.
* `dcpHyp_le_two` : B's `DCPHyp b N` for `1 ≤ b ≤ 2`, `b ≤ N`, unconditionally.
* `topWitnessHypothesis_of_halfSq`, `exactness_of_halfSq`, `linear_of_halfSq` : Theorem A, the
  exactness hypothesis and the linear onset (T1–T4, PC and NS, every prime), CONDITIONAL only on
  `HALFSq` in the window (via B's `topWitnessHypothesis_of_dcp'`, `linear_of_dcp'`).
-/
import BFinal
import DCPInterface
import DCPCanon

set_option autoImplicit false

namespace ClaudeDCP

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle012 SelfContainedCycle013
open ClaudeWitnessTransfer ClaudeC017 ClaudeCP ClaudeLinear


/-- `DCPHypB` is literally B's `DCPHyp`. -/
theorem dcpHypB_iff {K : Type} [Field K] (b N : ℕ) :
    DCPHypB (K := K) b N ↔ BExact.DCPHyp (K := K) b N := Iff.rfl

/-- **B's `DCPHyp b N` from the canonical open statement `HALFSq` in the window.** -/
theorem dcpHyp_of_halfSq {K : Type} [Field K] {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N)
    (H : ∀ b' M, 3 ≤ b' → b' ≤ b → b' + 2 ≤ M → M + 1 ≤ 2 * b' → HALFSq K b' M) :
    BExact.DCPHyp (K := K) b N :=
  dcpHypB_of_half hb hbN fun b' M hb' h1 h2 => half_of_halfSq (H b' M (by omega) hb' h1 h2)

/-- **B's `DCPHyp b N` for `b ≤ 2`, unconditionally.** -/
theorem dcpHyp_le_two {K : Type} [Field K] {b N : ℕ} (hb : 1 ≤ b) (hb2 : b ≤ 2) (hbN : b ≤ N) :
    BExact.DCPHyp (K := K) b N :=
  dcpHypB_le_two hb hb2 hbN

section Final

variable (p : ℕ) [Fact p.Prime]

/-- **Theorem A, CONDITIONAL only on `HALFSq` in the window.** -/
theorem topWitnessHypothesis_of_halfSq (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ b M, 3 ≤ b → b + 2 ≤ M → M + 1 ≤ 2 * b → HALFSq L b M) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  BExact.topWitnessHypothesis_of_dcp' p L fun _ _ hb hN =>
    dcpHyp_of_halfSq hb (by omega) fun b' M h3 _ h1 h2 => H b' M h3 h1 h2

/-- **Exactness with budget `2r - 1`, CONDITIONAL only on `HALFSq` in the window.** -/
theorem exactness_of_halfSq (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ b M, 3 ≤ b → b + 2 ≤ M → M + 1 ≤ 2 * b → HALFSq L b M) :
    ExactnessHypothesis p L (fun r => 2 * r - 1) :=
  exactness_of_top (topWitnessHypothesis_of_halfSq p L H)

variable {R : Type} [Field R] [CharP R p] (T : Template R)

/-- **Linear onset (T1–T4, PC and NS, every prime), CONDITIONAL only on `HALFSq` in the window**
(over the algebraic closure of the coefficient field). -/
theorem linear_of_halfSq
    (H : ∀ b M, 3 ≤ b → b + 2 ≤ M → M + 1 ≤ 2 * b → HALFSq (AlgebraicClosure R) b M) :
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
  BExact.linear_of_dcp' p T fun _ _ hb hN =>
    dcpHyp_of_halfSq hb (by omega) fun b' M h3 _ h1 h2 => H b' M h3 h1 h2

end Final

end ClaudeDCP
