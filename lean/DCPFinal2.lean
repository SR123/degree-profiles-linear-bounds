/-
Agent D, round 4 (26 Sep 2026).  Final assembly, improved window: with `HALF_b(b+2)` proved
(`DCPHalf2.half_succ_succ`), the only remaining input is `HALFSq K b M` for
`b + 3 ≤ M ≤ 2b - 1` (hence `b ≥ 4`).

* `dcpHyp_of_halfSq2` : B's `DCPHyp b N` (`1 ≤ b ≤ N`) from `HALFSq` in the reduced window.
* `dcpHyp_le_three` : B's `DCPHyp b N` for `1 ≤ b ≤ 3`, `b ≤ N`, UNCONDITIONALLY.
* `topWitnessHypothesis_of_halfSq2`, `exactness_of_halfSq2`, `linear_of_halfSq2` : Theorem A, the
  exactness hypothesis and the linear onset, CONDITIONAL only on `HALFSq` for `4 ≤ b`,
  `b + 3 ≤ M ≤ 2b - 1`.
-/
import DCPFinal
import DCPHalf2

set_option autoImplicit false

namespace ClaudeDCP

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle012 SelfContainedCycle013
open ClaudeWitnessTransfer ClaudeC017 ClaudeCP ClaudeLinear


/-- DCP in rook form for all `N`, from `HALF` in the reduced window (Lemma D from B's `lemmaD`). -/
theorem dcpr_of_halfWindow2 {α : Type} [Fintype α] [DecidableEq α] {K : Type} [CommRing K]
    (b : ℕ) (hhalf : ∀ b' N, b' ≤ b → b' + 3 ≤ N → N + 1 ≤ 2 * b' → HALF α K b' N) :
    ∀ N, DCPR α K b N :=
  dcpr_all2 (fun _ _ _ hC => colSplit hC) b hhalf

/-- **B's `DCPHyp b N` from `HALFSq` in the reduced window `b' + 3 ≤ M ≤ 2b' - 1`.** -/
theorem dcpHyp_of_halfSq2 {K : Type} [Field K] {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N)
    (H : ∀ b' M, 4 ≤ b' → b' ≤ b → b' + 3 ≤ M → M + 1 ≤ 2 * b' → HALFSq K b' M) :
    BExact.DCPHyp (K := K) b N :=
  dcpHypB_of_dcpr hb hbN (dcpr_of_halfWindow2 b
    (fun b' M hb' h1 h2 => half_of_halfSq (H b' M (by omega) hb' h1 h2)) N)

/-- **B's `DCPHyp b N` for `1 ≤ b ≤ 3`, unconditionally.** -/
theorem dcpHyp_le_three {K : Type} [Field K] {b N : ℕ} (hb : 1 ≤ b) (hb3 : b ≤ 3)
    (hbN : b ≤ N) : BExact.DCPHyp (K := K) b N :=
  dcpHypB_of_dcpr hb hbN (dcpr_le_three (fun _ _ _ hC => colSplit hC) hb3 N)

section Final

variable (p : ℕ) [Fact p.Prime]

/-- **Theorem A, CONDITIONAL only on `HALFSq` for `4 ≤ b`, `b + 3 ≤ M ≤ 2b - 1`.** -/
theorem topWitnessHypothesis_of_halfSq2 (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ b M, 4 ≤ b → b + 3 ≤ M → M + 1 ≤ 2 * b → HALFSq L b M) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  BExact.topWitnessHypothesis_of_dcp' p L fun _ _ hb hN =>
    dcpHyp_of_halfSq2 hb (by omega) fun b' M h4 _ h1 h2 => H b' M h4 h1 h2

/-- **Exactness with budget `2r - 1`, CONDITIONAL only on `HALFSq` in the reduced window.** -/
theorem exactness_of_halfSq2 (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ b M, 4 ≤ b → b + 3 ≤ M → M + 1 ≤ 2 * b → HALFSq L b M) :
    ExactnessHypothesis p L (fun r => 2 * r - 1) :=
  exactness_of_top (topWitnessHypothesis_of_halfSq2 p L H)

variable {R : Type} [Field R] [CharP R p] (T : Template R)

/-- **Linear onset (T1–T4, PC and NS, every prime), CONDITIONAL only on `HALFSq` for `4 ≤ b`,
`b + 3 ≤ M ≤ 2b - 1`** (over the algebraic closure of the coefficient field). -/
theorem linear_of_halfSq2
    (H : ∀ b M, 4 ≤ b → b + 3 ≤ M → M + 1 ≤ 2 * b → HALFSq (AlgebraicClosure R) b M) :
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
    dcpHyp_of_halfSq2 hb (by omega) fun b' M h4 _ h1 h2 => H b' M h4 h1 h2

end Final

end ClaudeDCP
