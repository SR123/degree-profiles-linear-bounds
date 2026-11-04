/-
Stage 2, step 6: the connected pipeline and the endpoint theorem.

  representation-theoretic inputs M1–M5          (hypothesis `DeletionHypothesis`)
    ⟹ one deletion step for actual PC / NS refutability of the instances   (`pc_step`, `ns_step`)
    ⟹ threshold periodicity of the actual profiles                         (`thresholdPeriodic_*`)
    ⟹ hypothesis (P) with onset `N(d)` and period `Q(d)`                   (`periodicProfile_*`)
    ⟹ four-type classification and the linear bounds                       (`uniform_template_linear_bounds`)

The profiles are `T.pcProfile n = PC.pcDegree (T.inst n)` and
`T.nsProfile n = NS.nsDegree (T.inst n)`: the degrees of the actual proof systems on the actual
polynomial instances of the template.

What is NOT assumed: periodicity, any statement about consequence spaces or their transport,
any refutability equivalence, exactness of `Φ`, tensor-closure of the bounded-tail categories.
The hypothesis mentions no template, polynomial or proof system.
-/
import DegreeProfilesReview.TemplateCompat
import DegreeProfilesReview.LinearBounds

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace DegreeProfilesReview.Uniform

open DegreeProfilesReview.Deletion DegreeProfilesReview.Transport DegreeProfilesReview.Profiles

/-! ### The hypothesis -/

/-- **The representation-theoretic hypothesis.**  For every degree `d ≥ 1`, every `p`-power
`q = p^a` exceeding `r = k d + s`, and every `n ≥ n₀` with `n > 2r` (the STRICT range), the
five inputs M1–M5 are available for `(p, q, r, n)` over the field `K`. -/
def DeletionHypothesis (K : Type) [Field K] (p k s n0 : ℕ) : Prop :=
  ∀ d a n : ℕ, 1 ≤ d → k * d + s < p ^ a → n0 ≤ n → 2 * (k * d + s) < n →
    Nonempty (DeletionInterface.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p (p ^ a) (k * d + s) n)

/-! ### One deletion step -/

namespace Template

variable {K : Type} [Field K] (T : Template K)

/-- **One deletion step, ordinary PC.**  For `d ≥ 1`, `n ≥ n₀`, `n > 2(kd+s)`: the instance at
size `n + q` has a PC refutation of degree `≤ d` iff the instance at size `n` has one. -/
theorem pc_step {p q n d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) (hn0 : T.n0 ≤ n)
    (hn : 2 * (T.k * d + T.s) < n)
    (I : DeletionInterface.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p q (T.k * d + T.s) n) :
    PC.Refutes (T.inst (n + q)) d ↔ PC.Refutes (T.inst n) d := by
  haveI : I.m3.Φ.IsEquivalence := I.m3.isEquivalence hp hn
  rw [PC.refutes_iff_one_mem_Vinf, PC.refutes_iff_one_mem_Vinf, PC.mem_Vinf_iff,
    PC.mem_Vinf_iff]
  apply exists_congr
  intro j
  rw [← T.pc_stage_iff hd I.m4N (le_trans hn0 (Nat.le_add_right n q)) j,
    ← T.pc_stage_iff hd I.m4n hn0 j]
  exact const_mem_iff I.m3.Φ (T.ΦCompat hd I.m5) j

/-- **One deletion step, Nullstellensatz.** -/
theorem ns_step {p q n d : ℕ} (hp : 2 ≤ p) (hn0 : T.n0 ≤ n)
    (hn : 2 * (T.k * d + T.s) < n)
    (I : DeletionInterface.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p q (T.k * d + T.s) n) :
    NS.NSRefutes (T.inst (n + q)) d ↔ NS.NSRefutes (T.inst n) d := by
  haveI : I.m3.Φ.IsEquivalence := I.m3.isEquivalence hp hn
  rw [NS.nsRefutes_iff_one_mem_NSspan, NS.nsRefutes_iff_one_mem_NSspan,
    ← T.ns_iff I.m4N (le_trans hn0 (Nat.le_add_right n q)), ← T.ns_iff I.m4n hn0]
  exact image_membership_iff I.m3.Φ _ _ _ _ (I.m5.δ _ _) (I.m5.δ _ _) (I.m5.δ _ _)
    (I.m5.δ_mat _ _ _) (I.m5.δ_mat _ _ _)

end Template

/-! ### Iterating the step -/

/-- A predicate that is invariant under `n ↦ n + q` beyond `B` is constant on residue classes
modulo `q` beyond `B`. -/
theorem congr_of_step {Pr : ℕ → Prop} {q B : ℕ} (hstep : ∀ n, B ≤ n → (Pr (n + q) ↔ Pr n))
    {n m : ℕ} (hn : B ≤ n) (hm : B ≤ m) (h : n % q = m % q) : Pr n ↔ Pr m := by
  have key : ∀ (n : ℕ), B ≤ n → ∀ j : ℕ, Pr (n + j * q) ↔ Pr n := by
    intro n hn j
    induction j with
    | zero => rw [Nat.zero_mul, Nat.add_zero]
    | succ j ih =>
      have : n + (j + 1) * q = (n + j * q) + q := by ring
      rw [this, hstep _ (le_trans hn (Nat.le_add_right _ _)), ih]
  rcases Nat.le_total n m with hnm | hnm
  · have hdiv : q ∣ m - n := (Nat.modEq_iff_dvd' hnm).mp h
    obtain ⟨j, hj⟩ := hdiv
    have : m = n + j * q := by rw [Nat.mul_comm] at hj; omega
    rw [this]
    exact (key n hn j).symm
  · have hdiv : q ∣ n - m := (Nat.modEq_iff_dvd' hnm).mp h.symm
    obtain ⟨j, hj⟩ := hdiv
    have : n = m + j * q := by rw [Nat.mul_comm] at hj; omega
    rw [this]
    exact key m hm j

/-! ### Threshold periodicity of the actual profiles -/

section Periodicity

variable {R : Type} [Field R] (T : Template R) {p : ℕ} (hp : 2 ≤ p)
  (K : Type) [Field K] [Algebra R K]

include hp in
/-- **`thm:PC` for uniform templates**, from M1–M5. -/
theorem thresholdPeriodic_pc
    (H : DeletionHypothesis.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    ThresholdPeriodic p T.k T.s T.n0 T.pcProfile := by
  intro d hd a ha n m hn hm h2n h2m hc
  rw [← T.pcProfile_map (K := K) n, ← T.pcProfile_map (K := K) m]
  unfold Template.pcProfile
  rw [PC.pcDegree_le_iff, PC.pcDegree_le_iff]
  refine congr_of_step (Pr := fun n => PC.Refutes ((T.map (algebraMap R K)).inst n) d)
    (B := max T.n0 (2 * (T.k * d + T.s) + 1)) (q := p ^ a) ?_
    (max_le hn h2n) (max_le hm h2m) hc
  intro n' hn'
  have h1 : T.n0 ≤ n' := le_trans (le_max_left _ _) hn'
  have h2 : 2 * (T.k * d + T.s) < n' := le_trans (le_max_right _ _) hn'
  obtain ⟨I⟩ := H d a n' hd ha h1 h2
  exact (T.map (algebraMap R K)).pc_step hp hd h1 h2 I

include hp in
/-- **`thm:NS` for uniform templates**, from M1–M5. -/
theorem thresholdPeriodic_ns
    (H : DeletionHypothesis.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    ThresholdPeriodic p T.k T.s T.n0 T.nsProfile := by
  intro d hd a ha n m hn hm h2n h2m hc
  rw [← T.nsProfile_map (K := K) n, ← T.nsProfile_map (K := K) m]
  unfold Template.nsProfile
  rw [NS.nsDegree_le_iff, NS.nsDegree_le_iff]
  refine congr_of_step (Pr := fun n => NS.NSRefutes ((T.map (algebraMap R K)).inst n) d)
    (B := max T.n0 (2 * (T.k * d + T.s) + 1)) (q := p ^ a) ?_
    (max_le hn h2n) (max_le hm h2m) hc
  intro n' hn'
  have h1 : T.n0 ≤ n' := le_trans (le_max_left _ _) hn'
  have h2 : 2 * (T.k * d + T.s) < n' := le_trans (le_max_right _ _) hn'
  obtain ⟨I⟩ := H d a n' hd ha h1 h2
  exact (T.map (algebraMap R K)).ns_step hp h1 h2 I

include hp in
/-- Hypothesis (P) for the actual PC profile, with `N(d) = max(n₀, 2(kd+s)+1)` and `Q(d)` the
least `p`-power above `kd+s`.  Degree-zero stabilisation is proved, not assumed. -/
theorem periodicProfile_pc
    (H : DeletionHypothesis.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    PeriodicProfile T.pcProfile (onset T.k T.s T.n0) (period p T.k T.s) :=
  template_periodicProfile hp T.hk T.hn0 (thresholdPeriodic_pc T hp K H) T.zeroStable_pc

include hp in
theorem periodicProfile_ns
    (H : DeletionHypothesis.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    PeriodicProfile T.nsProfile (onset T.k T.s T.n0) (period p T.k T.s) :=
  template_periodicProfile hp T.hk T.hn0 (thresholdPeriodic_ns T hp K H) T.zeroStable_ns

end Periodicity

/-! ### The endpoint -/

/-- The conclusions of `thm:four`, `cor:linear` and `cor:peaks` for one profile `h` with the
template's onset and period. -/
structure LinearBoundsFor (p k s n0 : ℕ) (h : ℕ → ℕ∞) : Prop where
  /-- hypothesis (P) -/
  periodic : PeriodicProfile h (onset k s n0) (period p k s)
  /-- exactly one of the four types -/
  four_types :
    (IsT1 h ∧ ¬ IsT2 h (onset k s n0) ∧ ¬ IsT3 h (onset k s n0) ∧ ¬ IsT4 h (onset k s n0)) ∨
    (¬ IsT1 h ∧ IsT2 h (onset k s n0) ∧ ¬ IsT3 h (onset k s n0) ∧ ¬ IsT4 h (onset k s n0)) ∨
    (¬ IsT1 h ∧ ¬ IsT2 h (onset k s n0) ∧ IsT3 h (onset k s n0) ∧ ¬ IsT4 h (onset k s n0)) ∨
    (¬ IsT1 h ∧ ¬ IsT2 h (onset k s n0) ∧ ¬ IsT3 h (onset k s n0) ∧ IsT4 h (onset k s n0))
  /-- type (ii): every value beyond `n₀` exceeds `⌊(n - 2s - 1)/(2k)⌋` -/
  T2_bound : IsT2 h (onset k s n0) → ∀ n, n0 ≤ n → ∀ x : ℕ, h n = (x : ℕ∞) →
    ((n : ℤ) - 2 * s - 1) / (2 * k) < (x : ℤ)
  /-- type (iii): the same bound off an exceptional set of residues -/
  T3_bound : IsT3 h (onset k s n0) →
    ∃ (D : ℕ) (U : Set ℕ), U.Nonempty ∧ (∃ c, c < period p k s D ∧ c ∉ U) ∧
      ∀ n, onset k s n0 D ≤ n → 2 * k + 2 * s + 1 ≤ n → n % period p k s D ∉ U →
        (((n - 2 * s - 1) / (2 * k) : ℕ) : ℕ∞) < h n
  /-- type (iv): arbitrarily large finite peaks `h n = d ≥ n/((p+2)k) - s/k` -/
  T4_bound : IsT4 h (onset k s n0) → ∀ B : ℕ,
    ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧ d ∈ E h (onset k s n0) ∧ h n = (d : ℕ∞) ∧
      n ≤ (p + 2) * (k * d + s) ∧ (n : ℚ) / ((p + 2) * k) - s / k ≤ d

theorem linearBoundsFor_of_periodic {p k s n0 : ℕ} {h : ℕ → ℕ∞} (hp : 2 ≤ p) (hk : 1 ≤ k)
    (P : PeriodicProfile h (onset k s n0) (period p k s)) : LinearBoundsFor p k s n0 h where
  periodic := P
  four_types := P.exactly_one
  T2_bound := fun h2 _ hn x hx => T2_linear hk P h2 hn x hx
  T3_bound := fun h3 => T3_linear hk P h3
  T4_bound := fun h4 B => T4_peaks hp hk P h4 B

/-- **Endpoint theorem.**  Let `T` be a uniform polynomial template with coefficients in a
field `R`, parameters `k, s, n₀`, and let `K` be an extension field of `R` over which the
representation-theoretic inputs M1–M5 hold in the strict range (`DeletionHypothesis`).  Then
the ACTUAL ordinary-PC and Nullstellensatz degree profiles of `T`,

  `n ↦ PC.pcDegree (T.inst n)`   and   `n ↦ NS.nsDegree (T.inst n)`,

satisfy hypothesis (P) with onset `max(n₀, 2(kd+s)+1)` and period the least `p`-power above
`kd+s`, fall into exactly one of the four types, and satisfy the linear bounds of `cor:linear`
and `cor:peaks`; moreover PC ≤ NS pointwise and type-(iv) PC peaks are simultaneous NS lower
bounds. -/
theorem uniform_template_linear_bounds {R : Type} [Field R] (T : Template R) {p : ℕ}
    (hp : 2 ≤ p) (K : Type) [Field K] [Algebra R K]
    (H : DeletionHypothesis.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    LinearBoundsFor p T.k T.s T.n0 (fun n => PC.pcDegree (T.inst n)) ∧
    LinearBoundsFor p T.k T.s T.n0 (fun n => NS.nsDegree (T.inst n)) ∧
    (∀ n, PC.pcDegree (T.inst n) ≤ NS.nsDegree (T.inst n)) ∧
    (IsT4 (fun n => PC.pcDegree (T.inst n)) (onset T.k T.s T.n0) → ∀ B : ℕ,
      ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧ PC.pcDegree (T.inst n) = (d : ℕ∞) ∧
        (d : ℕ∞) ≤ NS.nsDegree (T.inst n) ∧
        (n : ℚ) / ((p + 2) * T.k) - T.s / T.k ≤ d) :=
  ⟨linearBoundsFor_of_periodic hp T.hk (periodicProfile_pc T hp K H),
    linearBoundsFor_of_periodic hp T.hk (periodicProfile_ns T hp K H),
    T.pcProfile_le_nsProfile,
    fun h4 B => simultaneous_peaks hp T.hk (periodicProfile_pc T hp K H) h4
      T.pcProfile_le_nsProfile B⟩

end DegreeProfilesReview.Uniform
