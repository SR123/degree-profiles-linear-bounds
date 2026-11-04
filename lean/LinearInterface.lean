/-
Claude, 26 Sep 2026.  The interface for a linear onset.

The template transfer of Cycle 013 uses a witness only to make the actual shifted functor
`canonicalΨ = ker z / (ker z ∩ im z)` exact on the canonical class.  This file states that
exactness itself as the hypothesis, so that either route to a linear bound plugs in:

* a witness family with budget `W` gives `ExactnessHypothesis p L W` (`exactness_of_top`);
* an exact periodic equivalence in the stable range `n > 2r` (the range of Hone–Klein–Pauwels–
  Sherman–Yacobi–Zhang, Thm 8.5.3, as imported by the manuscript) is literally
  `ExactnessHypothesis p L (fun r => 2 * r + 1)`.

From `ExactnessHypothesis p L W` with `W` monotone we get (P) with onset `wOnset W`
(`periodic_of_exactness`).  For `W r = 2r+1` the onset is Stage 5's `onset k s n₀`, and Stage 5's
`T2_linear`, `T3_linear`, `T4_peaks` give the manuscript's linear corollaries
(`linear_of_exactness`).  For a general linear budget `W r = C r + D` the T2 bound is
`linear_T2_general`.

Nothing here proves the hypothesis.  It is an interface, and every theorem that uses it says so.
-/
import PFinal

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace ClaudeLinear
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle012 SelfContainedCycle013
open ClaudeWitnessTransfer ClaudeC017 ClaudeCP

/-! ### The hypothesis -/

section Hyp
variable {K : Type} [Field K]

/-- The actual shifted functor at support `r` is exact on the canonical class. -/
def ShiftedExact (p a n r : ℕ) [Fact p.Prime] (c : Fin a → K) : Prop :=
  PreservesFiniteLimits (canonicalΨ p a n r c) ∧ PreservesFiniteColimits (canonicalΨ p a n r c)

/-- **Exactness with budget `W`**: for every support `r`, every `p`-power `p^a > r` and every
retained rank `n ≥ W r`, some generic `c` makes the actual shifted functor exact. -/
def ExactnessHypothesis (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharP L p] (W : ℕ → ℕ) :
    Prop :=
  ∀ r a n : ℕ, r < p ^ a → W r ≤ n → ∃ c : Fin a → L, Generic p c ∧ ShiftedExact p a n r c

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p]

/-- A smaller budget is a stronger hypothesis. -/
theorem ExactnessHypothesis.mono {W W' : ℕ → ℕ} (hWW : ∀ r, W r ≤ W' r)
    (H : ExactnessHypothesis p L W) : ExactnessHypothesis p L W' :=
  fun r a n hr hn => H r a n hr (le_trans (hWW r) hn)

/-- **Route (a) plugs in.**  A top-power witness family with budget `W` gives exactness with
the same budget. -/
theorem exactness_of_top {W : ℕ → ℕ} (H : TopWitnessHypothesis p L W) :
    ExactnessHypothesis p L W := by
  intro r a n hr hn
  obtain ⟨c, hc, w, hw⟩ := H r a n hr hn
  exact ⟨c, hc, top_preserves_finiteLimits hc hr hw le_rfl,
    top_preserves_finiteColimits hc hr hw le_rfl⟩

/-- The unconditional instance: Cycle 017's triangular budget, over any algebraically closed
field of characteristic `p`. -/
theorem exactness_triW (L : Type) [Field L] [IsAlgClosed L] [CharP L p] :
    ExactnessHypothesis p L triW :=
  exactness_of_top (topWitnessHypothesis_of_isAlgClosed p L)

end Hyp

/-! ### One transfer step from exactness -/

section Step
variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem template_step_of_exact (T : Template K) {d a n : ℕ} (hd : 1 ≤ d) (hn0 : T.n0 ≤ n)
    (hrq : T.k * d + T.s < p ^ a) {c : Fin a → K} (hc : Generic p c)
    (hE : ShiftedExact p a n (T.k * d + T.s) c) :
    (Refutes (T.inst (n + p ^ a)) d ↔ Refutes (T.inst n) d) ∧
    (NSRefutes (T.inst (n + p ^ a)) d ↔ NSRefutes (T.inst n) d) := by
  haveI := hE.1
  haveI := hE.2
  letI : (canonicalΨ p a n (T.k * d + T.s) c).PreservesZeroMorphisms := inferInstance
  let m5 := canonicalM5w (n := n) (r := T.k * d + T.s) hc hrq
  exact ⟨template_pc_step_exact T (F := canonicalΨ p a n (T.k * d + T.s) c)
      hd (by omega) hn0 m5,
    template_ns_step_exact T (F := canonicalΨ p a n (T.k * d + T.s) c) (by omega) hn0 m5⟩

end Step

/-! ### (P) from exactness -/

section Profiles
variable {R : Type} [Field R] (T : Template R) (p : ℕ) [Fact p.Prime] (L : Type) [Field L]
  [CharP L p] [Algebra R L]

theorem step_of_exactness {W : ℕ → ℕ} (H : ExactnessHypothesis p L W) {d a n : ℕ}
    (hd : 1 ≤ d) (hn0 : T.n0 ≤ n) (hW : W (T.k * d + T.s) ≤ n) (hrq : T.k * d + T.s < p ^ a) :
    (T.pcProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ T.pcProfile n ≤ (d : ℕ∞)) ∧
    (T.nsProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ T.nsProfile n ≤ (d : ℕ∞)) := by
  obtain ⟨c, hc, hE⟩ := H (T.k * d + T.s) a n hrq hW
  have hh := template_step_of_exact (T.map (algebraMap R L)) hd hn0 hrq hc hE
  rw [← pcDegree_le_iff, ← pcDegree_le_iff, ← nsDegree_le_iff, ← nsDegree_le_iff] at hh
  change ((T.map (algebraMap R L)).pcProfile (n + p ^ a) ≤ d ↔
    (T.map (algebraMap R L)).pcProfile n ≤ d) ∧
    ((T.map (algebraMap R L)).nsProfile (n + p ^ a) ≤ d ↔
    (T.map (algebraMap R L)).nsProfile n ≤ d) at hh
  rw [T.pcProfile_map, T.pcProfile_map, T.nsProfile_map, T.nsProfile_map] at hh
  exact hh

/-- **(P) from exactness with any monotone budget.** -/
theorem periodic_of_exactness {W : ℕ → ℕ} (hWm : Monotone W)
    (H : ExactnessHypothesis p L W) :
    PeriodicProfile T.pcProfile (wOnset T.k T.s T.n0 W) (period p T.k T.s) ∧
    PeriodicProfile T.nsProfile (wOnset T.k T.s T.n0 W) (period p T.k T.s) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hge : ∀ d, d + 1 ≤ wOnset T.k T.s T.n0 W d := by
    intro d
    unfold wOnset
    split
    · have := T.hn0; omega
    · exact le_trans (onset_ge T.s T.hk T.hn0 d) (le_max_left _ _)
  have key : ∀ (h : ℕ → ℕ∞), ZeroStable T.n0 h →
      (∀ d a n, 1 ≤ d → T.n0 ≤ n → W (T.k * d + T.s) ≤ n → T.k * d + T.s < p ^ a →
        (h (n + p ^ a) ≤ (d : ℕ∞) ↔ h n ≤ (d : ℕ∞))) →
      PeriodicProfile h (wOnset T.k T.s T.n0 W) (period p T.k T.s) := by
    intro h h0 hstep
    refine ⟨wOnset_mono T hWm, hge, period_pos hp T.k T.s, ?_⟩
    intro d t htd n m hn hm hc
    by_cases ht : t = 0
    · subst ht
      have hN0 : T.n0 ≤ wOnset T.k T.s T.n0 W d := by
        unfold wOnset; split
        · exact le_refl _
        · exact le_trans (n0_le_onset _ _ _ d) (le_max_left _ _)
      exact h0 n m (le_trans hN0 hn) (le_trans hN0 hm)
    · have hd : 1 ≤ d := by omega
      have hon : wOnset T.k T.s T.n0 W d = max (onset T.k T.s T.n0 d) (W (T.k * d + T.s)) := by
        unfold wOnset; rw [if_neg (by omega)]
      rw [hon] at hn hm
      have hper : period p T.k T.s d = leastPowGt p (T.k * d + T.s) := by
        unfold period; rw [if_neg (by omega)]
      rw [hper] at hc
      obtain ⟨a, ha⟩ := leastPowGt_isPow hp (T.k * d + T.s)
      have hgt := leastPowGt_gt hp (T.k * d + T.s)
      rw [ha] at hc hgt
      have hkt : T.k * t ≤ T.k * d := Nat.mul_le_mul_left T.k htd
      have hWt : W (T.k * t + T.s) ≤ W (T.k * d + T.s) := hWm (by omega)
      have hn0d : T.n0 ≤ onset T.k T.s T.n0 d := n0_le_onset _ _ _ d
      refine congr_of_step (Pr := fun x => h x ≤ (t : ℕ∞)) (q := p ^ a)
        (B := max T.n0 (W (T.k * t + T.s))) ?_ ?_ ?_ hc
      · intro x hx
        exact hstep t a x (by omega) (le_trans (le_max_left _ _) hx)
          (le_trans (le_max_right _ _) hx) (by omega)
      · exact max_le (le_trans hn0d (le_trans (le_max_left _ _) hn))
          (le_trans hWt (le_trans (le_max_right _ _) hn))
      · exact max_le (le_trans hn0d (le_trans (le_max_left _ _) hm))
          (le_trans hWt (le_trans (le_max_right _ _) hm))
  exact ⟨key _ T.zeroStable_pc
      (fun d a n hd hn0 hW hrq => (step_of_exactness T p L H hd hn0 hW hrq).1),
    key _ T.zeroStable_ns
      (fun d a n hd hn0 hW hrq => (step_of_exactness T p L H hd hn0 hW hrq).2)⟩

end Profiles

/-! ### The stable range `n > 2r`: Stage 5's onset and its linear corollaries -/

section Stable

/-- The budget of the stable range. -/
def stableW (r : ℕ) : ℕ := 2 * r + 1

theorem stableW_mono : Monotone stableW := fun x y h => by unfold stableW; omega

/-- With the stable-range budget the onset is exactly Stage 5's `onset k s n₀`. -/
theorem wOnset_stableW (k s n0 : ℕ) : wOnset k s n0 stableW = onset k s n0 := by
  funext d
  unfold wOnset onset stableW
  split
  · rfl
  · exact max_eq_left (le_max_right _ _)

variable {R : Type} [Field R] (p : ℕ) [Fact p.Prime] [CharP R p] (T : Template R)

/-- **Linear corollaries, conditional on exactness in the stable range.**  If the actual shifted
functor is exact whenever `n > 2r` (over the algebraic closure of the coefficient field), then
both profiles satisfy (P) with Stage 5's onset `max(n₀, 2(kd+s)+1)`, exactly one of T1–T4 holds,
and: in T2, `h(n) > ⌊(n-2s-1)/(2k)⌋` for every `n ≥ n₀`; in T3 the same bound holds on the hard
residue classes beyond `N(D)`; in T4 there are arbitrarily large peaks `h(n) = d` with
`n ≤ (p+2)(kd+s)`. -/
theorem linear_of_exactness (H : ExactnessHypothesis p (AlgebraicClosure R) stableW) :
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
        (n : ℚ) / ((p + 2) * T.k) - T.s / T.k ≤ d) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hP := periodic_of_exactness T p (AlgebraicClosure R) stableW_mono H
  rw [wOnset_stableW] at hP
  intro h hh
  have P : PeriodicProfile h (onset T.k T.s T.n0) (period p T.k T.s) := by
    rcases hh with rfl | hh
    · exact hP.1
    · rw [Set.mem_singleton_iff] at hh; subst hh; exact hP.2
  exact ⟨P, P.exactly_one, fun h2 n x hn hx => T2_linear T.hk P h2 hn x hx,
    fun h3 => T3_linear T.hk P h3, fun h4 B => T4_peaks hp T.hk P h4 B⟩

end Stable

/-! ### Any linear budget: the T2 rate -/

section GeneralLinear
variable {k s n0 C D : ℕ} {h : ℕ → ℕ∞} {Q : ℕ → ℕ}

/-- The level `⌊(⌊(n-D)/C⌋ - s)/k⌋` has onset at most `n` for the budget `W r = C r + D`,
once `C ≥ 2`, `D ≥ 1` and `n ≥ n₀`. -/
theorem wOnset_linear_le (hk : 1 ≤ k) (hC : 2 ≤ C) (hD : 1 ≤ D) {n : ℕ} (hn : n0 ≤ n) :
    wOnset k s n0 (fun r => C * r + D) (((n - D) / C - s) / k) ≤ n := by
  set d := ((n - D) / C - s) / k with hd
  unfold wOnset
  split
  · exact hn
  · rename_i hd0
    have hkd : k * d ≤ (n - D) / C - s := Nat.mul_div_le _ _
    have h1 : 1 ≤ k * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hd0)
    have hx : k * d + s ≤ (n - D) / C := by omega
    have hC' : C * ((n - D) / C) ≤ n - D := Nat.mul_div_le _ _
    have hCx : C * (k * d + s) ≤ n - D := le_trans (Nat.mul_le_mul_left C hx) hC'
    have hND : D ≤ n := by
      by_contra hlt
      have : (n - D) / C = 0 := by rw [show n - D = 0 by omega]; simp
      omega
    have h2 : 2 * (k * d + s) ≤ C * (k * d + s) := Nat.mul_le_mul_right _ hC
    refine max_le ?_ (by show C * (k * d + s) + D ≤ n; omega)
    unfold onset
    rw [if_neg hd0]
    exact max_le hn (by omega)

/-- **T2 with any linear budget `C r + D`:** `h(n) > ⌊(⌊(n-D)/C⌋ - s)/k⌋` for all `n ≥ n₀`. -/
theorem linear_T2_general (hk : 1 ≤ k) (hC : 2 ≤ C) (hD : 1 ≤ D)
    (P : PeriodicProfile h (wOnset k s n0 (fun r => C * r + D)) Q)
    (h2 : IsT2 h (wOnset k s n0 (fun r => C * r + D))) {n : ℕ} (hn : n0 ≤ n) :
    ((((n - D) / C - s) / k : ℕ) : ℕ∞) < h n :=
  P.T2_gt h2 (wOnset_linear_le hk hC hD hn)

end GeneralLinear

/-- **Any linear budget, both proof systems.**  If exactness holds with budget `C r + D`
(`C ≥ 2`, `D ≥ 1`) then in type T2 both profiles exceed `⌊(⌊(n-D)/C⌋ - s)/k⌋` at every
`n ≥ n₀`. -/
theorem T2_of_linear_exactness {R : Type} [Field R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (T : Template R) {C D : ℕ} (hC : 2 ≤ C) (hD : 1 ≤ D)
    (H : ExactnessHypothesis p (AlgebraicClosure R) (fun r => C * r + D)) :
    (IsT2 T.pcProfile (wOnset T.k T.s T.n0 (fun r => C * r + D)) → ∀ n, T.n0 ≤ n →
      ((((n - D) / C - T.s) / T.k : ℕ) : ℕ∞) < T.pcProfile n) ∧
    (IsT2 T.nsProfile (wOnset T.k T.s T.n0 (fun r => C * r + D)) → ∀ n, T.n0 ≤ n →
      ((((n - D) / C - T.s) / T.k : ℕ) : ℕ∞) < T.nsProfile n) := by
  have hm : Monotone (fun r : ℕ => C * r + D) := fun x y hxy => by
    simp only; exact Nat.add_le_add_right (Nat.mul_le_mul_left C hxy) D
  have hP := periodic_of_exactness T p (AlgebraicClosure R) hm H
  exact ⟨fun h2 n hn => linear_T2_general T.hk hC hD hP.1 h2 hn,
    fun h2 n hn => linear_T2_general T.hk hC hD hP.2 h2 hn⟩

end ClaudeLinear
