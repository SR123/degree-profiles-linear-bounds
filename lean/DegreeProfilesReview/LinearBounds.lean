/-
Prompt 06, part 2: the template onset `N(d)`, the period `Q(d)`, instantiation of
hypothesis (P) from the threshold theorem, the floor inversion, and the peak bounds
(manuscript `cor:linear`, `cor:peaks`).

The threshold theorem for polynomial templates is an **explicit hypothesis**
(`ThresholdPeriodic`, `ZeroStable`).  This file proves nothing about polynomials.
Only `2 ≤ p` is used about `p` (so the results hold in particular for primes).
-/
import DegreeProfilesReview.DegreeProfiles
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic

namespace DegreeProfilesReview.Profiles

/-! ### The least `p`-power strictly above `m` -/

theorem exists_pow_gt {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : ∃ a, m < p ^ a :=
  ⟨m, Nat.lt_pow_self (by omega)⟩

/-- The least power of `p` strictly greater than `m` (junk value `1` if `p < 2`). -/
def leastPowGt (p m : ℕ) : ℕ :=
  if hp : 2 ≤ p then p ^ Nat.find (exists_pow_gt hp m) else 1

theorem leastPowGt_gt {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : m < leastPowGt p m := by
  unfold leastPowGt
  rw [dif_pos hp]
  exact Nat.find_spec (exists_pow_gt hp m)

theorem leastPowGt_isPow {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : ∃ a, leastPowGt p m = p ^ a := by
  unfold leastPowGt
  rw [dif_pos hp]
  exact ⟨_, rfl⟩

theorem leastPowGt_le {p : ℕ} (hp : 2 ≤ p) {m a : ℕ} (h : m < p ^ a) :
    leastPowGt p m ≤ p ^ a := by
  unfold leastPowGt
  rw [dif_pos hp]
  exact Nat.pow_le_pow_right (by omega) (Nat.find_min' _ h)

theorem leastPowGt_pos {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : 0 < leastPowGt p m :=
  lt_of_le_of_lt (Nat.zero_le m) (leastPowGt_gt hp m)

/-- `Q(d) ≤ p (kd+s)` in the manuscript: the least `p`-power above `m ≥ 1` is at most `p m`. -/
theorem leastPowGt_le_mul {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (hm : 1 ≤ m) :
    leastPowGt p m ≤ p * m := by
  unfold leastPowGt
  rw [dif_pos hp]
  set a := Nat.find (exists_pow_gt hp m) with ha
  have hspec : m < p ^ a := Nat.find_spec (exists_pow_gt hp m)
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hspec
    omega
  obtain ⟨a', ha'⟩ := Nat.exists_eq_succ_of_ne_zero ha0
  have hmin : ¬ m < p ^ a' := Nat.find_min (exists_pow_gt hp m) (by omega)
  rw [not_lt] at hmin
  rw [ha', pow_succ, mul_comm]
  exact Nat.mul_le_mul_left p hmin

/-! ### Onset and period of the template -/

/-- `N(0) = n₀`, `N(d) = max{n₀, 2(kd+s)+1}` for `d ≥ 1`. -/
def onset (k s n0 d : ℕ) : ℕ :=
  if d = 0 then n0 else max n0 (2 * (k * d + s) + 1)

/-- `Q(0) = 1`, `Q(d)` = least `p`-power above `kd+s` for `d ≥ 1`. -/
def period (p k s d : ℕ) : ℕ :=
  if d = 0 then 1 else leastPowGt p (k * d + s)

theorem n0_le_onset (k s n0 d : ℕ) : n0 ≤ onset k s n0 d := by
  unfold onset
  split
  · exact le_refl _
  · exact le_max_left _ _

theorem onset_pos_level {k s n0 d : ℕ} (hd : 1 ≤ d) :
    onset k s n0 d = max n0 (2 * (k * d + s) + 1) := by
  unfold onset
  rw [if_neg (by omega)]

theorem onset_mono (k s n0 : ℕ) : Monotone (onset k s n0) := by
  intro d d' hdd
  by_cases hd : d = 0
  · subst hd
    unfold onset
    rw [if_pos rfl]
    split
    · exact le_refl _
    · exact le_max_left _ _
  · rw [onset_pos_level (by omega), onset_pos_level (by omega)]
    have : k * d ≤ k * d' := Nat.mul_le_mul_left k hdd
    apply max_le_max (le_refl _)
    omega

/-- `N(d) ≥ d + 1` (uses `k ≥ 1`, `n₀ ≥ 1`). -/
theorem onset_ge {k n0 : ℕ} (s : ℕ) (hk : 1 ≤ k) (hn0 : 1 ≤ n0) (d : ℕ) :
    d + 1 ≤ onset k s n0 d := by
  by_cases hd : d = 0
  · subst hd
    unfold onset
    rw [if_pos rfl]
    omega
  · rw [onset_pos_level (by omega)]
    have : d ≤ k * d := Nat.le_mul_of_pos_left d hk
    have h2 : 2 * (k * d + s) + 1 ≤ max n0 (2 * (k * d + s) + 1) := le_max_right _ _
    omega

theorem period_pos {p : ℕ} (hp : 2 ≤ p) (k s d : ℕ) : 0 < period p k s d := by
  unfold period
  split
  · norm_num
  · exact leastPowGt_pos hp _

/-- `Q(d) ≤ p (kd+s)` for `d ≥ 1`, `k ≥ 1`. -/
theorem period_le {p k : ℕ} (s : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) {d : ℕ} (hd : 1 ≤ d) :
    period p k s d ≤ p * (k * d + s) := by
  unfold period
  rw [if_neg (by omega)]
  apply leastPowGt_le_mul hp
  have : d ≤ k * d := Nat.le_mul_of_pos_left d hk
  omega

/-! ### The explicit hypotheses -/

/-- The template threshold theorem, exactly as permitted by Prompt 06: an *input*. -/
def ThresholdPeriodic (p k s n0 : ℕ) (h : ℕ → ℕ∞) : Prop :=
  ∀ t, 1 ≤ t → ∀ a, k * t + s < p ^ a → ∀ n m, n0 ≤ n → n0 ≤ m →
    2 * (k * t + s) < n → 2 * (k * t + s) < m → n % p ^ a = m % p ^ a →
    (h n ≤ (t : ℕ∞) ↔ h m ≤ (t : ℕ∞))

/-- Stabilisation of the degree-zero predicate beyond `n₀`: a separate *input*. -/
def ZeroStable (n0 : ℕ) (h : ℕ → ℕ∞) : Prop :=
  ∀ n m, n0 ≤ n → n0 ≤ m → (h n ≤ ((0 : ℕ) : ℕ∞) ↔ h m ≤ ((0 : ℕ) : ℕ∞))

/-- Prompt 06, target 1: from the threshold theorem, all thresholds `t ≤ d` share the
onset `N(d)` and the period `Q(d)`; i.e. hypothesis (P) holds. -/
theorem template_periodicProfile {p k s n0 : ℕ} {h : ℕ → ℕ∞}
    (hp : 2 ≤ p) (hk : 1 ≤ k) (hn0 : 1 ≤ n0)
    (hT : ThresholdPeriodic p k s n0 h) (h0 : ZeroStable n0 h) :
    PeriodicProfile h (onset k s n0) (period p k s) where
  N_mono := onset_mono k s n0
  N_ge := onset_ge s hk hn0
  Q_pos := period_pos hp k s
  periodic := by
    intro d t htd n m hn hm hc
    by_cases ht : t = 0
    · subst ht
      exact h0 n m (le_trans (n0_le_onset k s n0 d) hn) (le_trans (n0_le_onset k s n0 d) hm)
    · have hd : 1 ≤ d := by omega
      rw [onset_pos_level hd] at hn hm
      have hper : period p k s d = leastPowGt p (k * d + s) := by
        unfold period; rw [if_neg (by omega)]
      rw [hper] at hc
      obtain ⟨a, ha⟩ := leastPowGt_isPow hp (k * d + s)
      have hgt := leastPowGt_gt hp (k * d + s)
      rw [ha] at hc hgt
      have hkt : k * t ≤ k * d := Nat.mul_le_mul_left k htd
      have h1 : n0 ≤ n := le_trans (le_max_left _ _) hn
      have h2 : n0 ≤ m := le_trans (le_max_left _ _) hm
      have h3 : 2 * (k * d + s) + 1 ≤ n := le_trans (le_max_right _ _) hn
      have h4 : 2 * (k * d + s) + 1 ≤ m := le_trans (le_max_right _ _) hm
      exact hT t (by omega) a (by omega) n m h1 h2 (by omega) (by omega) hc

/-! ### The floor inversion -/

/-- Prompt 06, target 4 (natural-number form, with the largeness hypothesis explicit so
that truncated subtraction cannot hide a false small-`n` statement). -/
theorem inversion {k s n0 n : ℕ} (hk : 1 ≤ k) (hn0 : n0 ≤ n) (hbig : 2 * k + 2 * s + 1 ≤ n) :
    1 ≤ (n - 2 * s - 1) / (2 * k) ∧ onset k s n0 ((n - 2 * s - 1) / (2 * k)) ≤ n := by
  have hpos : 0 < 2 * k := by omega
  have h1 : 1 ≤ (n - 2 * s - 1) / (2 * k) := by
    rw [Nat.le_div_iff_mul_le hpos]
    omega
  refine ⟨h1, ?_⟩
  rw [onset_pos_level h1]
  apply max_le hn0
  have h2 : (n - 2 * s - 1) / (2 * k) * (2 * k) ≤ n - 2 * s - 1 := Nat.div_mul_le_self _ _
  have h3 : (n - 2 * s - 1) / (2 * k) * (2 * k) = 2 * (k * ((n - 2 * s - 1) / (2 * k))) := by
    ring
  omega

/-- The integer floor `⌊(n - 2s - 1)/(2k)⌋` (floor division in `ℤ`, no truncation)
agrees with the natural-number expression as soon as `n ≥ 2s + 1`. -/
theorem int_floor_eq {k s n : ℕ} (hn : 2 * s + 1 ≤ n) :
    ((n : ℤ) - 2 * s - 1) / (2 * k) = (((n - 2 * s - 1) / (2 * k) : ℕ) : ℤ) := by
  have : ((n : ℤ) - 2 * s - 1) = ((n - 2 * s - 1 : ℕ) : ℤ) := by omega
  rw [this]
  norm_cast

/-- Case (ii), linear form (manuscript `cor:linear`), valid at **every** size `n ≥ n₀`
with the genuine integer floor: `h(n) > ⌊(n-2s-1)/(2k)⌋`. -/
theorem T2_linear {p k s n0 : ℕ} {h : ℕ → ℕ∞}
    (hk : 1 ≤ k)
    (P : PeriodicProfile h (onset k s n0) (period p k s))
    (h2 : IsT2 h (onset k s n0)) {n : ℕ} (hn0 : n0 ≤ n) (x : ℕ) (hx : h n = (x : ℕ∞)) :
    ((n : ℤ) - 2 * s - 1) / (2 * k) < (x : ℤ) := by
  by_cases hbig : 2 * k + 2 * s + 1 ≤ n
  · obtain ⟨_, hons⟩ := inversion (n0 := n0) hk hn0 hbig
    have hlt := P.T2_gt h2 hons
    rw [hx] at hlt
    rw [int_floor_eq (by omega)]
    exact_mod_cast hlt
  · -- the floor is `≤ 0`; it remains to exclude `x = 0` when the floor is `0`
    have hfloor : ((n : ℤ) - 2 * s - 1) / (2 * k) < 1 := by
      apply Int.ediv_lt_of_lt_mul (by omega)
      omega
    have hx0 : x ≠ 0 := by
      rintro rfl
      have h0 : onset k s n0 0 ≤ n := by unfold onset; rw [if_pos rfl]; exact hn0
      have hlt := P.T2_gt h2 h0
      rw [hx] at hlt
      exact lt_irrefl _ hlt
    omega

/-- Case (iii), linear form on the hard residue classes: beyond `N(D)` and `2k+2s+1`,
every hard size has `h(n) > ⌊(n-2s-1)/(2k)⌋`. -/
theorem T3_linear {p k s n0 : ℕ} {h : ℕ → ℕ∞}
    (hk : 1 ≤ k)
    (P : PeriodicProfile h (onset k s n0) (period p k s))
    (h3 : IsT3 h (onset k s n0)) :
    ∃ (D : ℕ) (U : Set ℕ), U.Nonempty ∧ (∃ c, c < period p k s D ∧ c ∉ U) ∧
      ∀ n, onset k s n0 D ≤ n → 2 * k + 2 * s + 1 ≤ n → n % period p k s D ∉ U →
        (((n - 2 * s - 1) / (2 * k) : ℕ) : ℕ∞) < h n := by
  obtain ⟨D, _, _, U, _, hUne, hUproper, _, hhard⟩ := P.T3_structure h3
  refine ⟨D, U, hUne, hUproper, fun n hn hbig hnU => ?_⟩
  have hn0 : n0 ≤ n := le_trans (n0_le_onset k s n0 D) hn
  obtain ⟨_, hons⟩ := inversion (n0 := n0) hk hn0 hbig
  exact hhard n hn hnU _ hons

/-! ### Peaks in the fluctuating case -/

/-- A recurring level `d ≥ 1` has a representative in `[N(d), N(d)+Q(d))`. -/
theorem peak_representative {p k s n0 : ℕ} {h : ℕ → ℕ∞}
    (P : PeriodicProfile h (onset k s n0) (period p k s)) {d : ℕ}
    (hdE : d ∈ E h (onset k s n0)) :
    ∃ n, onset k s n0 d ≤ n ∧ n < onset k s n0 d + period p k s d ∧ h n = (d : ℕ∞) := by
  obtain ⟨c, hc, _, hrec⟩ := P.recurs hdE
  have hQ := P.Q_pos d
  refine ⟨onset k s n0 d + (c - onset k s n0 d) % period p k s d, by omega, ?_, ?_⟩
  · have := Nat.mod_lt (c - onset k s n0 d) hQ
    omega
  · apply hrec _ (by omega)
    rw [Nat.add_mod_mod]
    congr 1
    omega

/-- The size bound `n ≤ (p+2)(kd+s)` once `n₀` is dominated. -/
theorem peak_size_bound {p k s n0 d n : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hdom : n0 ≤ 2 * (k * d + s) + 1)
    (hn : n < onset k s n0 d + period p k s d) : n ≤ (p + 2) * (k * d + s) := by
  rw [onset_pos_level hd, max_eq_right hdom] at hn
  have hQ := period_le s hp hk hd
  have : (p + 2) * (k * d + s) = p * (k * d + s) + 2 * (k * d + s) := by ring
  omega

/-- The rational form `d ≥ n/((p+2)k) - s/k`. -/
theorem peak_rational {p k s d n : ℕ} (hk : 1 ≤ k) (hn : n ≤ (p + 2) * (k * d + s)) :
    (n : ℚ) / ((p + 2) * k) - s / k ≤ d := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have hp' : (0 : ℚ) < (p : ℚ) + 2 := by positivity
  have hn' : (n : ℚ) ≤ ((p : ℚ) + 2) * (k * d + s) := by exact_mod_cast hn
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  calc (n : ℚ) ≤ ((p : ℚ) + 2) * (k * d + s) := hn'
    _ = ((d : ℚ) + s / k) * ((p + 2) * k) := by field_simp

/-- Prompt 06, target 5 (manuscript `cor:peaks`): in type (iv) there are arbitrarily
large sizes `n` with a finite value `h n = d`, `n ≤ (p+2)(kd+s)`, hence
`d ≥ n/((p+2)k) - s/k`; and the levels `d` themselves are unbounded. -/
theorem T4_peaks {p k s n0 : ℕ} {h : ℕ → ℕ∞} (hp : 2 ≤ p) (hk : 1 ≤ k)
    (P : PeriodicProfile h (onset k s n0) (period p k s))
    (h4 : IsT4 h (onset k s n0)) (B : ℕ) :
    ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧ d ∈ E h (onset k s n0) ∧ h n = (d : ℕ∞) ∧
      n ≤ (p + 2) * (k * d + s) ∧ (n : ℚ) / ((p + 2) * k) - s / k ≤ d := by
  obtain ⟨d, hdE, hBd⟩ := h4.exists_gt (max B n0)
  have hd1 : 1 ≤ d := by
    have := le_max_left B n0
    omega
  have hdn0 : n0 ≤ 2 * (k * d + s) + 1 := by
    have h1 : d ≤ k * d := Nat.le_mul_of_pos_left d hk
    have h2 := le_max_right B n0
    omega
  obtain ⟨n, hn1, hn2, hn3⟩ := peak_representative P hdE
  have hsize := peak_size_bound hp hk hd1 hdn0 hn2
  have hge := P.N_ge d
  have hB := le_max_left B n0
  exact ⟨n, d, by omega, by omega, hdE, hn3, hsize, peak_rational hk hsize⟩

/-- Prompt 06, target 6: simultaneous NS/PC peaks.  The PC peak witnesses are used; the
only comparison input is the pointwise inequality `hPC ≤ hNS`.  No equality of profiles
or of recurring level sets is asserted. -/
theorem simultaneous_peaks {p k s n0 : ℕ} {hPC hNS : ℕ → ℕ∞} (hp : 2 ≤ p) (hk : 1 ≤ k)
    (P : PeriodicProfile hPC (onset k s n0) (period p k s))
    (h4 : IsT4 hPC (onset k s n0)) (hle : ∀ n, hPC n ≤ hNS n) (B : ℕ) :
    ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧ hPC n = (d : ℕ∞) ∧ (d : ℕ∞) ≤ hNS n ∧
      (n : ℚ) / ((p + 2) * k) - s / k ≤ d := by
  obtain ⟨n, d, hn, hd, _, hval, _, hrat⟩ := T4_peaks hp hk P h4 B
  exact ⟨n, d, hn, hd, hval, by rw [← hval]; exact hle n, hrat⟩

end DegreeProfilesReview.Profiles
