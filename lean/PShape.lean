/-
Claude, 25 Sep 2026.  The shape of a profile beyond the classification, in every prime
characteristic, with emphasis on T4.

Write `β(n) = ⌊(⌊√(2n)⌋ - s - 1)/k⌋` and `Q(v)` for the least power of `p` above `kv+s`
(`Q(0) = 1`).  For every template over a field of characteristic `p`, and for its PC and its NS
profile `h`:

* LOCKED OR PEAK (`charP_locked_or_peak`).  At every size `n ≥ max(n₀,3)`, either `h(n) > β(n)`,
  or `v = h(n) ≤ β(n)` and the value is locked in: `h(m) = v` for every `m ≥ n` with
  `m ≡ n (mod Q(v))`, where `Q(v)` is a power of `p` and `Q(v) ≤ p(kv+s+1)`.
* PEAKS IN EVERY WINDOW (`charP_peaks_in_windows`).  Unless `h` is eventually bounded (T1), every
  window `[X, X + p⌊√(2X)⌋)` with `X ≥ max(n₀,3)` contains a size `n` with `h(n) > β(X)`.
* In T4 both kinds recur forever: the locked values are unbounded, each occupying a residue
  class of modulus at most `p(kv+s+1)` (`charP_T4_shape`).
-/
import PFinal

set_option autoImplicit false

namespace ClaudeCP
open DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles
open ClaudeWitnessTransfer ClaudeC017

/-! ### Two facts about any profile satisfying (P) -/

section Generic
variable {h : ℕ → ℕ∞} {N Q : ℕ → ℕ}

/-- A value inside its own window is locked on its residue class. -/
theorem locked_of_window (P : PeriodicProfile h N Q) {n v : ℕ} (hn : N v ≤ n)
    (hv : h n = (v : ℕ∞)) : ∀ m, n ≤ m → m % Q v = n % Q v → h m = (v : ℕ∞) :=
  fun _ hm hmod => (P.exact_level (le_refl v) (le_trans hn hm) hn hmod).mpr hv

/-- Unless the profile is eventually bounded, every window of length `Q d` beyond `N d`
contains a size where the degree exceeds `d`. -/
theorem hard_in_window (P : PeriodicProfile h N Q) (hnb : ¬ IsT1 h) {d X : ℕ} (hX : N d ≤ X) :
    ∃ n, X ≤ n ∧ n < X + Q d ∧ (d : ℕ∞) < h n := by
  by_contra hno
  push_neg at hno
  apply hnb
  refine ⟨d, X, fun m hm => ?_⟩
  have hq := P.Q_pos d
  set n := X + (m - X) % Q d with hn
  have hn1 : X ≤ n := Nat.le_add_right _ _
  have hn2 : n < X + Q d := Nat.add_lt_add_left (Nat.mod_lt _ hq) _
  have hsplit : m = n + Q d * ((m - X) / Q d) := by
    have := Nat.mod_add_div (m - X) (Q d)
    omega
  have hmod : n % Q d = m % Q d := by
    conv_rhs => rw [hsplit]
    rw [Nat.add_mul_mod_self_left]
  exact (P.periodic d d le_rfl n m (le_trans hX hn1) (le_trans hX hm) hmod).mp (hno n hn1 hn2)

/-- Beyond `N d`, the sizes where the degree exceeds `d` form a union of residue classes
modulo `Q d`. -/
theorem hard_periodic (P : PeriodicProfile h N Q) {d n m : ℕ} (hn : N d ≤ n) (hm : N d ≤ m)
    (hc : n % Q d = m % Q d) : ((d : ℕ∞) < h n ↔ (d : ℕ∞) < h m) := by
  rw [← not_le, ← not_le, P.periodic d d le_rfl n m hn hm hc]

end Generic

/-! ### With the triangular onset and `p`-power periods -/

section Shape
variable {p : ℕ} [Fact p.Prime] {k s n0 : ℕ} {h : ℕ → ℕ∞}

theorem period_le_succ (hk : 1 ≤ k) (v : ℕ) : period p k s v ≤ p * (k * v + s + 1) := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases hv : v = 0
  · subst hv
    unfold period
    rw [if_pos rfl]
    nlinarith
  · have := period_le s hp hk (by omega : 1 ≤ v)
    nlinarith

/-- **Locked or peak.** -/
theorem locked_or_peak (hk : 1 ≤ k)
    (P : PeriodicProfile h (wOnset k s n0 triW) (period p k s)) {n : ℕ} (hn0 : n0 ≤ n)
    (h3 : 3 ≤ n) :
    (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n ∨
      ∃ v : ℕ, h n = v ∧ v ≤ (Nat.sqrt (2 * n) - s - 1) / k ∧
        (∃ j, period p k s v = p ^ j) ∧ period p k s v ≤ p * (k * v + s + 1) ∧
        ∀ m, n ≤ m → m % period p k s v = n % period p k s v → h m = (v : ℕ∞) := by
  by_cases hlt : (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n
  · exact Or.inl hlt
  · right
    rw [not_lt] at hlt
    obtain ⟨v, hv, hvβ⟩ := enat_exists_of_le_coe hlt
    have hN : wOnset k s n0 triW v ≤ n :=
      le_trans (P.N_mono hvβ) (wOnset_sqrt2_le hk hn0 h3)
    exact ⟨v, hv, hvβ, period_isPowP v, period_le_succ hk v, locked_of_window P hN hv⟩

/-- **Peaks in every window of length `p⌊√(2X)⌋`**, unless the profile is eventually bounded. -/
theorem peaks_in_windows (hk : 1 ≤ k)
    (P : PeriodicProfile h (wOnset k s n0 triW) (period p k s)) (hnb : ¬ IsT1 h) {X : ℕ}
    (hX0 : n0 ≤ X) (h3 : 3 ≤ X) :
    ∃ n, X ≤ n ∧ n < X + p * Nat.sqrt (2 * X) ∧
      (((Nat.sqrt (2 * X) - s - 1) / k : ℕ) : ℕ∞) < h n := by
  have hQ : ∀ d, d = (Nat.sqrt (2 * X) - s - 1) / k → period p k s d ≤ p * Nat.sqrt (2 * X) := by
    intro d hd
    have hp := (Fact.out : p.Prime).two_le
    have hsq : 2 ≤ Nat.sqrt (2 * X) := by
      rw [Nat.le_sqrt]
      omega
    by_cases hd0 : d = 0
    · rw [hd0]
      unfold period
      rw [if_pos rfl]
      nlinarith
    · have hper := period_le s hp hk (Nat.one_le_iff_ne_zero.mpr hd0)
      have hkd : k * d ≤ Nat.sqrt (2 * X) - s - 1 := by rw [hd]; exact Nat.mul_div_le _ _
      have h1 : 1 ≤ k * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hd0)
      have hx : k * d + s ≤ Nat.sqrt (2 * X) := by omega
      exact le_trans hper (Nat.mul_le_mul_left p hx)
  obtain ⟨n, hn1, hn2, hn3⟩ := hard_in_window P hnb (wOnset_sqrt2_le hk hX0 h3)
  exact ⟨n, hn1, lt_of_lt_of_le hn2 (Nat.add_le_add_left (hQ _ rfl) _), hn3⟩

/-- **The shape of a T4 profile.** -/
theorem T4_shape (hk : 1 ≤ k) (P : PeriodicProfile h (wOnset k s n0 triW) (period p k s))
    (h4 : IsT4 h (wOnset k s n0 triW)) :
    -- every size beyond max(n₀,3) is a peak or carries a locked value
    (∀ n, n0 ≤ n → 3 ≤ n →
      (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n ∨
      ∃ v : ℕ, h n = v ∧ v ≤ (Nat.sqrt (2 * n) - s - 1) / k ∧
        (∃ j, period p k s v = p ^ j) ∧ period p k s v ≤ p * (k * v + s + 1) ∧
        ∀ m, n ≤ m → m % period p k s v = n % period p k s v → h m = (v : ℕ∞)) ∧
    -- peaks occur in every window of length p⌊√(2X)⌋
    (∀ X, n0 ≤ X → 3 ≤ X → ∃ n, X ≤ n ∧ n < X + p * Nat.sqrt (2 * X) ∧
      (((Nat.sqrt (2 * X) - s - 1) / k : ℕ) : ℕ∞) < h n) ∧
    -- locked values are unbounded, each on a residue class of modulus ≤ p(kv+s+1)
    (∀ B : ℕ, ∃ v, B < v ∧ ∃ c, wOnset k s n0 triW v ≤ c ∧ h c = (v : ℕ∞) ∧
      period p k s v ≤ p * (k * v + s + 1) ∧
      ∀ m, c ≤ m → m % period p k s v = c % period p k s v → h m = (v : ℕ∞)) := by
  have hnb : ¬ IsT1 h := by
    rcases P.exactly_one with h' | h' | h' | h'
    · exact absurd h4 h'.2.2.2
    · exact h'.1
    · exact h'.1
    · exact h'.1
  refine ⟨fun n hn0 h3 => locked_or_peak hk P hn0 h3,
    fun X hX0 h3 => peaks_in_windows hk P hnb hX0 h3, fun B => ?_⟩
  obtain ⟨v, hvE, hBv⟩ := h4.exists_gt B
  obtain ⟨c, hc, hcv, -⟩ := P.recurs hvE
  exact ⟨v, hBv, c, hc, hcv, period_le_succ hk v, locked_of_window P hc hcv⟩

end Shape

/-! ### For the actual profiles -/

section Main
variable {R : Type} [Field R] (p : ℕ) [Fact p.Prime] [CharP R p] (T : Template R)

theorem charP_locked_or_peak {n : ℕ} (hn0 : T.n0 ≤ n) (h3 : 3 ≤ n) :
    ((((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.pcProfile n ∨
      ∃ v : ℕ, T.pcProfile n = v ∧ v ≤ (Nat.sqrt (2 * n) - T.s - 1) / T.k ∧
        (∃ j, period p T.k T.s v = p ^ j) ∧ period p T.k T.s v ≤ p * (T.k * v + T.s + 1) ∧
        ∀ m, n ≤ m → m % period p T.k T.s v = n % period p T.k T.s v →
          T.pcProfile m = (v : ℕ∞)) ∧
    ((((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.nsProfile n ∨
      ∃ v : ℕ, T.nsProfile n = v ∧ v ≤ (Nat.sqrt (2 * n) - T.s - 1) / T.k ∧
        (∃ j, period p T.k T.s v = p ^ j) ∧ period p T.k T.s v ≤ p * (T.k * v + T.s + 1) ∧
        ∀ m, n ≤ m → m % period p T.k T.s v = n % period p T.k T.s v →
          T.nsProfile m = (v : ℕ∞)) :=
  ⟨locked_or_peak T.hk (charP_periodic p T).1 hn0 h3,
    locked_or_peak T.hk (charP_periodic p T).2 hn0 h3⟩

/-- The sizes where the degree exceeds `d` are, beyond `N(d)`, a union of residue classes
modulo the `p`-power `Q(d)`. -/
theorem charP_hard_periodic {d n m : ℕ} (hn : wOnset T.k T.s T.n0 triW d ≤ n)
    (hm : wOnset T.k T.s T.n0 triW d ≤ m) (hc : n % period p T.k T.s d = m % period p T.k T.s d) :
    ((d : ℕ∞) < T.pcProfile n ↔ (d : ℕ∞) < T.pcProfile m) ∧
    ((d : ℕ∞) < T.nsProfile n ↔ (d : ℕ∞) < T.nsProfile m) :=
  ⟨hard_periodic (charP_periodic p T).1 hn hm hc, hard_periodic (charP_periodic p T).2 hn hm hc⟩

theorem charP_peaks_in_windows {X : ℕ} (hX0 : T.n0 ≤ X) (h3 : 3 ≤ X) :
    (¬ IsT1 T.pcProfile → ∃ n, X ≤ n ∧ n < X + p * Nat.sqrt (2 * X) ∧
      (((Nat.sqrt (2 * X) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.pcProfile n) ∧
    (¬ IsT1 T.nsProfile → ∃ n, X ≤ n ∧ n < X + p * Nat.sqrt (2 * X) ∧
      (((Nat.sqrt (2 * X) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.nsProfile n) :=
  ⟨fun hnb => peaks_in_windows T.hk (charP_periodic p T).1 hnb hX0 h3,
    fun hnb => peaks_in_windows T.hk (charP_periodic p T).2 hnb hX0 h3⟩

/-- **T4 for the PC profile, in full.** -/
theorem charP_T4_shape_pc (h4 : IsT4 T.pcProfile (wOnset T.k T.s T.n0 triW)) :
    (∀ n, T.n0 ≤ n → 3 ≤ n →
      (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.pcProfile n ∨
      ∃ v : ℕ, T.pcProfile n = v ∧ v ≤ (Nat.sqrt (2 * n) - T.s - 1) / T.k ∧
        (∃ j, period p T.k T.s v = p ^ j) ∧ period p T.k T.s v ≤ p * (T.k * v + T.s + 1) ∧
        ∀ m, n ≤ m → m % period p T.k T.s v = n % period p T.k T.s v →
          T.pcProfile m = (v : ℕ∞)) ∧
    (∀ X, T.n0 ≤ X → 3 ≤ X → ∃ n, X ≤ n ∧ n < X + p * Nat.sqrt (2 * X) ∧
      (((Nat.sqrt (2 * X) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.pcProfile n) ∧
    (∀ B : ℕ, ∃ v, B < v ∧ ∃ c, wOnset T.k T.s T.n0 triW v ≤ c ∧ T.pcProfile c = (v : ℕ∞) ∧
      period p T.k T.s v ≤ p * (T.k * v + T.s + 1) ∧
      ∀ m, c ≤ m → m % period p T.k T.s v = c % period p T.k T.s v → T.pcProfile m = (v : ℕ∞)) :=
  T4_shape T.hk (charP_periodic p T).1 h4

/-- **T4 for the NS profile, in full.** -/
theorem charP_T4_shape_ns (h4 : IsT4 T.nsProfile (wOnset T.k T.s T.n0 triW)) :
    (∀ n, T.n0 ≤ n → 3 ≤ n →
      (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.nsProfile n ∨
      ∃ v : ℕ, T.nsProfile n = v ∧ v ≤ (Nat.sqrt (2 * n) - T.s - 1) / T.k ∧
        (∃ j, period p T.k T.s v = p ^ j) ∧ period p T.k T.s v ≤ p * (T.k * v + T.s + 1) ∧
        ∀ m, n ≤ m → m % period p T.k T.s v = n % period p T.k T.s v →
          T.nsProfile m = (v : ℕ∞)) ∧
    (∀ X, T.n0 ≤ X → 3 ≤ X → ∃ n, X ≤ n ∧ n < X + p * Nat.sqrt (2 * X) ∧
      (((Nat.sqrt (2 * X) - T.s - 1) / T.k : ℕ) : ℕ∞) < T.nsProfile n) ∧
    (∀ B : ℕ, ∃ v, B < v ∧ ∃ c, wOnset T.k T.s T.n0 triW v ≤ c ∧ T.nsProfile c = (v : ℕ∞) ∧
      period p T.k T.s v ≤ p * (T.k * v + T.s + 1) ∧
      ∀ m, c ≤ m → m % period p T.k T.s v = c % period p T.k T.s v → T.nsProfile m = (v : ℕ∞)) :=
  T4_shape T.hk (charP_periodic p T).2 h4

end Main
end ClaudeCP
