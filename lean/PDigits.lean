/-
Claude, 25 Sep 2026.  The lim inf of a profile, and the degree as a function of the last base-p
digits of n, in every prime characteristic.

* LIM INF (`liminf_eq_min`, `liminf_eq_top`).  For any profile satisfying (P): if some finite
  value recurs, the lim inf is the least recurring value `e₀`; the profile is `≥ e₀` from `N(e₀)`
  on and equals `e₀` on a whole residue class modulo `Q(e₀)`.  If no finite value recurs (T2),
  the lim inf is `∞`.  So in T1, T3 and T4 the lim inf is finite and attained periodically.
* DIGIT TABLE (`digit_table`).  There is one table `Φ d c ∈ {0,…,d+1}` (value `d+1` meaning
  "more than d") such that `min(h n, d+1) = Φ d (n mod Q d)` for all `n ≥ N d`, coherent in `d`.
  With `d = β(n)` for the actual profiles: `min(h n, β(n)+1) = Φ (β n) (n mod p^j(n))`, with
  `p^j(n) = Q(β n) ≤ p⌊√(2n)⌋`; so the degree up to the square-root window is read off the
  last `j(n) ≤ 1 + log_p √(2n)` base-p digits of `n`, from a table that does not depend on `n`.
-/
import PShape

set_option autoImplicit false
open Filter

namespace ClaudeCP
open DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles
open ClaudeWitnessTransfer ClaudeC017

/-! ### The lim inf -/

section Liminf
variable {h : ℕ → ℕ∞} {N Q : ℕ → ℕ}

/-- The least recurring value is the eventual minimum, attained on a residue class. -/
theorem eventual_min (P : PeriodicProfile h N Q) (hne : (E h N).Nonempty) :
    ∃ e₀ ∈ E h N, (∀ x ∈ E h N, e₀ ≤ x) ∧ (∀ n, N e₀ ≤ n → (e₀ : ℕ∞) ≤ h n) ∧
      ∃ c, N e₀ ≤ c ∧ h c = (e₀ : ℕ∞) ∧
        ∀ m, c ≤ m → m % Q e₀ = c % Q e₀ → h m = (e₀ : ℕ∞) := by
  classical
  let e₀ := Nat.find (p := fun e => e ∈ E h N) (by obtain ⟨x, hx⟩ := hne; exact ⟨x, hx⟩)
  have he₀ : e₀ ∈ E h N := Nat.find_spec (p := fun e => e ∈ E h N) _
  have hmin : ∀ x ∈ E h N, e₀ ≤ x := fun x hx => Nat.find_min' (p := fun e => e ∈ E h N) _ hx
  refine ⟨e₀, he₀, hmin, ?_, ?_⟩
  · intro n hn
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy, hye⟩ := enat_exists_of_le_coe (le_of_lt hlt)
    have hy' : y < e₀ := by rw [hy] at hlt; exact_mod_cast hlt
    have hyE : y ∈ E h N := ⟨n, le_trans (P.N_mono hy'.le) hn, hy⟩
    exact absurd (hmin y hyE) (by omega)
  · obtain ⟨c, hc, hce, -⟩ := P.recurs he₀
    exact ⟨c, hc, hce, locked_of_window P hc hce⟩

/-- **lim inf = least recurring value** (T1, T3, T4). -/
theorem liminf_eq_min (P : PeriodicProfile h N Q) (hne : (E h N).Nonempty) :
    ∃ e₀ ∈ E h N, (∀ x ∈ E h N, e₀ ≤ x) ∧ liminf h atTop = (e₀ : ℕ∞) := by
  obtain ⟨e₀, he₀, hmin, hge, -⟩ := eventual_min P hne
  refine ⟨e₀, he₀, hmin, ?_⟩
  rw [liminf_eq_iSup_iInf_of_nat]
  apply le_antisymm
  · apply iSup_le
    intro M
    obtain ⟨n, hn, hne'⟩ := (P.mem_E_iff e₀).mp he₀ M
    exact le_trans (iInf₂_le n hn) (le_of_eq hne')
  · exact le_iSup_of_le (N e₀) (le_iInf₂ fun n hn => hge n hn)

/-- **lim inf = ∞ in T2.** -/
theorem liminf_eq_top (P : PeriodicProfile h N Q) (h2 : IsT2 h N) : liminf h atTop = ⊤ := by
  rw [liminf_eq_iSup_iInf_of_nat, ENat.eq_top_iff_forall_ge]
  intro B
  exact le_iSup_of_le (N B) (le_iInf₂ fun n hn => le_of_lt (P.T2_gt h2 hn))

end Liminf

/-! ### The digit table -/

section Table
variable {h : ℕ → ℕ∞} {N Q : ℕ → ℕ}

/-- The table: the truncated degree at the least-residue representative beyond `N d`. -/
noncomputable def table (h : ℕ → ℕ∞) (N Q : ℕ → ℕ) (d c : ℕ) : ℕ∞ :=
  min (h (c % Q d + Q d * N d)) ((d + 1 : ℕ) : ℕ∞)

theorem table_le (d c : ℕ) : table h N Q d c ≤ ((d + 1 : ℕ) : ℕ∞) := min_le_right _ _

theorem table_mod (d c : ℕ) : table h N Q d (c % Q d) = table h N Q d c := by
  unfold table
  rw [Nat.mod_mod]

/-- **The degree, truncated at level `d`, is the table evaluated at `n mod Q d`.** -/
theorem digit_table (P : PeriodicProfile h N Q) {d n : ℕ} (hn : N d ≤ n) :
    min (h n) ((d + 1 : ℕ) : ℕ∞) = table h N Q d (n % Q d) := by
  unfold table
  have hq := P.Q_pos d
  have hrep : N d ≤ n % Q d % Q d + Q d * N d := by
    have : N d ≤ Q d * N d := Nat.le_mul_of_pos_left _ hq
    omega
  have hmod : n % Q d = (n % Q d % Q d + Q d * N d) % Q d := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod, Nat.mod_mod]
  exact P.tau hn hrep hmod

/-- **Coherence**: the tables for different levels are compatible when the periods divide. -/
theorem table_coherent (P : PeriodicProfile h N Q) {d d' : ℕ} (hdd : d ≤ d')
    (hQ : Q d ∣ Q d') (c : ℕ) :
    table h N Q d c = min (table h N Q d' c) ((d + 1 : ℕ) : ℕ∞) := by
  set m := c % Q d' + Q d' * N d' with hm
  have hq' := P.Q_pos d'
  have hmN : N d' ≤ m := by
    have : N d' ≤ Q d' * N d' := Nat.le_mul_of_pos_left _ hq'
    omega
  have h1 := digit_table P (le_trans (P.N_mono hdd) hmN)
  have hmodc : m % Q d = c % Q d := by
    have hm' : m % Q d' = c % Q d' := by rw [hm, Nat.add_mul_mod_self_left, Nat.mod_mod]
    rw [← Nat.mod_mod_of_dvd m hQ, hm', Nat.mod_mod_of_dvd c hQ]
  rw [hmodc, table_mod] at h1
  rw [← h1]
  have hle : ((d + 1 : ℕ) : ℕ∞) ≤ ((d' + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.succ_le_succ hdd
  unfold table
  rw [← hm, min_assoc, min_eq_right hle]

end Table

/-! ### `p`-power periods divide each other -/

section Periods
variable {p : ℕ} [Fact p.Prime] {k s : ℕ}

theorem period_mono {d d' : ℕ} (hdd : d ≤ d') : period p k s d ≤ period p k s d' := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases hd : d = 0
  · subst hd
    unfold period
    rw [if_pos rfl]
    exact period_pos hp k s d'
  · unfold period
    rw [if_neg hd, if_neg (by omega)]
    obtain ⟨a, ha⟩ := leastPowGt_isPow hp (k * d' + s)
    have hgt := leastPowGt_gt hp (k * d' + s)
    rw [ha] at hgt ⊢
    exact leastPowGt_le hp (lt_of_le_of_lt (by have := Nat.mul_le_mul_left k hdd; omega) hgt)

theorem period_dvd {d d' : ℕ} (hdd : d ≤ d') : period p k s d ∣ period p k s d' := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨i, hi⟩ := period_isPowP (p := p) (k := k) (s := s) d
  obtain ⟨j, hj⟩ := period_isPowP (p := p) (k := k) (s := s) d'
  have hle := period_mono (p := p) (k := k) (s := s) hdd
  rw [hi, hj] at hle ⊢
  exact Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right (by omega)).mp hle)

end Periods

/-! ### For the actual profiles -/

section Main
variable {R : Type} [Field R] (p : ℕ) [Fact p.Prime] [CharP R p] (T : Template R)

omit [CharP R p] in
/-- The window modulus `Q(β n)` is a power of `p` at most `p⌊√(2n)⌋`. -/
theorem window_modulus {n : ℕ} (h3 : 3 ≤ n) :
    (∃ j, period p T.k T.s ((Nat.sqrt (2 * n) - T.s - 1) / T.k) = p ^ j) ∧
    period p T.k T.s ((Nat.sqrt (2 * n) - T.s - 1) / T.k) ≤ p * Nat.sqrt (2 * n) := by
  refine ⟨period_isPowP _, ?_⟩
  have hp := (Fact.out : p.Prime).two_le
  have hk := T.hk
  set d := (Nat.sqrt (2 * n) - T.s - 1) / T.k with hd
  have hsq : 2 ≤ Nat.sqrt (2 * n) := by
    rw [Nat.le_sqrt]
    omega
  by_cases hd0 : d = 0
  · rw [hd0]
    unfold period
    rw [if_pos rfl]
    nlinarith
  · have hper := period_le T.s hp hk (Nat.one_le_iff_ne_zero.mpr hd0)
    have hkd : T.k * d ≤ Nat.sqrt (2 * n) - T.s - 1 := by rw [hd]; exact Nat.mul_div_le _ _
    have h1 : 1 ≤ T.k * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hd0)
    have hx : T.k * d + T.s ≤ Nat.sqrt (2 * n) := by omega
    exact le_trans hper (Nat.mul_le_mul_left p hx)

/-- **The degree as a function of the last base-p digits** (both profiles).  For every
`n ≥ max(n₀,3)`, with `β = β(n)` and `p^j = Q(β) ≤ p⌊√(2n)⌋`:
`min(h n, β+1) = Φ β (n mod p^j)`, for one table `Φ` that does not depend on `n` and is coherent
across levels.  In particular `h n = Φ β (n mod p^j)` whenever `h n ≤ β`, and `h n > β` exactly
when the table entry is `β+1`. -/
theorem charP_digit_formula :
    let β := fun n : ℕ => (Nat.sqrt (2 * n) - T.s - 1) / T.k
    let Q := period p T.k T.s
    let N := wOnset T.k T.s T.n0 triW
    (∀ n, T.n0 ≤ n → 3 ≤ n →
      min (T.pcProfile n) ((β n + 1 : ℕ) : ℕ∞) = table T.pcProfile N Q (β n) (n % Q (β n)) ∧
      min (T.nsProfile n) ((β n + 1 : ℕ) : ℕ∞) = table T.nsProfile N Q (β n) (n % Q (β n)) ∧
      (∃ j, Q (β n) = p ^ j) ∧ Q (β n) ≤ p * Nat.sqrt (2 * n)) ∧
    (∀ d d' c, d ≤ d' →
      table T.pcProfile N Q d c = min (table T.pcProfile N Q d' c) ((d + 1 : ℕ) : ℕ∞) ∧
      table T.nsProfile N Q d c = min (table T.nsProfile N Q d' c) ((d + 1 : ℕ) : ℕ∞)) := by
  intro β Q N
  refine ⟨fun n hn0 h3 => ?_, fun d d' c hdd => ?_⟩
  · have hN : N (β n) ≤ n := wOnset_sqrt2_le T.hk hn0 h3
    exact ⟨digit_table (charP_periodic p T).1 hN, digit_table (charP_periodic p T).2 hN,
      window_modulus p T h3⟩
  · exact ⟨table_coherent (charP_periodic p T).1 hdd (period_dvd hdd) c,
      table_coherent (charP_periodic p T).2 hdd (period_dvd hdd) c⟩

/-- **The lim inf in each type** (both profiles): `∞` in T2, and otherwise the least recurring
value `e₀`, which bounds the profile from `N(e₀)` on and is attained on a residue class modulo
`Q(e₀) ≤ p(k e₀ + s + 1)`. -/
theorem charP_liminf (h : ℕ → ℕ∞) (hh : h = T.pcProfile ∨ h = T.nsProfile) :
    (IsT2 h (wOnset T.k T.s T.n0 triW) → liminf h atTop = ⊤) ∧
    (¬ IsT2 h (wOnset T.k T.s T.n0 triW) →
      ∃ e₀ : ℕ, liminf h atTop = (e₀ : ℕ∞) ∧ e₀ ∈ E h (wOnset T.k T.s T.n0 triW) ∧
        (∀ n, wOnset T.k T.s T.n0 triW e₀ ≤ n → (e₀ : ℕ∞) ≤ h n) ∧
        period p T.k T.s e₀ ≤ p * (T.k * e₀ + T.s + 1) ∧
        ∃ c, wOnset T.k T.s T.n0 triW e₀ ≤ c ∧
          ∀ m, c ≤ m → m % period p T.k T.s e₀ = c % period p T.k T.s e₀ →
            h m = (e₀ : ℕ∞)) := by
  have P : PeriodicProfile h (wOnset T.k T.s T.n0 triW) (period p T.k T.s) := by
    rcases hh with rfl | rfl
    · exact (charP_periodic p T).1
    · exact (charP_periodic p T).2
  refine ⟨liminf_eq_top P, fun hn2 => ?_⟩
  have hne : (E h (wOnset T.k T.s T.n0 triW)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hn2
  obtain ⟨e₀, he₀, hmin, hge, c, hc, -, hlock⟩ := eventual_min P hne
  obtain ⟨e₁, he₁, hmin₁, hlim⟩ := liminf_eq_min P hne
  have he : e₁ = e₀ := le_antisymm (hmin₁ e₀ he₀) (hmin e₁ he₁)
  rw [he] at hlim
  exact ⟨e₀, hlim, he₀, hge, period_le_succ T.hk e₀, c, hc, hlock⟩

end Main
end ClaudeCP
