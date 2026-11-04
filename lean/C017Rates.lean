/-
Claude, 25 Sep 2026.  Formalisation of Cycle 017, part F: the square-root rates in all four
cases.

With the triangular onset `N(d) = max(n₀, 2r+1, r(r+1)/2)`, `r = kd+s`, proved in `C017Final`,
Stage 5's structure theorems for the four types give explicit `√(2n)` statements:

* T2: `h(n) > ⌊(⌊√(2n)⌋ - s - 1)/k⌋` for every `n ≥ max(n₀, 3)`;
* T3: a nonempty proper set of residue classes modulo a power of two carries eventually
  constant finite values; on every other class the T2 bound holds;
* T4: arbitrarily large finite `d` recur on whole residue classes, each with a representative
  `n_d < N(d) + Q(d)` satisfying `⌊√(2 n_d)⌋ < kd + s + 3`, i.e. `d > (⌊√(2 n_d)⌋ - s - 3)/k`.
-/
import C017Final

set_option autoImplicit false

namespace ClaudeC017
open DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles
open ClaudeWitnessTransfer

/-- The triangular witness budget of Cycle 017. -/
def triW (r : ℕ) : ℕ := r * (r + 1) / 2

/-! ### Arithmetic of the triangular onset -/

section Window
variable {k s n0 : ℕ}

/-- The square-root window: for `n ≥ max(n₀, 3)` the onset at `d = (⌊√(2n)⌋ - s - 1)/k` is at
most `n`. -/
theorem wOnset_sqrt2_le (hk : 1 ≤ k) {n : ℕ} (hn : n0 ≤ n) (h3 : 3 ≤ n) :
    wOnset k s n0 triW ((Nat.sqrt (2 * n) - s - 1) / k) ≤ n := by
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.sqrt (2 * n) := ⟨_, rfl⟩
  rw [← hm]
  set d := (m - s - 1) / k with hd
  have hsq : m * m ≤ 2 * n := by rw [hm]; exact Nat.sqrt_le (2 * n)
  unfold wOnset
  split
  · exact hn
  · rename_i hd0
    have hkd : k * d ≤ m - s - 1 := Nat.mul_div_le _ _
    have h1 : 1 ≤ k * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hd0)
    have hx : k * d + s + 1 ≤ m := by omega
    have h2m : 2 * m ≤ n + 1 := by
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · rcases (by omega : m ≤ 2 ∨ m = 3) with hm2 | hm3
        · omega
        · rw [hm3] at hsq; omega
      · nlinarith
    set x := k * d + s with hxdef
    have hx2 : (x + 1) * (x + 1) ≤ 2 * n := le_trans (Nat.mul_le_mul hx hx) hsq
    refine max_le ?_ ?_
    · unfold onset
      rw [if_neg hd0]
      exact max_le hn (by omega)
    · change x * (x + 1) / 2 ≤ n
      apply Nat.div_le_of_le_mul
      nlinarith

/-- `r ↦ r(r+1)/2` is monotone. -/
theorem triW_mono : Monotone triW := by
  intro x y hxy
  exact Nat.div_le_div_right (Nat.mul_le_mul hxy (by omega))

/-- For large levels the triangular term dominates the onset. -/
theorem wOnset_eq_triW (hk : 1 ≤ k) {d : ℕ} (hd : n0 + 4 < d) :
    wOnset k s n0 triW d = triW (k * d + s) := by
  have hd0 : d ≠ 0 := by omega
  have hr : d ≤ k * d := Nat.le_mul_of_pos_left d hk
  set r := k * d + s with hrdef
  have hr4 : n0 + 4 < r := by omega
  have hT : 2 * r + 1 ≤ triW r := by
    unfold triW
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  unfold wOnset
  rw [if_neg hd0]
  apply max_eq_right
  unfold onset
  rw [if_neg hd0]
  exact max_le (le_trans (by omega) hT) hT

/-- The period at a positive level is a power of two, at most `2(kd+s)`. -/
theorem period_isPow (d : ℕ) : ∃ j, period 2 k s d = 2 ^ j := by
  unfold period
  split
  · exact ⟨0, rfl⟩
  · exact leastPowGt_isPow (le_refl 2) _

end Window

/-! ### The four cases with explicit rates -/

section Rates
variable {k s n0 : ℕ} {h : ℕ → ℕ∞}

/-- **T2.** No recurring level: `h(n) > ⌊(⌊√(2n)⌋ - s - 1)/k⌋` for every `n ≥ max(n₀, 3)`. -/
theorem T2_sqrt (hk : 1 ≤ k) {Q : ℕ → ℕ} (P : PeriodicProfile h (wOnset k s n0 triW) Q)
    (h2 : IsT2 h (wOnset k s n0 triW)) {n : ℕ} (hn : n0 ≤ n) (h3 : 3 ≤ n) :
    (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n :=
  P.T2_gt h2 (wOnset_sqrt2_le hk hn h3)

/-- **T3.** With `D = max E` and `q = Q(D)` a power of two, a nonempty proper set `U` of
residues mod `q` carries eventually constant values `≤ D`; on every other residue class the
T2 bound holds beyond `N(D)`. -/
theorem T3_sqrt (hk : 1 ≤ k) (P : PeriodicProfile h (wOnset k s n0 triW) (period 2 k s))
    (h3 : IsT3 h (wOnset k s n0 triW)) :
    ∃ D, D ∈ E h (wOnset k s n0 triW) ∧ (∀ d ∈ E h (wOnset k s n0 triW), d ≤ D) ∧
      (∃ j, period 2 k s D = 2 ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period 2 k s D) ∧ U.Nonempty ∧
        (∃ c, c < period 2 k s D ∧ c ∉ U) ∧
        (∀ n, wOnset k s n0 triW D ≤ n → n % period 2 k s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, wOnset k s n0 triW D ≤ m →
            m % period 2 k s D = n % period 2 k s D → h m = (v : ℕ∞)) ∧
        (∀ n, wOnset k s n0 triW D ≤ n → 3 ≤ n → n % period 2 k s D ∉ U →
          (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n) := by
  obtain ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, hUeasy, hUhard⟩ := P.T3_structure h3
  refine ⟨D, hDE, hDmax, period_isPow D, U, hUlt, hUne, hUprop, hUeasy, ?_⟩
  intro n hn h3n hnU
  have hn0 : n0 ≤ n := by
    have h0 : wOnset k s n0 triW 0 = n0 := by unfold wOnset; rw [if_pos rfl]
    have := P.N_mono (Nat.zero_le D)
    rw [h0] at this
    exact le_trans this hn
  exact hUhard n hn hnU _ (wOnset_sqrt2_le hk hn0 h3n)

/-- **T4.** For every `B` there is a recurring level `d > B`, holding on a whole residue
class beyond its onset, with a representative `n_d < N(d) + Q(d)` and `⌊√(2 n_d)⌋ < kd+s+3`. -/
theorem T4_sqrt (hk : 1 ≤ k) (P : PeriodicProfile h (wOnset k s n0 triW) (period 2 k s))
    (h4 : IsT4 h (wOnset k s n0 triW)) (B : ℕ) :
    ∃ d, B < d ∧ ∃ c, wOnset k s n0 triW d ≤ c ∧ c < wOnset k s n0 triW d + period 2 k s d ∧
      (∀ m, wOnset k s n0 triW d ≤ m → m % period 2 k s d = c % period 2 k s d →
        h m = (d : ℕ∞)) ∧
      Nat.sqrt (2 * c) < k * d + s + 3 ∧ (Nat.sqrt (2 * c) - s - 3) / k < d := by
  obtain ⟨d, hBd, c0, hc0, hrec⟩ := P.T4_structure h4 (max B (n0 + 4))
  set N := wOnset k s n0 triW d with hN
  set q := period 2 k s d with hq
  have hq0 : 0 < q := P.Q_pos d
  set c := N + (c0 - N) % q with hc
  have hsplit : c0 = c + q * ((c0 - N) / q) := by
    have := Nat.mod_add_div (c0 - N) q
    omega
  have hcmod : c % q = c0 % q := by
    rw [hsplit, Nat.add_mul_mod_self_left]
  refine ⟨d, lt_of_le_of_lt (le_max_left _ _) hBd, c, Nat.le_add_right _ _,
    Nat.add_lt_add_left (Nat.mod_lt _ hq0) _, fun m hm hmc => (hrec m hm (hmc.trans hcmod)).1, ?_⟩
  -- the square-root bound for the representative
  have hd4 : n0 + 4 < d := lt_of_le_of_lt (le_max_right _ _) hBd
  have hkd : d ≤ k * d := Nat.le_mul_of_pos_left d hk
  set r := k * d + s with hr
  have hNr : N = triW r := wOnset_eq_triW hk hd4
  have hqr : q ≤ 2 * r := period_le s (le_refl 2) hk (by omega)
  have hclt : c < triW r + 2 * r := by
    have : c < N + q := Nat.add_lt_add_left (Nat.mod_lt _ hq0) _
    omega
  have htri : 2 * triW r ≤ r * (r + 1) := by unfold triW; exact Nat.mul_div_le _ _
  have h2c : 2 * c < (r + 3) * (r + 3) := by nlinarith
  have hsqrt : Nat.sqrt (2 * c) < r + 3 := Nat.sqrt_lt.mpr h2c
  refine ⟨hsqrt, ?_⟩
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have : 1 ≤ k * d := by nlinarith
  rw [mul_comm d k]
  omega

/-- **The four types with square-root rates**, for any profile satisfying (P) with the
triangular onset and power-of-two periods. -/
theorem four_types_sqrt (hk : 1 ≤ k)
    (P : PeriodicProfile h (wOnset k s n0 triW) (period 2 k s)) :
    let N := wOnset k s n0 triW
    ((IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ IsT4 h N)) ∧
    (IsT1 h → ∃ B M : ℕ, ∀ n, M ≤ n → h n ≤ (B : ℕ∞)) ∧
    (IsT2 h N → ∀ n, n0 ≤ n → 3 ≤ n → (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n) ∧
    (IsT3 h N →
      ∃ D, D ∈ E h N ∧ (∀ d ∈ E h N, d ≤ D) ∧ (∃ j, period 2 k s D = 2 ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period 2 k s D) ∧ U.Nonempty ∧
        (∃ c, c < period 2 k s D ∧ c ∉ U) ∧
        (∀ n, N D ≤ n → n % period 2 k s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, N D ≤ m →
            m % period 2 k s D = n % period 2 k s D → h m = (v : ℕ∞)) ∧
        (∀ n, N D ≤ n → 3 ≤ n → n % period 2 k s D ∉ U →
          (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n)) ∧
    (IsT4 h N → ∀ B : ℕ,
      ∃ d, B < d ∧ ∃ c, N d ≤ c ∧ c < N d + period 2 k s d ∧
        (∀ m, N d ≤ m → m % period 2 k s d = c % period 2 k s d → h m = (d : ℕ∞)) ∧
        Nat.sqrt (2 * c) < k * d + s + 3 ∧ (Nat.sqrt (2 * c) - s - 3) / k < d) :=
  ⟨P.exactly_one, fun h1 => h1, fun h2 _ hn h3 => T2_sqrt hk P h2 hn h3, T3_sqrt hk P,
    T4_sqrt hk P⟩

end Rates

/-! ### The characteristic-two theorem -/

section CharTwo
variable {R : Type} [Field R] [CharP R 2] (T : Template R)

theorem triW_eq : (fun r : ℕ => r * (r + 1) / 2) = triW := rfl

/-- **Theorem B (characteristic two), PC profile**, with all four square-root statements. -/
theorem charTwo_pc_main :
    let N := wOnset T.k T.s T.n0 triW
    let h := T.pcProfile
    ((IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ IsT4 h N)) ∧
    (IsT1 h → ∃ B M : ℕ, ∀ n, M ≤ n → h n ≤ (B : ℕ∞)) ∧
    (IsT2 h N → ∀ n, T.n0 ≤ n → 3 ≤ n →
      (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n) ∧
    (IsT3 h N →
      ∃ D, D ∈ E h N ∧ (∀ d ∈ E h N, d ≤ D) ∧ (∃ j, period 2 T.k T.s D = 2 ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period 2 T.k T.s D) ∧ U.Nonempty ∧
        (∃ c, c < period 2 T.k T.s D ∧ c ∉ U) ∧
        (∀ n, N D ≤ n → n % period 2 T.k T.s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, N D ≤ m →
            m % period 2 T.k T.s D = n % period 2 T.k T.s D → h m = (v : ℕ∞)) ∧
        (∀ n, N D ≤ n → 3 ≤ n → n % period 2 T.k T.s D ∉ U →
          (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n)) ∧
    (IsT4 h N → ∀ B : ℕ,
      ∃ d, B < d ∧ ∃ c, N d ≤ c ∧ c < N d + period 2 T.k T.s d ∧
        (∀ m, N d ≤ m → m % period 2 T.k T.s d = c % period 2 T.k T.s d → h m = (d : ℕ∞)) ∧
        Nat.sqrt (2 * c) < T.k * d + T.s + 3 ∧ (Nat.sqrt (2 * c) - T.s - 3) / T.k < d) :=
  four_types_sqrt T.hk (charTwo_periodic T).1

/-- **Theorem B (characteristic two), NS profile**, with all four square-root statements. -/
theorem charTwo_ns_main :
    let N := wOnset T.k T.s T.n0 triW
    let h := T.nsProfile
    ((IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ IsT4 h N)) ∧
    (IsT1 h → ∃ B M : ℕ, ∀ n, M ≤ n → h n ≤ (B : ℕ∞)) ∧
    (IsT2 h N → ∀ n, T.n0 ≤ n → 3 ≤ n →
      (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n) ∧
    (IsT3 h N →
      ∃ D, D ∈ E h N ∧ (∀ d ∈ E h N, d ≤ D) ∧ (∃ j, period 2 T.k T.s D = 2 ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period 2 T.k T.s D) ∧ U.Nonempty ∧
        (∃ c, c < period 2 T.k T.s D ∧ c ∉ U) ∧
        (∀ n, N D ≤ n → n % period 2 T.k T.s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, N D ≤ m →
            m % period 2 T.k T.s D = n % period 2 T.k T.s D → h m = (v : ℕ∞)) ∧
        (∀ n, N D ≤ n → 3 ≤ n → n % period 2 T.k T.s D ∉ U →
          (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n)) ∧
    (IsT4 h N → ∀ B : ℕ,
      ∃ d, B < d ∧ ∃ c, N d ≤ c ∧ c < N d + period 2 T.k T.s d ∧
        (∀ m, N d ≤ m → m % period 2 T.k T.s d = c % period 2 T.k T.s d → h m = (d : ℕ∞)) ∧
        Nat.sqrt (2 * c) < T.k * d + T.s + 3 ∧ (Nat.sqrt (2 * c) - T.s - 3) / T.k < d) :=
  four_types_sqrt T.hk (charTwo_periodic T).2

/-- The recurring set does not depend on the onset: it is the set of finite values taken
infinitely often.  So T1–T4 are intrinsic properties of the profile. -/
theorem charTwo_E_intrinsic :
    E T.pcProfile (wOnset T.k T.s T.n0 triW) =
        {d : ℕ | ∀ M, ∃ n, M ≤ n ∧ T.pcProfile n = (d : ℕ∞)} ∧
      E T.nsProfile (wOnset T.k T.s T.n0 triW) =
        {d : ℕ | ∀ M, ∃ n, M ≤ n ∧ T.nsProfile n = (d : ℕ∞)} :=
  ⟨Set.ext fun d => (charTwo_periodic T).1.mem_E_iff d,
    Set.ext fun d => (charTwo_periodic T).2.mem_E_iff d⟩

end CharTwo
end ClaudeC017
