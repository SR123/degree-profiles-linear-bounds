/-
Prompt 06, part 1: degree profiles, hypothesis (P), recurring levels, and the
four-way classification (manuscript `thm:four`).

Everything here is elementary order/arithmetic.  The *only* mathematical hypothesis
is the explicit structure `PeriodicProfile` (the manuscript's hypothesis (P) in
threshold form); nothing about polynomials is proved or assumed in this file.

A profile is `h : ℕ → ℕ∞`, `⊤` being the degree of a satisfiable instance.  Rank zero
never enters: every statement is relative to sizes `n ≥ N d ≥ d + 1 ≥ 1`.
Congruence `n ≡ m (mod q)` is written `n % q = m % q` (this is `Nat.ModEq` unfolded).
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith

namespace DegreeProfilesReview.Profiles

/-! ### Extended-natural helpers -/

theorem enat_eq_coe_iff (x : ℕ∞) (t : ℕ) :
    x = (t : ℕ∞) ↔ x ≤ (t : ℕ∞) ∧ ∀ u : ℕ, u < t → ¬ x ≤ (u : ℕ∞) := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe a =>
    simp only [Nat.cast_inj, Nat.cast_le]
    constructor
    · rintro rfl
      exact ⟨le_refl _, fun u hu h => by omega⟩
    · rintro ⟨h1, h2⟩
      by_contra hne
      exact h2 a (by omega) (le_refl _)

theorem enat_exists_of_le_coe {x : ℕ∞} {B : ℕ} (h : x ≤ (B : ℕ∞)) :
    ∃ a : ℕ, x = (a : ℕ∞) ∧ a ≤ B := by
  induction x using ENat.recTopCoe with
  | top => simp at h
  | coe a => exact ⟨a, rfl, by simpa using h⟩

/-- The manuscript's truncation `τ_d`, as `min · (d+1)`: agreement of all thresholds
`t ≤ d` is the same as `τ_d (x) = τ_d (y)`. -/
theorem enat_min_coe (a b : ℕ) : min (a : ℕ∞) (b : ℕ∞) = ((min a b : ℕ) : ℕ∞) :=
  ((Nat.mono_cast (α := ℕ∞)).map_min).symm

theorem thresholds_iff_tau (x y : ℕ∞) (d : ℕ) :
    (∀ t : ℕ, t ≤ d → (x ≤ (t : ℕ∞) ↔ y ≤ (t : ℕ∞))) ↔
      min x ((d + 1 : ℕ) : ℕ∞) = min y ((d + 1 : ℕ) : ℕ∞) := by
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => simp
    | coe b =>
      rw [min_eq_right le_top, enat_min_coe, Nat.cast_inj]
      simp only [top_le_iff, ENat.coe_ne_top, Nat.cast_le, false_iff, not_le]
      constructor
      · intro h
        have := h d (le_refl _)
        omega
      · intro h t ht
        omega
  | coe a =>
    induction y using ENat.recTopCoe with
    | top =>
      rw [min_eq_right (le_top : ((d + 1 : ℕ) : ℕ∞) ≤ ⊤), enat_min_coe, Nat.cast_inj]
      simp only [top_le_iff, ENat.coe_ne_top, Nat.cast_le, iff_false, not_le]
      constructor
      · intro h
        have := h d (le_refl _)
        omega
      · intro h t ht
        omega
    | coe b =>
      rw [enat_min_coe, enat_min_coe, Nat.cast_inj]
      simp only [Nat.cast_le]
      constructor
      · intro h
        by_cases ha : a ≤ d
        · have h1 := (h a ha).mp (le_refl _)
          by_cases hb : b ≤ d
          · have h2 := (h b hb).mpr (le_refl _)
            omega
          · omega
        · by_cases hb : b ≤ d
          · have h2 := (h b hb).mpr (le_refl _)
            omega
          · omega
      · intro h t ht
        omega

/-! ### Hypothesis (P) -/

/-- The manuscript's hypothesis (P), stated through threshold predicates.
`N` is the common onset, `Q d` the period at level `d` (a `p`-power in the application;
the classification itself does not use that). -/
structure PeriodicProfile (h : ℕ → ℕ∞) (N Q : ℕ → ℕ) : Prop where
  N_mono : Monotone N
  N_ge : ∀ d, d + 1 ≤ N d
  Q_pos : ∀ d, 0 < Q d
  periodic : ∀ d t, t ≤ d → ∀ n m, N d ≤ n → N d ≤ m → n % Q d = m % Q d →
    (h n ≤ (t : ℕ∞) ↔ h m ≤ (t : ℕ∞))

variable {h : ℕ → ℕ∞} {N Q : ℕ → ℕ}

/-- (P) in the manuscript's `τ_d` form. -/
theorem PeriodicProfile.tau (P : PeriodicProfile h N Q) {d n m : ℕ}
    (hn : N d ≤ n) (hm : N d ≤ m) (hc : n % Q d = m % Q d) :
    min (h n) ((d + 1 : ℕ) : ℕ∞) = min (h m) ((d + 1 : ℕ) : ℕ∞) :=
  (thresholds_iff_tau _ _ d).mp fun t ht => P.periodic d t ht n m hn hm hc

/-- Prompt 06, target 1: every exact level `t ≤ d` is periodic beyond `N d`.
This uses *all* thresholds up to `t`, not a single upper-threshold predicate. -/
theorem PeriodicProfile.exact_level (P : PeriodicProfile h N Q) {d t n m : ℕ} (ht : t ≤ d)
    (hn : N d ≤ n) (hm : N d ≤ m) (hc : n % Q d = m % Q d) :
    h n = (t : ℕ∞) ↔ h m = (t : ℕ∞) := by
  rw [enat_eq_coe_iff, enat_eq_coe_iff, P.periodic d t ht n m hn hm hc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => by
      rw [← P.periodic d u (by omega) n m hn hm hc]; exact h2 u hu⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u hu => by
      rw [P.periodic d u (by omega) n m hn hm hc]; exact h2 u hu⟩

/-! ### The inverse threshold `b` -/

/-- `b(n) = max ({-1} ∪ {d : N d ≤ n})`, with `⊥ : WithBot ℕ` playing the role of `-1`. -/
def b (N : ℕ → ℕ) (n : ℕ) : WithBot ℕ :=
  ((Finset.range (n + 1)).filter (fun d => N d ≤ n)).max

theorem le_b_iff (P : PeriodicProfile h N Q) (d n : ℕ) :
    WithBot.some d ≤ b N n ↔ N d ≤ n := by
  unfold b
  constructor
  · intro hd
    set S := (Finset.range (n + 1)).filter (fun d => N d ≤ n) with hS
    by_cases hne : S.Nonempty
    · obtain ⟨m, hm⟩ := Finset.max_of_nonempty hne
      have hmS : m ∈ S := Finset.mem_of_max hm
      rw [hm] at hd
      have hdm : d ≤ m := WithBot.coe_le_coe.mp hd
      have : N m ≤ n := (Finset.mem_filter.mp hmS).2
      exact le_trans (P.N_mono hdm) this
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.max_empty] at hd
      exact absurd hd (by simp)
  · intro hd
    apply Finset.le_max
    rw [Finset.mem_filter, Finset.mem_range]
    have := P.N_ge d
    exact ⟨by omega, hd⟩

/-- `b` is monotone. -/
theorem b_mono (P : PeriodicProfile h N Q) : Monotone (b N) := by
  intro n m hnm
  by_cases hbot : b N n = ⊥
  · rw [hbot]; exact bot_le
  · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have h1 : N d ≤ n := (le_b_iff P d n).mp (le_of_eq hd)
    rw [← hd]
    exact (le_b_iff P d m).mpr (le_trans h1 hnm)

/-- `b(n) → ∞`. -/
theorem b_tendsto (P : PeriodicProfile h N Q) (d : ℕ) :
    ∀ n, N d ≤ n → WithBot.some d ≤ b N n :=
  fun n hn => (le_b_iff P d n).mpr hn

/-! ### Recurring levels -/

/-- The set of recurring low degrees. -/
def E (h : ℕ → ℕ∞) (N : ℕ → ℕ) : Set ℕ :=
  {d | ∃ n, N d ≤ n ∧ h n = (d : ℕ∞)}

/-- A recurring level occupies an entire residue class beyond its onset. -/
theorem PeriodicProfile.recurs (P : PeriodicProfile h N Q) {d : ℕ} (hd : d ∈ E h N) :
    ∃ c, N d ≤ c ∧ h c = (d : ℕ∞) ∧
      ∀ m, N d ≤ m → m % Q d = c % Q d → h m = (d : ℕ∞) := by
  obtain ⟨c, hc, hcd⟩ := hd
  exact ⟨c, hc, hcd, fun m hm hmc => (P.exact_level (le_refl d) hm hc hmc).mpr hcd⟩

/-- Prompt 06, target 2: membership of `E` is equivalent to arbitrarily large occurrences. -/
theorem PeriodicProfile.mem_E_iff (P : PeriodicProfile h N Q) (d : ℕ) :
    d ∈ E h N ↔ ∀ M, ∃ n, M ≤ n ∧ h n = (d : ℕ∞) := by
  constructor
  · intro hd M
    obtain ⟨c, hc, _, hrec⟩ := P.recurs hd
    refine ⟨c + M * Q d, ?_, hrec _ (by omega) (Nat.add_mul_mod_self_right _ _ _)⟩
    have := Nat.le_mul_of_pos_right M (P.Q_pos d)
    omega
  · intro hM
    obtain ⟨n, hn, hnd⟩ := hM (N d)
    exact ⟨n, hn, hnd⟩

/-- A finite value at a size beyond its own onset is recurring. -/
theorem mem_E_of_le (P : PeriodicProfile h N Q) {n d x : ℕ} (hn : N d ≤ n)
    (hx : h n = (x : ℕ∞)) (hxd : x ≤ d) : x ∈ E h N :=
  ⟨n, le_trans (P.N_mono hxd) hn, hx⟩

/-! ### The four types -/

/-- Eventual boundedness of the *extended-valued* profile. -/
def EventuallyBounded (h : ℕ → ℕ∞) : Prop :=
  ∃ B : ℕ, ∃ M : ℕ, ∀ n, M ≤ n → h n ≤ (B : ℕ∞)

def IsT1 (h : ℕ → ℕ∞) : Prop := EventuallyBounded h
def IsT2 (h : ℕ → ℕ∞) (N : ℕ → ℕ) : Prop := E h N = ∅
def IsT3 (h : ℕ → ℕ∞) (N : ℕ → ℕ) : Prop :=
  (E h N).Finite ∧ (E h N).Nonempty ∧ ¬ EventuallyBounded h
def IsT4 (h : ℕ → ℕ∞) (N : ℕ → ℕ) : Prop := (E h N).Infinite

/-- An eventually bounded profile has a finite nonempty recurring set. -/
theorem PeriodicProfile.bounded_E (P : PeriodicProfile h N Q) (hb : EventuallyBounded h) :
    (E h N).Finite ∧ (E h N).Nonempty := by
  obtain ⟨B, M, hBM⟩ := hb
  constructor
  · apply Set.Finite.subset (Set.finite_Iic B)
    intro d hd
    obtain ⟨n, hn, hnd⟩ := (P.mem_E_iff d).mp hd M
    have := hBM n hn
    rw [hnd] at this
    exact Set.mem_Iic.mpr (by exact_mod_cast this)
  · have hle := hBM (max M (N B)) (le_max_left _ _)
    obtain ⟨x, hx, hxB⟩ := enat_exists_of_le_coe hle
    exact ⟨x, mem_E_of_le P (le_max_right M (N B)) hx hxB⟩

/-- Prompt 06, target 3 (manuscript `thm:four`): the four alternatives are exhaustive
and pairwise disjoint. -/
theorem PeriodicProfile.exactly_one (P : PeriodicProfile h N Q) :
    (IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
    (¬ IsT1 h ∧ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
    (¬ IsT1 h ∧ ¬ IsT2 h N ∧ IsT3 h N ∧ ¬ IsT4 h N) ∨
    (¬ IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ IsT4 h N) := by
  unfold IsT1 IsT2 IsT3 IsT4
  by_cases hb : EventuallyBounded h
  · obtain ⟨hfin, hne⟩ := P.bounded_E hb
    left
    exact ⟨hb, hne.ne_empty, fun h3 => h3.2.2 hb, fun h4 => h4 hfin⟩
  · right
    by_cases hfin : (E h N).Finite
    · by_cases hemp : E h N = ∅
      · left
        exact ⟨hb, hemp, fun h3 => h3.2.1.ne_empty hemp, fun h4 => h4 hfin⟩
      · right; left
        exact ⟨hb, hemp, ⟨hfin, Set.nonempty_iff_ne_empty.mpr hemp, hb⟩, fun h4 => h4 hfin⟩
    · right; right
      refine ⟨hb, ?_, fun h3 => hfin h3.1, hfin⟩
      intro hemp
      apply hfin
      rw [hemp]
      exact Set.finite_empty

/-- Case (ii): if no level recurs, then `h n > d` for every `d` with `N d ≤ n`;
equivalently `h n > b n`. -/
theorem PeriodicProfile.T2_gt (P : PeriodicProfile h N Q) (h2 : IsT2 h N) {n d : ℕ}
    (hd : N d ≤ n) : (d : ℕ∞) < h n := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨x, hx, hxd⟩ := enat_exists_of_le_coe hlt
  have : x ∈ E h N := mem_E_of_le P hd hx hxd
  rw [h2] at this
  exact this

theorem PeriodicProfile.T2_gt_b (P : PeriodicProfile h N Q) (h2 : IsT2 h N) (n d : ℕ)
    (hd : WithBot.some d ≤ b N n) : (d : ℕ∞) < h n :=
  P.T2_gt h2 ((le_b_iff P d n).mp hd)

/-- Case (iii), structure: with `D = max E` and `q = Q D`, the residues split into a
nonempty proper set `U` of low classes (constant value `≤ D` beyond `N D`) and hard
classes on which `h n > b n`. -/
theorem PeriodicProfile.T3_structure (P : PeriodicProfile h N Q) (h3 : IsT3 h N) :
    ∃ D, D ∈ E h N ∧ (∀ d ∈ E h N, d ≤ D) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < Q D) ∧ U.Nonempty ∧ (∃ c, c < Q D ∧ c ∉ U) ∧
        (∀ n, N D ≤ n → n % Q D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, N D ≤ m → m % Q D = n % Q D → h m = (v : ℕ∞)) ∧
        (∀ n, N D ≤ n → n % Q D ∉ U → ∀ d, N d ≤ n → (d : ℕ∞) < h n) := by
  obtain ⟨hfin, hne, hnb⟩ := h3
  obtain ⟨D, hDE, hDmax⟩ : ∃ D, D ∈ E h N ∧ ∀ d ∈ E h N, d ≤ D := by
    obtain ⟨D, hD, hmax⟩ := hfin.exists_maximal hne
    refine ⟨D, hD, fun d hd => ?_⟩
    rcases le_total d D with hle | hle
    · exact hle
    · exact hmax hd hle
  refine ⟨D, hDE, hDmax, {c | c < Q D ∧ ∃ n, N D ≤ n ∧ n % Q D = c ∧ h n ≤ (D : ℕ∞)},
    fun c hc => hc.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn, hnD⟩ := hDE
    exact ⟨n % Q D, Nat.mod_lt _ (P.Q_pos D), n, hn, rfl, by rw [hnD]⟩
  · by_contra hall
    apply hnb
    refine ⟨D, N D, fun n hn => ?_⟩
    have hmem : n % Q D ∈ {c | c < Q D ∧ ∃ n, N D ≤ n ∧ n % Q D = c ∧ h n ≤ (D : ℕ∞)} := by
      by_contra hnot
      exact hall ⟨n % Q D, Nat.mod_lt _ (P.Q_pos D), hnot⟩
    obtain ⟨_, n', hn', hc, hle⟩ := hmem
    exact (P.periodic D D (le_refl _) n n' hn hn' hc.symm).mpr hle
  · rintro n hn ⟨_, n', hn', hc, hle⟩
    have hle' : h n ≤ (D : ℕ∞) := (P.periodic D D (le_refl _) n n' hn hn' hc.symm).mpr hle
    obtain ⟨v, hv, hvD⟩ := enat_exists_of_le_coe hle'
    exact ⟨v, hvD, fun m hm hmc => (P.exact_level hvD hm hn hmc).mpr hv⟩
  · intro n hn hU d hd
    by_contra hlt
    rw [not_lt] at hlt
    obtain ⟨x, hx, hxd⟩ := enat_exists_of_le_coe hlt
    have hxE : x ∈ E h N := mem_E_of_le P hd hx hxd
    have hxD : x ≤ D := hDmax x hxE
    apply hU
    refine ⟨Nat.mod_lt _ (P.Q_pos D), n, hn, rfl, ?_⟩
    rw [hx]
    exact_mod_cast hxD

/-- Case (iv): arbitrarily large finite degrees recur, each on a whole residue class
beyond its onset, and every member `m` of that class has `d ≤ b m`. -/
theorem PeriodicProfile.T4_structure (P : PeriodicProfile h N Q) (h4 : IsT4 h N) (B : ℕ) :
    ∃ d, B < d ∧ ∃ c, N d ≤ c ∧
      ∀ m, N d ≤ m → m % Q d = c % Q d → (h m = (d : ℕ∞) ∧ WithBot.some d ≤ b N m) := by
  obtain ⟨d, hdE, hBd⟩ := h4.exists_gt B
  obtain ⟨c, hc, _, hrec⟩ := P.recurs hdE
  exact ⟨d, hBd, c, hc, fun m hm hmc => ⟨hrec m hm hmc, (le_b_iff P d m).mpr hm⟩⟩

/-! ### Regressions -/

/-- `h ≡ ∞` has no recurring level: it is of type (ii), whatever the onset function. -/
theorem regression_top (N : ℕ → ℕ) : IsT2 (fun _ => (⊤ : ℕ∞)) N := by
  unfold IsT2 E
  ext d
  simp

/-- `h = 1` on odd sizes and `∞` on even sizes. -/
def oddOne (n : ℕ) : ℕ∞ := if n % 2 = 1 then 1 else ⊤

theorem oddOne_periodic : PeriodicProfile oddOne (fun d => d + 1) (fun _ => 2) where
  N_mono := fun a b hab => by simpa using hab
  N_ge := fun d => le_refl _
  Q_pos := fun _ => by norm_num
  periodic := by
    intro d t _ n m _ _ hc
    unfold oddOne
    rw [hc]

/-- The mixed example is of type (iii): one finite value, yet not eventually bounded. -/
theorem regression_oddOne : IsT3 oddOne (fun d => d + 1) := by
  have hnb : ¬ EventuallyBounded oddOne := by
    rintro ⟨B, M, hBM⟩
    have := hBM (2 * M) (by omega)
    unfold oddOne at this
    rw [if_neg (by omega)] at this
    simp at this
  have h1 : (1 : ℕ) ∈ E oddOne (fun d => d + 1) :=
    ⟨3, by norm_num, by unfold oddOne; simp⟩
  rcases oddOne_periodic.exactly_one with h' | h' | h' | h'
  · exact absurd h'.1 hnb
  · have := h'.2.1
    unfold IsT2 at this
    rw [this] at h1
    exact absurd h1 (Set.notMem_empty _)
  · exact h'.2.2.1
  · exfalso
    apply h'.2.2.2
    apply Set.Finite.subset (Set.finite_singleton 1)
    rintro d ⟨n, _, hn⟩
    unfold oddOne at hn
    split at hn
    · have : (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) := by simp
      rw [this, Nat.cast_inj] at hn
      simp [← hn]
    · simp at hn

end DegreeProfilesReview.Profiles
