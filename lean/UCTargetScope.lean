/- Explicit statement adapters for the audited invariant-target development. -/
import UCClassification

set_option autoImplicit false
open MvPolynomial

namespace UniformConsequence.Scope
open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles
open DegreeProfilesReview.PC DegreeProfilesReview.NS

theorem onset_floor_le {k s n0 n : ℕ} (hn0 : n0 ≤ n) :
    onset k s n0 ((n - 2 * s - 1) / (2 * k)) ≤ n := by
  unfold onset
  split_ifs with h0
  · exact hn0
  · have h1 : (n - 2 * s - 1) / (2 * k) * (2 * k) ≤ n - 2 * s - 1 := Nat.div_mul_le_self _ _
    have hpos : 1 ≤ (n - 2 * s - 1) / (2 * k) := Nat.one_le_iff_ne_zero.mpr h0
    have hk : 0 < 2 * k := by
      rcases Nat.eq_zero_or_pos (2 * k) with h | h
      · rw [h, Nat.div_zero] at hpos; omega
      · exact h
    have e : 2 * (k * ((n - 2 * s - 1) / (2 * k)) + s) + 1 =
        (n - 2 * s - 1) / (2 * k) * (2 * k) + 2 * s + 1 := by ring
    have h2 : (n - 2 * s - 1) / (2 * k) * (2 * k) ≥ 2 * k :=
      Nat.le_mul_of_pos_left _ hpos
    rw [e]
    generalize (n - 2 * s - 1) / (2 * k) * (2 * k) = t at h1 h2
    omega

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p]
  {T : Template R} (G : Target T)

theorem periodic_for {h : ℕ → ℕ∞} (hh : h = G.pcProfile ∨ h = G.nsProfile) :
    PeriodicProfile h (onset T.k T.s G.nstar) (period p T.k T.s) := by
  rcases hh with rfl | rfl
  · exact G.periodic_pc p
  · exact G.periodic_ns p

include p in
/-- Natural floor bound in the extended order, including infinity. -/
theorem T2_extended {h : ℕ → ℕ∞} (hh : h = G.pcProfile ∨ h = G.nsProfile)
    (h2 : IsT2 h (onset T.k T.s G.nstar)) {n : ℕ} (hn : G.nstar ≤ n) :
    (((n - 2 * T.s - 1) / (2 * T.k) : ℕ) : ℕ∞) < h n :=
  (periodic_for p G hh).T2_gt h2 (onset_floor_le hn)

/-- Full easy-class constancy and complementary hard-class bound for T3. -/
theorem T3_full {h : ℕ → ℕ∞} (hh : h = G.pcProfile ∨ h = G.nsProfile)
    (h3 : IsT3 h (onset T.k T.s G.nstar)) :
    ∃ D : ℕ, D ∈ E h (onset T.k T.s G.nstar) ∧
      (∀ d ∈ E h (onset T.k T.s G.nstar), d ≤ D) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p T.k T.s D) ∧ U.Nonempty ∧
        (∃ c, c < period p T.k T.s D ∧ c ∉ U) ∧
        (∀ c ∈ U, ∃ v : ℕ, v ≤ D ∧ ∀ n, onset T.k T.s G.nstar D ≤ n →
            n % period p T.k T.s D = c → h n = (v : ℕ∞)) ∧
        (∀ n, onset T.k T.s G.nstar D ≤ n → n % period p T.k T.s D ∉ U →
            (((n - 2 * T.s - 1) / (2 * T.k) : ℕ) : ℕ∞) < h n) := by
  have P := periodic_for p G hh
  obtain ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, hUeasy, hUhard⟩ := P.T3_structure h3
  refine ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, ?_, ?_⟩
  · intro c hc
    set N := onset T.k T.s G.nstar D
    set Q := period p T.k T.s D
    have hQ : 0 < Q := P.Q_pos D
    have hrep : (c + Q * N) % Q = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hUlt c hc)]
    have hNle : N ≤ c + Q * N := le_add_left (Nat.le_mul_of_pos_left N hQ)
    obtain ⟨v, hvD, hv⟩ := hUeasy (c + Q * N) hNle (by rw [hrep]; exact hc)
    exact ⟨v, hvD, fun n hn hnc => hv n hn (by rw [hnc, hrep])⟩
  · intro n hn hnU
    have hn0 : G.nstar ≤ n := le_trans (n0_le_onset _ _ _ D) hn
    exact hUhard n hn hnU _ (onset_floor_le hn0)

/-- The concrete transfer directly in the additive NS convention. -/
theorem target_transfer_additive {d a n : ℕ} (hn0 : T.n0 ≤ n) (hnG : G.nG ≤ n)
    (hW : 2 * (T.k * d + T.s) - 1 ≤ n) (hrq : T.k * d + T.s < p ^ a) :
    (Derives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a)) ↔ Derives (T.inst n) d (G.poly n)) ∧
    (NSDerivesAdd (T.inst (n + p ^ a)) d (G.poly (n + p ^ a)) ↔
      NSDerivesAdd (T.inst n) d (G.poly n)) := by
  rw [derives_iff_mem_Vinf, derives_iff_mem_Vinf,
    nsDerivesAdd_iff_mem_NSspan, nsDerivesAdd_iff_mem_NSspan]
  exact target_transfer p G hn0 hnG hW hrq

include p in
/-- Whole-consequence comparison directly in the additive NS convention. -/
theorem uniform_comparison_additive :
    ∃ F : ℕ → ℕ, Monotone F ∧ (∀ t, t ≤ F t) ∧
      ∀ n t (g : MvPolynomial (T.Var.Rk n) R), Derives (T.inst n) t g →
        NSDerivesAdd (T.inst n) (F t) g := by
  obtain ⟨F, hF, hFt, hinc⟩ := uniform_inclusion p T
  refine ⟨F, hF, hFt, fun n t g hg => ?_⟩
  rw [nsDerivesAdd_iff_mem_NSspan]
  exact hinc n t (derives_iff_mem_Vinf.mp hg)

end UniformConsequence.Scope
