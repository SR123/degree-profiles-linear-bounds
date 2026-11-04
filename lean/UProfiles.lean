/-
Claude, 27 Sep 2026.  Undecidability, part K1: types of perturbed profiles (intrinsic form).

For profiles `h, g, h' : ℕ → ℕ∞` (only sizes `n ≥ 1` matter):

* `iType_sandwich`: if `g` is eventually bounded and
  `max (h n) (g n) ≤ h' n ≤ max (h n) (g n) + 1` for all `n ≥ 1`, then `h'` and `h` have the same
  intrinsic type.  (An eventually bounded block and a `+1` never change the type.)
* `iType2_mono`: a profile dominating a T2 profile is T2.  (T2 dominates.)
* `iType3_of`: a profile bounded off the multiples of `p` and dominating a T2 profile on the
  multiples of `p` is T3.

The pigeonhole facts used: `rec_nonempty_of_frequently_le` (a profile that is infinitely often
at most `B` has a recurring value) and `rec_two`.
-/
import UWitCommon

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open DegreeProfilesReview.Profiles

section Pigeonhole
variable {h : ℕ → ℕ∞}

theorem exists_coe_of_le {x : ℕ∞} {B : ℕ} (hx : x ≤ B) : ∃ k : ℕ, x = k ∧ k ≤ B := by
  have hx' : x ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top B) hx
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hx'
  exact ⟨k, rfl, by exact_mod_cast hx⟩

/-- A profile that is infinitely often at most `B` has a recurring value. -/
theorem rec_nonempty_of_frequently_le (B : ℕ) (hf : ∀ M, ∃ n, M ≤ n ∧ h n ≤ B) :
    (Rec h).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hM : ∀ d : ℕ, ∃ M, ∀ n, M ≤ n → h n ≠ (d : ℕ∞) := by
    intro d
    by_contra hc
    push_neg at hc
    have : d ∈ Rec h := hc
    rw [hne] at this
    exact this
  choose M hM using hM
  obtain ⟨n, hn, hle⟩ := hf ((Finset.range (B + 1)).sup M)
  obtain ⟨d, hd, hdB⟩ := exists_coe_of_le hle
  exact hM d n (le_trans (Finset.le_sup (f := M) (Finset.mem_range.mpr (by omega))) hn) hd

/-- Two values taken infinitely often in total: one of them recurs. -/
theorem rec_two {d : ℕ} (hf : ∀ M, ∃ n, M ≤ n ∧ (h n = (d : ℕ∞) ∨ h n = ((d + 1 : ℕ) : ℕ∞))) :
    d ∈ Rec h ∨ d + 1 ∈ Rec h := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have h1' : ∃ M, ∀ n, M ≤ n → h n ≠ (d : ℕ∞) := by
    by_contra hc; push_neg at hc; exact h1 hc
  have h2' : ∃ M, ∀ n, M ≤ n → h n ≠ ((d + 1 : ℕ) : ℕ∞) := by
    by_contra hc; push_neg at hc; exact h2 hc
  obtain ⟨M1, hM1⟩ := h1'
  obtain ⟨M2, hM2⟩ := h2'
  obtain ⟨n, hn, hv⟩ := hf (M1 + M2)
  rcases hv with hv | hv
  · exact hM1 n (by omega) hv
  · exact hM2 n (by omega) hv

end Pigeonhole

/-! ### Arithmetic in `ℕ∞` -/

theorem max_coe (a b : ℕ) : max (a : ℕ∞) (b : ℕ∞) = ((max a b : ℕ) : ℕ∞) := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right (by exact_mod_cast hab), max_eq_right hab]
  · rw [max_eq_left (by exact_mod_cast hab), max_eq_left hab]

/-- From `max x y ≤ z ≤ max x y + 1` with `y ≤ C < z - 1`: `x = z - 1` or `x = z`. -/
theorem sandwich_val {x y : ℕ∞} {C e : ℕ} (hy : y ≤ C) (hce : C + 1 < e)
    (h1 : max x y ≤ (e : ℕ∞)) (h2 : (e : ℕ∞) ≤ max x y + 1) :
    x = ((e - 1 : ℕ) : ℕ∞) ∨ x = ((e - 1 + 1 : ℕ) : ℕ∞) := by
  obtain ⟨k, rfl, -⟩ := exists_coe_of_le (le_trans (le_max_left x y) h1)
  obtain ⟨m, rfl, hm⟩ := exists_coe_of_le hy
  rw [max_coe] at h1 h2
  have h1' : max k m ≤ e := by exact_mod_cast h1
  have h2' : e ≤ max k m + 1 := by exact_mod_cast h2
  have hk : k = e - 1 ∨ k = e - 1 + 1 := by omega
  rcases hk with hk | hk
  · exact Or.inl (by rw [hk])
  · exact Or.inr (by rw [hk])

/-- From `max x y ≤ z ≤ max x y + 1` with `x = d`, `y ≤ C < d`: `z = d` or `z = d + 1`. -/
theorem sandwich_val' {z y : ℕ∞} {C d : ℕ} (hy : y ≤ C) (hcd : C < d)
    (h1 : max (d : ℕ∞) y ≤ z) (h2 : z ≤ max (d : ℕ∞) y + 1) :
    z = (d : ℕ∞) ∨ z = ((d + 1 : ℕ) : ℕ∞) := by
  obtain ⟨m, rfl, hm⟩ := exists_coe_of_le hy
  rw [max_coe] at h1 h2
  have e2 : ((max d m : ℕ) : ℕ∞) + 1 = ((max d m + 1 : ℕ) : ℕ∞) := by push_cast; rfl
  rw [e2] at h2
  obtain ⟨k, rfl, hk⟩ := exists_coe_of_le h2
  have h1' : max d m ≤ k := by exact_mod_cast h1
  have hk' : k = d ∨ k = d + 1 := by omega
  rcases hk' with hk' | hk'
  · exact Or.inl (by rw [hk'])
  · exact Or.inr (by rw [hk'])

/-! ### Bounded perturbation does not change the type -/

section Sandwich
variable {h g h' : ℕ → ℕ∞} (hg : EventuallyBounded g)
  (hlo : ∀ n, 1 ≤ n → max (h n) (g n) ≤ h' n) (hhi : ∀ n, 1 ≤ n → h' n ≤ max (h n) (g n) + 1)
include hg hlo hhi

theorem eb_sandwich : EventuallyBounded h' ↔ EventuallyBounded h := by
  obtain ⟨C, N, hC⟩ := hg
  constructor
  · rintro ⟨B, M, hB⟩
    exact ⟨B, M + 1, fun n hn =>
      le_trans (le_trans (le_max_left _ _) (hlo n (by omega))) (hB n (by omega))⟩
  · rintro ⟨B, M, hB⟩
    refine ⟨max B C + 1, M + N + 1, fun n hn => le_trans (hhi n (by omega)) ?_⟩
    have e : ((max B C + 1 : ℕ) : ℕ∞) = max (B : ℕ∞) (C : ℕ∞) + 1 := by
      rw [max_coe]; push_cast; rfl
    rw [e]
    have h1 := hB n (by omega)
    have h2 := hC n (by omega)
    gcongr

theorem ne_sandwich : (Rec h').Nonempty ↔ (Rec h).Nonempty := by
  obtain ⟨C, N, hC⟩ := hg
  constructor
  · rintro ⟨e, he⟩
    refine rec_nonempty_of_frequently_le e fun M => ?_
    obtain ⟨n, hn, hv⟩ := he (M + 1)
    exact ⟨n, by omega, by
      rw [← hv]; exact le_trans (le_max_left _ _) (hlo n (by omega))⟩
  · rintro ⟨d, hd⟩
    refine rec_nonempty_of_frequently_le (max d C + 1) fun M => ?_
    obtain ⟨n, hn, hv⟩ := hd (M + N + 1)
    refine ⟨n, by omega, le_trans (hhi n (by omega)) ?_⟩
    have e : ((max d C + 1 : ℕ) : ℕ∞) = max (d : ℕ∞) (C : ℕ∞) + 1 := by
      rw [max_coe]; push_cast; rfl
    rw [e, hv]
    have h2 := hC n (by omega)
    gcongr

theorem fin_sandwich : (Rec h').Finite ↔ (Rec h).Finite := by
  obtain ⟨C, N, hC⟩ := hg
  constructor
  · intro hfin
    refine ((Set.finite_Iic C).union (hfin.union (hfin.image fun e => e - 1))).subset ?_
    intro d hd
    by_cases hdC : d ≤ C
    · exact Or.inl hdC
    · right
      have := rec_two (h := h') (d := d) fun M => by
        obtain ⟨n, hn, hv⟩ := hd (M + N + 1)
        refine ⟨n, by omega, sandwich_val' (hC n (by omega)) (by omega) ?_ ?_⟩
        · rw [← hv]; exact hlo n (by omega)
        · rw [← hv]; exact hhi n (by omega)
      rcases this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨d + 1, h1, by simp⟩
  · intro hfin
    refine ((Set.finite_Iic (C + 1)).union (hfin.union (hfin.image fun d => d + 1))).subset ?_
    intro e he
    by_cases heC : e ≤ C + 1
    · exact Or.inl heC
    · right
      have := rec_two (h := h) (d := e - 1) fun M => by
        obtain ⟨n, hn, hv⟩ := he (M + N + 1)
        refine ⟨n, by omega, sandwich_val (hC n (by omega)) (by omega) ?_ ?_⟩
        · rw [← hv]; exact hlo n (by omega)
        · rw [← hv]; exact hhi n (by omega)
      rcases this with h1 | h1
      · exact Or.inr ⟨e - 1, h1, by simp only; omega⟩
      · exact Or.inl (by rwa [show e - 1 + 1 = e by omega] at h1)

/-- **Bounded perturbation**: the type of `h'` is the type of `h`. -/
theorem iType_sandwich (τ : ℕ) : IType h' τ ↔ IType h τ := by
  have e1 := eb_sandwich hg hlo hhi
  have e2 := ne_sandwich hg hlo hhi
  have e3 := fin_sandwich hg hlo hhi
  rcases τ with _ | _ | _ | _ | _ | τ
  · exact Iff.rfl
  · exact e1
  · show Rec h' = ∅ ↔ Rec h = ∅
    rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, e2]
  · show (Rec h').Finite ∧ (Rec h').Nonempty ∧ ¬ EventuallyBounded h' ↔
      (Rec h).Finite ∧ (Rec h).Nonempty ∧ ¬ EventuallyBounded h
    rw [e1, e2, e3]
  · show (Rec h').Infinite ↔ (Rec h).Infinite
    rw [Set.Infinite, Set.Infinite, e3]
  · exact Iff.rfl

end Sandwich

/-! ### T2 dominates; a T3 criterion -/

/-- **T2 dominates.** -/
theorem iType2_mono {h h' : ℕ → ℕ∞} (h2 : IType h 2) (hle : ∀ n, 1 ≤ n → h n ≤ h' n) :
    IType h' 2 := by
  show Rec h' = ∅
  by_contra hne
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have : (Rec h).Nonempty := rec_nonempty_of_frequently_le e fun M => by
    obtain ⟨n, hn, hv⟩ := he (M + 1)
    exact ⟨n, by omega, by rw [← hv]; exact hle n (by omega)⟩
  have h2' : Rec h = ∅ := h2
  rw [h2'] at this
  exact Set.not_nonempty_empty this

/-- **A T3 criterion**: bounded off the multiples of `p`, above a T2 profile on them. -/
theorem iType3_of {h hη : ℕ → ℕ∞} {p : ℕ} (hp : 2 ≤ p) (C : ℕ) (hη2 : IType hη 2)
    (hoff : ∀ n, 1 ≤ n → ¬ p ∣ n → h n ≤ C) (hon : ∀ n, 1 ≤ n → p ∣ n → hη n ≤ h n) :
    IType h 3 := by
  have hη2' : Rec hη = ∅ := hη2
  have hndvd : ∀ M, ¬ p ∣ p * M + 1 := fun M hdvd => by
    have : p ∣ 1 := (Nat.dvd_add_right (Nat.dvd_mul_right p M)).mp hdvd
    have := Nat.le_of_dvd one_pos this
    omega
  refine ⟨?_, ?_, ?_⟩
  · refine (Set.finite_Iic C).subset fun e he => ?_
    by_contra hec
    simp only [Set.mem_Iic, not_le] at hec
    have : (Rec hη).Nonempty := rec_nonempty_of_frequently_le e fun M => by
      obtain ⟨n, hn, hv⟩ := he (M + 1)
      by_cases hpn : p ∣ n
      · exact ⟨n, by omega, by rw [← hv]; exact hon n (by omega) hpn⟩
      · have := hoff n (by omega) hpn
        rw [hv] at this
        exact absurd (by exact_mod_cast this) (by omega : ¬ e ≤ C)
    rw [hη2'] at this
    exact Set.not_nonempty_empty this
  · exact rec_nonempty_of_frequently_le C fun M =>
      ⟨p * M + 1, by nlinarith, hoff _ (by omega) (hndvd M)⟩
  · rintro ⟨B, M, hB⟩
    have : (Rec hη).Nonempty := rec_nonempty_of_frequently_le B fun M' =>
      ⟨p * (M + M' + 1), by nlinarith, le_trans (hon _ (by nlinarith) (Nat.dvd_mul_right _ _))
        (hB _ (by nlinarith))⟩
    rw [hη2'] at this
    exact Set.not_nonempty_empty this

end ClaudeUndec
