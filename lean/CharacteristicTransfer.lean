import MarkedBinomial
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic

namespace SelfContainedCycle044
open SelfContainedCycle035 SelfContainedCycle038 SelfContainedCycle040
open SelfContainedCycle042 SelfContainedCycle043

/-- Frobenius gives a polynomial supported only at multiples of the prime power. -/
theorem binomial_expand {F : Type*} [CommSemiring F] {p a L : ℕ}
    (hp : p.Prime) [CharP F p] (hL : p^a ∣ L) :
    (Polynomial.X + 1 : Polynomial F)^L =
      Polynomial.expand F (p^a) ((Polynomial.X + 1)^(L / p^a)) := by
  letI : Fact p.Prime := ⟨hp⟩
  conv_lhs => rw [← Nat.mul_div_cancel' hL]
  rw [pow_mul, add_pow_char_pow, one_pow]
  simp

/-- Every coefficient below the first positive supported degree vanishes. -/
theorem choose_cast_eq_zero {F : Type*} [CommSemiring F] {p a L k : ℕ}
    (hp : p.Prime) [CharP F p] (hL : p^a ∣ L) (hk0 : 0 < k) (hkq : k < p^a) :
    (L.choose k : F) = 0 := by
  have hq : 0 < p^a := pow_pos hp.pos a
  have hnd : ¬ p^a ∣ k := fun h => (Nat.le_of_dvd hk0 h).not_gt hkq
  rw [← Polynomial.coeff_X_add_one_pow F L k, binomial_expand hp hL,
    Polynomial.coeff_expand hq, if_neg hnd]

/-- The corresponding divisibility theorem is obtained in the prime residue ring. -/
theorem prime_dvd_choose {p a L k : ℕ} (hp : p.Prime)
    (hL : p^a ∣ L) (hk0 : 0 < k) (hkq : k < p^a) : p ∣ L.choose k := by
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp (choose_cast_eq_zero hp hL hk0 hkq)

/-- Characteristic transfer for the actual deterministic empty-leaf coefficient. -/
theorem normalizer_transfer {F : Type*} [CommRing F] {p a n m d L : ℕ}
    (hp : p.Prime) [CharP F p] (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (hdq : d < p^a) (hL : p^a ∣ L) :
    (normalizer (n+L) m R : F) = (normalizer n m R : F) := by
  rw [normalizer_binomial R hm hR hd hn L]
  push_cast
  rw [Finset.sum_eq_single 0]
  · simp [coefficient_zero R hm hR]
  · intro k hk hk0
    have hkd := Finset.mem_range.mp hk
    rw [choose_cast_eq_zero hp hL (Nat.pos_of_ne_zero hk0) (by omega), zero_mul]
  · simp

/-- Characteristic transfer for the actual marked appended-row sum. -/
theorem markedSum_transfer {F : Type*} [CommRing F] {p a n m d j L : ℕ}
    (hp : p.Prime) [CharP F p] (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ d) (hn : 2*d ≤ n) (hdq : d < p^a) (hL : p^a ∣ L) :
    (markedSum n L m R j : F) = 0 := by
  rw [marked_binomial_positive R hm hR hj hju hd hn L]
  push_cast
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hk0,hkd⟩ := Finset.mem_Icc.mp hk
  rw [choose_cast_eq_zero hp hL hk0 (hkd.trans_lt hdq), zero_mul]

/-- Sum form, with the actual integer normalizer cast term by term. -/
theorem appended_row_sum_zero {F : Type*} [CommRing F] {p a n m d j L : ℕ}
    (hp : p.Prime) [CharP F p] (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ d) (hn : 2*d ≤ n) (hdq : d < p^a) (hL : p^a ∣ L) :
    (∑ i ∈ tailRows n L, (normalizer (n+L) m (addEdge R i j) : F)) = 0 := by
  have h := markedSum_transfer (F:=F) hp R hm hR hj hju hd hn hdq hL
  simpa only [markedSum, Int.cast_sum] using h

/-- The old rectangular coefficient is the restriction of its square coefficient. -/
theorem square_coefficient_transfer {F : Type*} [CommRing F] {p a n m d : ℕ}
    (hp : p.Prime) [CharP F p] (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (hdq : d < p^a) (hnm : n ≤ m) (hL : p^a ∣ m-n) :
    (normalizer m m R : F) = (normalizer n m R : F) := by
  simpa only [Nat.add_sub_of_le hnm] using normalizer_transfer (F:=F) hp R hm hR hd hn hdq hL

/-- Exactly the omitted rows in the square column equation contribute zero. -/
theorem square_appended_row_sum_zero {F : Type*} [CommRing F] {p a n m d j : ℕ}
    (hp : p.Prime) [CharP F p] (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ d) (hn : 2*d ≤ n) (hdq : d < p^a)
    (hnm : n ≤ m) (hL : p^a ∣ m-n) :
    (∑ i ∈ Finset.Icc (n+1) m, (normalizer m m (addEdge R i j) : F)) = 0 := by
  simpa only [tailRows, Nat.add_sub_of_le hnm] using
    appended_row_sum_zero (F:=F) hp R hm hR hj hju hd hn hdq hL

/-- The concrete characteristic-two family: transfer from 6q-by-6q to 3q-by-6q. -/
theorem concrete_family_transfer {F : Type*} [CommRing F] [CharP F 2]
    (a : ℕ) (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid (3*2^a) (6*2^a))
    (hd : R.card < 2^a) :
    (normalizer (6*2^a) (6*2^a) R : F) = (normalizer (3*2^a) (6*2^a) R : F) := by
  apply square_coefficient_transfer (p:=2) (a:=a) (d:=R.card) (by decide) R hm hR le_rfl
  · omega
  · exact hd
  · omega
  · have heq : 6*2^a - 3*2^a = 2^a * 3 := by omega
    rw [heq]
    exact dvd_mul_right _ _

/-- The same concrete family, with the initial marked row and its full degree cost. -/
theorem concrete_family_marked {F : Type*} [CommRing F] [CharP F 2]
    (a : ℕ) (R : Edges) (j : ℕ) (hm : IsMatching R) (hR : R ⊆ grid (3*2^a) (6*2^a))
    (hj : j ∈ Finset.Icc 1 (6*2^a)) (hju : j ∉ cols R) (hd : R.card+1 < 2^a) :
    (∑ i ∈ Finset.Icc (3*2^a+1) (6*2^a),
      (normalizer (6*2^a) (6*2^a) (addEdge R i j) : F)) = 0 := by
  apply square_appended_row_sum_zero (p:=2) (a:=a) (d:=R.card+1)
    (by decide) R hm hR hj hju le_rfl
  · omega
  · exact hd
  · omega
  · have heq : 6*2^a - 3*2^a = 2^a * 3 := by omega
    rw [heq]
    exact dvd_mul_right _ _

/-- A higher prime power and nonzero multiple, instantiated for every commutative ring of characteristic 2. -/
theorem singleton_four_to_twelve {F : Type*} [CommRing F] [CharP F 2] :
    (normalizer 12 12 {(1,1)} : F) = (normalizer 4 12 {(1,1)} : F) := by
  exact square_coefficient_transfer (p:=2) (a:=2) (d:=2) (by decide) {(1,1)}
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The marked companion has a nonempty old matching and a genuinely unused column. -/
theorem singleton_marked_four_to_twelve {F : Type*} [CommRing F] [CharP F 2] :
    (∑ i ∈ Finset.Icc 5 12, (normalizer 12 12 (addEdge {(1,1)} i 2) : F)) = 0 := by
  exact square_appended_row_sum_zero (p:=2) (a:=2) (n:=4) (d:=2) (j:=2)
    (by decide) {(1,1)} (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Odd characteristic and k above p: the prime-power range is essential. -/
theorem odd_characteristic_example {F : Type*} [CommSemiring F] [CharP F 3] :
    (Nat.choose 18 6 : F) = 0 := by
  exact choose_cast_eq_zero (p:=3) (a:=2) (by decide) (by decide) (by decide) (by decide)

/-- The strict upper boundary cannot be replaced by a non-strict one. -/
theorem prime_power_boundary {p a : ℕ} (hp : p.Prime) :
    (Nat.choose (p^a) (p^a) : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp

/-- At exponent zero the positive vanishing interval is empty. -/
theorem exponent_zero_boundary {p k : ℕ} (hk : 0 < k) : ¬ k < p^0 := by
  simp only [pow_zero]
  omega

/-- The zero-appended-row boundary has no marked terms, without extra assumptions. -/
theorem zero_appended_boundary {F : Type*} [CommRing F] (n m : ℕ) (R : Edges) (j : ℕ) :
    (normalizer (n+0) m R : F) = (normalizer n m R : F) ∧ (markedSum n 0 m R j : F) = 0 := by
  simp

/-- The transferred coefficient is normalized at the empty matching for every size. -/
theorem empty_coefficient_one {F : Type*} [CommRing F] (n m : ℕ) :
    (normalizer n m ∅ : F) = 1 := by simp

end SelfContainedCycle044
