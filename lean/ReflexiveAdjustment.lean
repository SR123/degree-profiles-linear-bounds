/- Cycle 017: normalization inside the same finite algebra, preserving every
   already-valid inner-inverse identity under algebra representations. -/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

set_option autoImplicit false
namespace SelfContainedCycle017

variable {M : Type*} [Monoid M]

theorem power_period_from_collision (x : M) {i d : ℕ}
    (h : x^(i+d) = x^i) (n : ℕ) (hn : i ≤ n) :
    x^(n+d) = x^n := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  calc
    x^(i+t+d) = x^(i+d)*x^t := by rw [←pow_add]; congr 1; omega
    _ = x^(i+t) := by rw [h,pow_add]

theorem power_period_multiple (x : M) {i d : ℕ}
    (h : x^(i+d) = x^i) (n : ℕ) (hn : i ≤ n) (t : ℕ) :
    x^(n+t*d) = x^n := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      x^(n+(t+1)*d) = x^((n+t*d)+d) := by congr 1; ring
      _ = x^(n+t*d) := power_period_from_collision x h _ (by omega)
      _ = x^n := ih

/-- Eventual periodicity supplies a positive power satisfying f*x*f=f.
    This is an unconditional finite-monoid theorem. -/
theorem exists_reflexive_power [Finite M] (x : M) :
    ∃ k : ℕ, 0 < k ∧ x^(2*k+1) = x^k := by
  obtain ⟨i,j,hij,heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x^n)
  have hcol : ∃ i d : ℕ, 0 < d ∧ x^(i+d)=x^i := by
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨i,j-i,by omega,by simpa [Nat.add_sub_of_le (Nat.le_of_lt hij)] using heq.symm⟩
    · exact ⟨j,i-j,by omega,by simpa [Nat.add_sub_of_le (Nat.le_of_lt hji)] using heq⟩
  obtain ⟨i,d,hd,h⟩ := hcol
  let k := (i+2)*d-1
  have hm : i+2 ≤ (i+2)*d := by nlinarith
  have hk : 0 < k := by dsimp [k]; omega
  have hik : i ≤ k := by dsimp [k]; omega
  have he : 2*k+1 = k+(i+2)*d := by dsimp [k]; omega
  exact ⟨k,hk,by rw [he]; exact power_period_multiple x h k hik (i+2)⟩

variable {R : Type*} [Ring R]

def adjusted (z a : R) (k : ℕ) : R := (a*z)^k*a

theorem adjusted_outer (z a : R) {k : ℕ}
    (hk : (a*z)^(2*k+1)=(a*z)^k) :
    adjusted z a k * z * adjusted z a k = adjusted z a k := by
  unfold adjusted
  calc
    (a*z)^k*a*z*((a*z)^k*a) = ((a*z)^k*(a*z)*(a*z)^k)*a := by noncomm_ring
    _ = (a*z)^(k+1+k)*a := by rw [pow_add, pow_succ]
    _ = (a*z)^(2*k+1)*a := by congr 2; omega
    _ = (a*z)^k*a := by rw [hk]

theorem inner_identity_power (z a : R) (h : z*a*z=z) (k : ℕ) :
    z*(a*z)^k = z := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,←mul_assoc,ih,←mul_assoc,h]

theorem adjusted_preserves_inner (z a : R) (h : z*a*z=z) (k : ℕ) :
    z*adjusted z a k*z=z := by
  unfold adjusted
  calc
    z*((a*z)^k*a)*z = z*(a*z)^(k+1) := by rw [pow_succ]; noncomm_ring
    _ = z := inner_identity_power z a h (k+1)

theorem adjusted_map {S : Type*} [Ring S] (φ : R →+* S) (z a : R) (k : ℕ) :
    φ (adjusted z a k) = adjusted (φ z) (φ a) k := by simp [adjusted]

/-- One normalization exponent works before passing to any representation. -/
theorem finite_adjustment [Finite R] (z a : R) :
    ∃ k : ℕ, 0 < k ∧ adjusted z a k*z*adjusted z a k=adjusted z a k := by
  obtain ⟨k,hk,h⟩ := exists_reflexive_power (a*z)
  exact ⟨k,hk,adjusted_outer z a h⟩

theorem adjusted_preserves_representation {S : Type*} [Ring S]
    (φ : R →+* S) (z a : R) (h : φ z*φ a*φ z=φ z) (k : ℕ) :
    φ z*φ (adjusted z a k)*φ z=φ z := by
  rw [adjusted_map]
  exact adjusted_preserves_inner _ _ h k

end SelfContainedCycle017
