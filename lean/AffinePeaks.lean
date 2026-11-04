import RectangularPC
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.ZMod.Basic

namespace SelfContainedCycle073
open SelfContainedCycle054 SelfContainedCycle058
open DegreeProfilesReview.NS DegreeProfilesReview.PC

/-- The coefficient at a prime-power degree records precisely that base-p digit. -/
theorem choose_prime_power_digit {p : ℕ} (hp : p.Prime) (a n : ℕ) :
    Nat.ModEq p (n.choose (p^a)) (n/(p^a)) := by
  letI : Fact p.Prime := ⟨hp⟩
  induction a generalizing n with
  | zero => simp only [pow_zero,Nat.choose_one_right,Nat.div_one]; rfl
  | succ a ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=p) (n:=n) (k:=p^(a+1))
    have hmod : p^(a+1)%p=0 := by rw [pow_succ']; exact Nat.mul_mod_right _ _
    have hdiv : p^(a+1)/p=p^a := by rw [pow_succ']; exact Nat.mul_div_right _ hp.pos
    rw [hmod,hdiv,Nat.choose_zero_right,one_mul] at h
    have hrec := ih (n/p)
    rw [Nat.div_div_eq_div_mul,← pow_succ'] at hrec
    exact h.trans hrec

/-- No factorial division is used in the nonzero scalar for the NS upper certificate. -/
theorem choose_gap_scalar {p a r u : ℕ} (hp : p.Prime) :
    Nat.ModEq p ((r+p^a*u).choose (p^a)) (r.choose (p^a)+u) := by
  have hq : 0<p^a := pow_pos hp.pos _
  have hd : (r+p^a*u)/(p^a)=r/(p^a)+u := by
    rw [Nat.add_mul_div_left _ _ hq]
  have h := choose_prime_power_digit hp a (r+p^a*u)
  rw [hd] at h
  exact h.trans ((choose_prime_power_digit hp a r).add_right u).symm

/-- The exact scalar in any field of characteristic p is the quotient of the gap. -/
theorem choose_gap_scalar_field {F : Type*} [Field F] {p a r u : ℕ}
    (hp : p.Prime) [CharP F p] :
    (((r+p^a*u).choose (p^a) : ℕ) : F) - ((r.choose (p^a) : ℕ) : F) = (u : F) := by
  have he := CharP.natCast_eq_natCast' F p (choose_gap_scalar (a:=a) (r:=r) (u:=u) hp)
  push_cast at he
  rw [he]
  ring

theorem choose_gap_scalar_nonzero {F : Type*} [Field F] {p a r u : ℕ}
    (hp : p.Prime) [CharP F p] (hu : ¬p∣u) :
    (((r+p^a*u).choose (p^a) : ℕ) : F) - ((r.choose (p^a) : ℕ) : F) ≠ 0 := by
  rw [choose_gap_scalar_field hp]
  exact (CharP.cast_eq_zero_iff F p u).not.mpr hu

/-- Every residue equation with invertible slope has a genuine bounded solution. -/
theorem affine_residue_solution {q h : ℕ} (hq : 0<q) (hc : Nat.Coprime h q) (t : ℕ) :
    ∃ z<q, q∣h*z+t := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hu : IsUnit (h : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr hc
  let w : ZMod q := -(t : ZMod q)*(h : ZMod q)⁻¹
  have he : (h : ZMod q)*w+(t : ZMod q)=0 := by
    dsimp [w]
    calc
      (h : ZMod q)*(-(t : ZMod q)*(h : ZMod q)⁻¹)+(t : ZMod q) =
          -(t : ZMod q)*((h : ZMod q)*(h : ZMod q)⁻¹)+(t : ZMod q) := by ring
      _ = 0 := by rw [ZMod.mul_inv_of_unit _ hu]; ring
  refine ⟨w.val,ZMod.val_lt w,?_⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val] using he

/-- Divisibility and a linear-size witness interval, with the solution constructed above. -/
theorem affine_peak_rank {p h : ℕ} (hp : p.Prime) (hc : Nat.Coprime h p) (t k : ℕ) :
    ∃ n, p^k≤n ∧ n<2*p^k ∧ p^k∣h*n+t := by
  obtain ⟨z,hz,hd⟩ := affine_residue_solution (pow_pos hp.pos k) (hc.pow_right k) t
  refine ⟨z+p^k,by omega,by omega,?_⟩
  have he : h*(z+p^k)+t=(h*z+t)+h*p^k := by ring
  rw [he]
  exact dvd_add hd (dvd_mul_left _ _)

/-- Any actual refutation of the affine rectangle at a chosen peak exceeds n/2.
    All hypotheses are arithmetic parameters of the concrete family. -/
theorem affine_peak_degree {F : Type*} [Field F] {p k v a b h t n d : ℕ}
    (hp : p.Prime) [CharP F p] (ha : 1≤a) (hn : 1≤n) (hnq : n<2*p^k)
    (hdiv : p^k∣h*n+t)
    (href : NSRefutes {f : MvPolynomial (Var (a*n+b) (a*n+b+p^v*(h*n+t))) F |
        IsBAxiom (a*n+b) (a*n+b+p^v*(h*n+t)) f} d ∨
      Refutes {f : MvPolynomial (Var (a*n+b) (a*n+b+p^v*(h*n+t))) F |
        IsBAxiom (a*n+b) (a*n+b+p^v*(h*n+t)) f} d) : n<2*d := by
  by_contra! hdn
  have hnr : n≤a*n+b := by nlinarith
  have hdq : d<p^k := by omega
  have hdgap : p^k∣(a*n+b+p^v*(h*n+t))-(a*n+b) := by
    rw [Nat.add_sub_cancel_left]
    exact dvd_mul_of_dvd_right hdiv _
  have hno := no_PCRefutes_rectangle (F:=F) (p:=p) (a:=k) hp
    (hn.trans hnr) (hdn.trans hnr) hdq (by omega) hdgap
  rcases href with hs | hc
  · exact hno (refutes_of_nsRefutes hs)
  · exact hno hc

/-- Unbounded, simultaneous NS/ordinary-PC linear peaks for every normalized affine family.
    No exactness, periodicity, representation or design premise is assumed. -/
theorem affine_infinitely_large_peaks {F : Type*} [Field F] {p a h : ℕ}
    (hp : p.Prime) [CharP F p] (ha : 1≤a) (hc : Nat.Coprime h p) (v b t L : ℕ) :
    ∃ n, L<n ∧ ∀ d,
      (NSRefutes {f : MvPolynomial (Var (a*n+b) (a*n+b+p^v*(h*n+t))) F |
          IsBAxiom (a*n+b) (a*n+b+p^v*(h*n+t)) f} d ∨
        Refutes {f : MvPolynomial (Var (a*n+b) (a*n+b+p^v*(h*n+t))) F |
          IsBAxiom (a*n+b) (a*n+b+p^v*(h*n+t)) f} d) → n<2*d := by
  obtain ⟨n,hl,hu,hd⟩ := affine_peak_rank hp hc t L
  have hL : L<p^L := (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hp.two_le L)
  refine ⟨n,hL.trans_le hl,fun d href => ?_⟩
  exact affine_peak_degree hp ha (by omega) hu hd href

/-- A concrete offset family at an actual peak: n=59, rows=n+2, columns=2n+7. -/
theorem offset_peak_example {F : Type*} [Field F] [CharP F 2] :
    ¬ Refutes {f : MvPolynomial (Var 61 125) F | IsBAxiom 61 125 f} 29 := by
  exact no_PCRefutes_rectangle (p:=2) (a:=5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end SelfContainedCycle073
