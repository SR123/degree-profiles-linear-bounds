/-
Claude, 27 Sep 2026.  Undecidability, part F: the types of the witnesses and of the reduction
outputs.

For every prime `p` and every field `K` of characteristic `p` (NS profiles; ordinary PC via
`pcType_iff_nsType`):

* `psi1` has type T1, `eta` type T2, `psi3 p = eta ∧ χ_p` type T3, `bhat` type T4;
* all four have no model of any size `n ≥ 1`;
* for any counter machine `M` and witness `ψ` (well formed, no nonempty models):
  - if `M` does not halt, `ψ ∧ θ_M` has exactly the NS profile of `ψ` at every `n ≥ 1` (the `θ_M`
    block has a root: switch (i) and the satisfiable-block lemma), hence the type of `ψ`;
  - if `M` halts, `ψ ∧ θ_M` is eventually bounded (switch (iii)), type T1;
  - `ψ ∧ θ_M` has no model of any size `n ≥ 1`.
-/
import UWitB
import UHalt

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open MvPolynomial DegreeProfilesReview.NS DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles

theorem nsRefutes_of_eq {σ K : Type} [Field K] {Γ : Set (MvPolynomial σ K)} {d : ℕ}
    (h : nsDegree Γ = d) : NSRefutes Γ d := (nsDegree_le_iff Γ d).mp (le_of_eq h)

theorem exists_of_le_coe {x : ℕ∞} {B : ℕ} (h : x ≤ B) : ∃ d : ℕ, x = d ∧ d ≤ B := by
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top B) h
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp hx
  exact ⟨d, rfl, by exact_mod_cast h⟩

/-- The third witness: `η ∧ χ_p`. -/
def psi3 (p : ℕ) : Sentence := conj eta (chi p)

theorem psi3_WF (p : ℕ) : WF (psi3 p) := conj_WF eta_WF (chi_WF p)

/-- The witnesses `ψ₁, …, ψ₄`. -/
def wit (p : ℕ) : ℕ → Sentence
  | 1 => psi1
  | 2 => eta
  | 3 => psi3 p
  | 4 => bhat
  | _ => psi1

theorem wit_WF (p τ : ℕ) : WF (wit p τ) := by
  rcases τ with _ | _ | _ | _ | _ | τ
  · exact psi1_WF
  · exact psi1_WF
  · exact eta_WF
  · exact psi3_WF p
  · exact bhat_WF
  · exact psi1_WF

theorem wit_no_model (p τ : ℕ) {n : ℕ} (hn : 0 < n) : ¬ HasModelOfSize (wit p τ) n := by
  rcases τ with _ | _ | _ | _ | _ | τ
  · exact psi1_no_model hn
  · exact psi1_no_model hn
  · exact eta_no_model hn
  · exact fun h => eta_no_model hn (hasModel_conj eta (chi p) n eta_WF (chi_WF p) hn h).1
  · exact bhat_no_model hn
  · exact psi1_no_model hn

section WitnessTypes
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
include hp

set_option linter.unusedSectionVars false in
theorem psi1_type : IType (template psi1 K).nsProfile 1 :=
  ⟨1, 1, fun n hn => (nsDegree_le_iff _ 1).mpr (psi1_nsRefutes K (by omega))⟩

theorem eta_type : IType (template eta K).nsProfile 2 := by
  show Rec _ = ∅
  ext d
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hd
  obtain ⟨n, hn, hv⟩ := hd (3 * p * (d + 1) + 3)
  have := eta_lower K hp.out (by omega) (nsRefutes_of_eq hv)
  have : 3 * p * d ≤ 3 * p * (d + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

omit [CharP K p] in
/-- At multiples of `p` the conjunction has exactly the degree of `η`. -/
theorem psi3_eq_eta {n : ℕ} (hn : 0 < n) (hpn : p ∣ n) :
    (template (psi3 p) K).nsProfile n = (template eta K).nsProfile n := by
  obtain ⟨y, hy⟩ := (hasRoot_iff (chi p) K hn).mpr (chi_model hp.out.two_le hn hpn)
  exact nsDegree_conj_eq_left eta (chi p) n K eta_WF (chi_WF p) y hy

/-- Off the multiples of `p` the conjunction has degree at most `p`. -/
theorem psi3_le {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) :
    (template (psi3 p) K).nsProfile n ≤ (p : ℕ∞) := by
  refine le_trans (nsDegree_conj_le_right eta (chi p) n K (chi_WF p)) ?_
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.two_le; omega⟩
  exact (nsDegree_le_iff _ _).mpr (chi_nsRefutes q K hn hpn)

theorem psi3_type : IType (template (psi3 p) K).nsProfile 3 := by
  have hp1 := hp.out.one_lt
  refine ⟨?_, ?_, ?_⟩
  · -- only levels `≤ p` recur
    refine Set.Finite.subset (Set.finite_Iic p) fun d hd => ?_
    by_contra hdp
    simp only [Set.mem_Iic, not_le] at hdp
    obtain ⟨n, hn, hv⟩ := hd (3 * p * (d + 1) + 3)
    by_cases hpn : p ∣ n
    · rw [psi3_eq_eta p K (by omega) hpn] at hv
      have := eta_lower K hp.out (by omega) (nsRefutes_of_eq hv)
      have : 3 * p * d ≤ 3 * p * (d + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · have := psi3_le p K (by omega) hpn
      rw [hv] at this
      exact absurd (by exact_mod_cast this) (by omega : ¬ d ≤ p)
  · -- some level `≤ p` recurs, along the sizes `≡ 1 (mod p)`
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hM : ∀ d : ℕ, ∃ M, ∀ n, M ≤ n → (template (psi3 p) K).nsProfile n ≠ (d : ℕ∞) := by
      intro d
      by_contra hc
      push_neg at hc
      have : d ∈ Rec (template (psi3 p) K).nsProfile := hc
      rw [hne] at this; exact this
    choose M hMs using hM
    have hMle : ∀ d ≤ p, M d ≤ (Finset.range (p + 1)).sup M := fun d hd =>
      Finset.le_sup (f := M) (Finset.mem_range.mpr (by omega))
    have hpn : ¬ p ∣ p * ((Finset.range (p + 1)).sup M + 1) + 1 := by
      intro hdvd
      have : p ∣ 1 := (Nat.dvd_add_right (Nat.dvd_mul_right p _)).mp hdvd
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
    obtain ⟨d, hd, hdp⟩ := exists_of_le_coe (psi3_le p K (by omega) hpn)
    exact hMs d _ (le_trans (hMle d hdp) (by nlinarith)) hd
  · -- unbounded along the multiples of `p`
    rintro ⟨B, M, hB⟩
    have hpn : p ∣ p * (3 * (B + 1) + M + 1) := Nat.dvd_mul_right p _
    have hnM : M ≤ p * (3 * (B + 1) + M + 1) := by nlinarith
    have hle := hB _ hnM
    rw [psi3_eq_eta p K (by positivity) hpn] at hle
    have := eta_lower K hp.out (by nlinarith) ((nsDegree_le_iff _ B).mp hle)
    have : 3 * p * B < p * (3 * (B + 1) + M + 1) := by nlinarith
    omega

theorem bhat_type : IType (template bhat K).nsProfile 4 := by
  show (Rec (template bhat K).nsProfile).Infinite
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  -- the level `b` has a recurring value `≥ p^b > b`
  have hq : 0 < p ^ b := pow_pos hp.out.pos b
  have hbq : b < p ^ b := Nat.lt_pow_self hp.out.one_lt
  -- at `n = p^b (p k + 1)` the degree lies in `[p^b, p^b + 4]`
  have hval : ∀ k, ∃ d : ℕ, (template bhat K).nsProfile (p ^ b * (p * (k + 1) + 1)) = d ∧
      p ^ b ≤ d ∧ d ≤ p ^ b + 4 := by
    intro k
    have hn : 0 < p ^ b * (p * (k + 1) + 1) := Nat.mul_pos hq (by omega)
    have hu : ¬ p ∣ p * (k + 1) + 1 := by
      intro hdvd
      have : p ∣ 1 := (Nat.dvd_add_right (Nat.dvd_mul_right p _)).mp hdvd
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
    obtain ⟨d, hd, hdle⟩ := exists_of_le_coe ((nsDegree_le_iff _ _).mpr
      (bhat_upper K hn hp.out hu rfl))
    refine ⟨d, hd, ?_, hdle⟩
    by_contra hlt
    push_neg at hlt
    have h3 : 3 ≤ p * (k + 1) + 1 := by nlinarith [hp.out.two_le]
    have h4 : 2 * d ≤ p ^ b * (p * (k + 1) + 1) := by nlinarith
    exact bhat_lower K hp.out hn (a := b) (Nat.dvd_mul_right _ _) h4 hlt (nsRefutes_of_eq hd)
  -- pigeonhole over the five values
  have hM' : ∀ d : ℕ, ∃ M, p ^ b ≤ d → d ≤ p ^ b + 4 → ∀ n, M ≤ n →
      (template bhat K).nsProfile n ≠ (d : ℕ∞) := by
    intro d
    by_cases h1 : p ^ b ≤ d ∧ d ≤ p ^ b + 4
    · by_contra hc
      push_neg at hc
      have hrec : d ∈ Rec (template bhat K).nsProfile := by
        intro M
        obtain ⟨_, _, n, hn, hv⟩ := hc M
        exact ⟨n, hn, hv⟩
      have := hb hrec
      omega
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h1⟩
  choose M hMs using hM'
  obtain ⟨d, hd, h1, h2⟩ := hval ((Finset.range (p ^ b + 5)).sup M)
  apply hMs d h1 h2 _ _ hd
  have hsup : M d ≤ (Finset.range (p ^ b + 5)).sup M :=
    Finset.le_sup (f := M) (Finset.mem_range.mpr (by omega))
  have h5 : (Finset.range (p ^ b + 5)).sup M ≤ p * ((Finset.range (p ^ b + 5)).sup M + 1) :=
    le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_left _ hp.out.pos)
  have h6 : p * ((Finset.range (p ^ b + 5)).sup M + 1) + 1 ≤
      p ^ b * (p * ((Finset.range (p ^ b + 5)).sup M + 1) + 1) := Nat.le_mul_of_pos_left _ hq
  omega

/-- **The witnesses have the four types** (NS). -/
theorem wit_type (τ : ℕ) (hτ : τ ∈ ({1, 2, 3, 4} : Set ℕ)) :
    NSType (template (wit p τ) K) τ := by
  rw [nsType_iff_intrinsic p]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl | rfl | rfl
  · exact psi1_type p K
  · exact eta_type p K
  · exact psi3_type p K
  · exact bhat_type p K

end WitnessTypes

/-! ### The reduction `M ↦ ψ ∧ θ_M` -/

section Reduction
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
include hp

/-- **Non-halting**: the conjunction has the type of the witness. -/
theorem conj_type_nonhalt (ψ : Sentence) (hψ : WF ψ) (P : Prog) (hP : ¬ P.Halts) (τ : ℕ) :
    NSType (template (conj ψ (theta P)) K) τ ↔ NSType (template ψ K) τ := by
  rw [nsType_iff_intrinsic p, nsType_iff_intrinsic p]
  apply iType_congr
  intro n hn
  obtain ⟨y, hy⟩ := (hasRoot_iff (theta P) K (n := n) (by omega)).mpr (switch_i P hP (by omega))
  exact nsDegree_conj_eq_left ψ (theta P) n K hψ (theta_WF P) y hy

end Reduction

section Reduction2
variable (K : Type) [Field K]

/-- **Halting**: the conjunction is eventually bounded. -/
theorem conj_type_halt (ψ : Sentence) (P : Prog) (hP : P.Halts) :
    NSType (template (conj ψ (theta P)) K) 1 := by
  obtain ⟨C, N, hC⟩ := theta_eventually_bounded P K hP
  exact ⟨C, N, fun n hn => le_trans (nsDegree_conj_le_right ψ (theta P) n K (theta_WF P))
    (hC n hn)⟩

/-- The conjunction with an all-size-unsatisfiable witness is all-size unsatisfiable. -/
theorem conj_no_model (ψ : Sentence) (hψ : WF ψ) (hno : ∀ n, 0 < n → ¬ HasModelOfSize ψ n)
    (P : Prog) {n : ℕ} (hn : 0 < n) : ¬ HasModelOfSize (conj ψ (theta P)) n :=
  fun h => hno n hn (hasModel_conj ψ (theta P) n hψ (theta_WF P) hn h).1

end Reduction2

end ClaudeUndec
