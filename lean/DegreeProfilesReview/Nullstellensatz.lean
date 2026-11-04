/-
Total-product-degree Nullstellensatz certificates, the certificate-map (span) form used in
manuscript `lem:presentation`, and the same-degree simulation of NS by ordinary PC.

* `NSRefutes Γ d`: there are finitely many axioms `f ∈ Γ` with multipliers `a f` such that
  `∑ a f * f = 1` and every product `a f * f` has total degree `≤ d`
  (`totalDegree 0 = 0`, so zero products are harmless).  This is total-product degree,
  NOT multiplier degree.
* `NSspan Γ d`: the image of the certificate map, i.e. the `K`-span of the products
  `μ * f` over the formal basis of pairs `(μ, f)` with `deg μ + deg f ≤ d`.
* `nsRefutes_iff_one_mem_NSspan`: the two agree (uses that `K[x]` is a domain:
  `deg (a f) = deg a + deg f` for nonzero factors).
* `NSspan_le_Vinf`: every NS certificate is simulated by an ordinary PC derivation of the
  same degree, hence `d_PC ≤ d_NS`.

No external hypothesis is used.
-/
import DegreeProfilesReview.PCClosure
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

open MvPolynomial

namespace DegreeProfilesReview.NS

open DegreeProfilesReview.PC

variable {σ : Type*} {K : Type*} [Field K]

/-- A total-product-degree `≤ d` Nullstellensatz refutation of `Γ`. -/
def NSRefutes (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Prop :=
  ∃ (s : Finset (MvPolynomial σ K)) (a : MvPolynomial σ K → MvPolynomial σ K),
    (∀ f ∈ s, f ∈ Γ) ∧ (∀ f ∈ s, (a f * f).totalDegree ≤ d) ∧ ∑ f ∈ s, a f * f = 1

/-- Degree of a monomial exponent. -/
def mdeg (m : σ →₀ ℕ) : ℕ := m.sum fun _ e => e

/-- The image of the NS certificate map: span of `μ f` with `deg μ + deg f ≤ d`. -/
def NSspan (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Submodule K (MvPolynomial σ K) :=
  Submodule.span K
    {g | ∃ (m : σ →₀ ℕ) (f : MvPolynomial σ K), f ∈ Γ ∧ mdeg m + f.totalDegree ≤ d ∧
      g = monomial m (1 : K) * f}

/-! ### Certificates versus the span -/

theorem mul_mem_NSspan {Γ : Set (MvPolynomial σ K)} {d : ℕ} {a f : MvPolynomial σ K}
    (hf : f ∈ Γ) (h : a.totalDegree + f.totalDegree ≤ d) : a * f ∈ NSspan Γ d := by
  have hsum : a * f = ∑ v ∈ a.support, coeff v a • (monomial v (1 : K) * f) := by
    conv_lhs => rw [as_sum a, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [hsum]
  apply Submodule.sum_mem
  intro v hv
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨v, f, hf, ?_, rfl⟩
  have : mdeg v ≤ a.totalDegree := le_totalDegree hv
  omega

/-- Closure of "weak certificates" (degree bound in the additive form). -/
private def weakCert (Γ : Set (MvPolynomial σ K)) (d : ℕ) (g : MvPolynomial σ K) : Prop :=
  ∃ (s : Finset (MvPolynomial σ K)) (a : MvPolynomial σ K → MvPolynomial σ K),
    (∀ f ∈ s, f ∈ Γ) ∧ (∀ f ∈ s, a f = 0 ∨ (a f).totalDegree + f.totalDegree ≤ d) ∧
      ∑ f ∈ s, a f * f = g

private theorem weakCert_of_mem_NSspan {Γ : Set (MvPolynomial σ K)} {d : ℕ}
    {g : MvPolynomial σ K} (hg : g ∈ NSspan Γ d) : weakCert Γ d g := by
  classical
  unfold NSspan at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f, hf, hdeg, rfl⟩ := hx
    refine ⟨{f}, fun _ => monomial m 1, ?_, ?_, by simp⟩
    · intro f' hf'; rw [Finset.mem_singleton] at hf'; subst hf'; exact hf
    · intro f' hf'
      rw [Finset.mem_singleton] at hf'; subst hf'
      right
      show (monomial m (1 : K)).totalDegree + f'.totalDegree ≤ d
      have : (monomial m (1 : K)).totalDegree ≤ mdeg m := totalDegree_monomial_le m 1
      omega
  | zero => exact ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, a, hs, ha, rfl⟩ := hx
    obtain ⟨s', a', hs', ha', rfl⟩ := hy
    refine ⟨s ∪ s', fun f => (if f ∈ s then a f else 0) + (if f ∈ s' then a' f else 0),
      ?_, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_union.mp hf with h | h
      · exact hs f h
      · exact hs' f h
    · intro f _
      by_cases h1 : f ∈ s <;> by_cases h2 : f ∈ s'
      · simp only [h1, h2, if_true]
        rcases ha f h1 with e1 | e1 <;> rcases ha' f h2 with e2 | e2
        · left; rw [e1, e2, add_zero]
        · right; rw [e1, zero_add]; exact e2
        · right; rw [e2, add_zero]; exact e1
        · right
          have := totalDegree_add (a f) (a' f)
          have := max_le_iff.mpr ⟨le_refl (max (a f).totalDegree (a' f).totalDegree), le_refl _⟩
          rcases le_total (a f).totalDegree (a' f).totalDegree with h | h
          · rw [max_eq_right h] at *; omega
          · rw [max_eq_left h] at *; omega
      · simp only [h1, h2, if_true, if_false, add_zero]; exact ha f h1
      · simp only [h1, h2, if_true, if_false, zero_add]; exact ha' f h2
      · left; simp [h1, h2]
    · simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
        Finset.union_inter_cancel_right]
  | smul c x _ hx =>
    obtain ⟨s, a, hs, ha, rfl⟩ := hx
    refine ⟨s, fun f => c • a f, hs, ?_, ?_⟩
    · intro f hf
      rcases ha f hf with e | e
      · left
        show c • a f = 0
        rw [e, smul_zero]
      · right
        show (c • a f).totalDegree + f.totalDegree ≤ d
        have := totalDegree_smul_le c (a f)
        omega
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [smul_mul_assoc]

/-- Manuscript `lem:presentation`, first sentence: the image of the certificate map contains
`1` exactly when a total-product-degree `≤ d` NS refutation exists. -/
theorem nsRefutes_iff_one_mem_NSspan {Γ : Set (MvPolynomial σ K)} {d : ℕ} :
    NSRefutes Γ d ↔ (1 : MvPolynomial σ K) ∈ NSspan Γ d := by
  constructor
  · rintro ⟨s, a, hs, hdeg, hsum⟩
    rw [← hsum]
    apply Submodule.sum_mem
    intro f hf
    by_cases ha : a f = 0
    · rw [ha, zero_mul]; exact Submodule.zero_mem _
    by_cases hf0 : f = 0
    · rw [hf0, mul_zero]; exact Submodule.zero_mem _
    apply mul_mem_NSspan (hs f hf)
    rw [← totalDegree_mul_of_isDomain ha hf0]
    exact hdeg f hf
  · intro h
    obtain ⟨s, a, hs, ha, hsum⟩ := weakCert_of_mem_NSspan h
    refine ⟨s, a, hs, ?_, hsum⟩
    intro f hf
    rcases ha f hf with e | e
    · rw [e, zero_mul]; simp
    · exact le_trans (totalDegree_mul _ _) e

theorem NSRefutes.mono {Γ : Set (MvPolynomial σ K)} {d d' : ℕ} (hdd : d ≤ d')
    (h : NSRefutes Γ d) : NSRefutes Γ d' := by
  obtain ⟨s, a, hs, hdeg, hsum⟩ := h
  exact ⟨s, a, hs, fun f hf => le_trans (hdeg f hf) hdd, hsum⟩

/-! ### PC simulates NS in the same degree -/

/-- A variable times a low-degree consequence is a consequence. -/
theorem X_mul_mem_Vinf {Γ : Set (MvPolynomial σ K)} {d : ℕ} (i : σ) {g : MvPolynomial σ K}
    (hg : g ∈ Vinf Γ d) (hlow : g ∈ lowDeg σ K d) : X i * g ∈ Vinf Γ d := by
  obtain ⟨j, hj⟩ := mem_Vinf_iff.mp hg
  apply (le_iSup (V Γ d) (j + 1) : V Γ d (j + 1) ≤ Vinf Γ d)
  apply (le_sup_right : mulStep (V Γ d j ⊓ lowDeg σ K d) ≤ step d (V Γ d j))
  exact Submodule.subset_span ⟨i, g, ⟨hj, hlow⟩, rfl⟩

theorem monomial_mul_mem_Vinf {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K}
    (hf : f ∈ Γ) : ∀ (n : ℕ) (m : σ →₀ ℕ), mdeg m = n → mdeg m + f.totalDegree ≤ d →
      monomial m (1 : K) * f ∈ Vinf Γ d := by
  intro n
  induction n with
  | zero =>
    intro m hm hd
    have hm0 : m = 0 := by
      ext i
      by_contra hne
      have hi : i ∈ m.support := Finsupp.mem_support_iff.mpr hne
      have : m i ≤ mdeg m := Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _) hi
      have hpos : 0 < m i := Nat.pos_of_ne_zero hne
      omega
    subst hm0
    have : (monomial (0 : σ →₀ ℕ) (1 : K)) = 1 := rfl
    rw [this, one_mul]
    apply (le_iSup (V Γ d) 0 : V Γ d 0 ≤ Vinf Γ d)
    exact Submodule.subset_span ⟨hf, by omega⟩
  | succ n ih =>
    intro m hm hd
    have hex : ∃ i, m i ≠ 0 := by
      by_contra hno
      push_neg at hno
      have : m = 0 := by ext i; exact hno i
      rw [this] at hm
      simp [mdeg] at hm
    obtain ⟨i, hi⟩ := hex
    have hle : Finsupp.single i 1 ≤ m := by
      intro j
      by_cases hji : j = i
      · subst hji; simp; omega
      · simp [Ne.symm hji]
    set m' := m - Finsupp.single i 1 with hm'
    have hadd : Finsupp.single i 1 + m' = m := add_tsub_cancel_of_le hle
    have hdeg' : mdeg m = 1 + mdeg m' := by
      rw [← hadd]
      unfold mdeg
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl]
    have hrec := ih m' (by omega) (by omega)
    have hmon : monomial m (1 : K) * f = X i * (monomial m' (1 : K) * f) := by
      rw [← hadd, monomial_single_add, pow_one, mul_assoc]
    rw [hmon]
    apply X_mul_mem_Vinf i hrec
    unfold lowDeg
    rw [if_neg (by omega), mem_restrictTotalDegree]
    have h1 := totalDegree_mul (monomial m' (1 : K)) f
    have h2 : (monomial m' (1 : K)).totalDegree ≤ mdeg m' := totalDegree_monomial_le m' 1
    omega

/-- The certificate image lies in the PC closure. -/
theorem NSspan_le_Vinf (Γ : Set (MvPolynomial σ K)) (d : ℕ) : NSspan Γ d ≤ Vinf Γ d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m, f, hf, hdeg, rfl⟩
  exact monomial_mul_mem_Vinf hf _ m rfl hdeg

/-- **`d_PC ≤ d_NS`, by an actual simulation.** -/
theorem refutes_of_nsRefutes {Γ : Set (MvPolynomial σ K)} {d : ℕ} (h : NSRefutes Γ d) :
    Refutes Γ d :=
  refutes_iff_one_mem_Vinf.mpr (NSspan_le_Vinf Γ d (nsRefutes_iff_one_mem_NSspan.mp h))

open Classical in
/-- Minimum total-product NS degree (`⊤` if there is no refutation). -/
noncomputable def nsDegree (Γ : Set (MvPolynomial σ K)) : ℕ∞ :=
  if h : ∃ d, NSRefutes Γ d then ((Nat.find h : ℕ) : ℕ∞) else ⊤

theorem nsDegree_le_iff (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    nsDegree Γ ≤ (d : ℕ∞) ↔ NSRefutes Γ d := by
  classical
  unfold nsDegree
  split
  · rename_i h
    rw [Nat.cast_le]
    exact ⟨fun hle => (Nat.find_spec h).mono hle, fun hd => Nat.find_min' h hd⟩
  · rename_i h
    simp only [top_le_iff, ENat.coe_ne_top, false_iff]
    exact fun hd => h ⟨d, hd⟩

/-- Two extended naturals with the same finite upper bounds are equal. -/
theorem enat_eq_of_forall_le_iff {x y : ℕ∞}
    (h : ∀ d : ℕ, x ≤ (d : ℕ∞) ↔ y ≤ (d : ℕ∞)) : x = y := by
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => rfl
    | coe b => exact absurd ((h b).mpr (le_refl _)) (by simp)
  | coe a =>
    induction y using ENat.recTopCoe with
    | top => exact absurd ((h a).mp (le_refl _)) (by simp)
    | coe b =>
      have h1 := (h a).mp (le_refl _)
      have h2 := (h b).mpr (le_refl _)
      exact le_antisymm h2 h1

/-- The pointwise comparison `d_PC ≤ d_NS` in `ℕ∞`, including the value `⊤`. -/
theorem pcDegree_le_nsDegree (Γ : Set (MvPolynomial σ K)) : pcDegree Γ ≤ nsDegree Γ := by
  induction hns : nsDegree Γ using ENat.recTopCoe with
  | top => exact le_top
  | coe a =>
    rw [pcDegree_le_iff]
    apply refutes_of_nsRefutes
    rw [← nsDegree_le_iff, hns]

end DegreeProfilesReview.NS
