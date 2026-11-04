/-
Claude, 27 Sep 2026.  Undecidability, part C0: Nullstellensatz tools.

* `mul_mem_NSspan_of`: multiplying a member of `NSspan Γ e` by a polynomial of degree `≤ k`
  gives a member of `NSspan Γ (e + k)`.
* `map_NSspan`: an algebra map sending variables to polynomials of degree `≤ 1`, and every
  axiom of `Γ` into `NSspan Δ (its degree)`, maps `NSspan Γ d` into `NSspan Δ d`.  Hence
  `nsRefutes_of_hom` and `nsDegree_le_of_hom`.  This covers renaming, substituting constants
  (for a satisfiable block) and linear substitutions.
* `not_nsRefutes_of_root`: a system with a common root has no NS refutation (any degree).
-/
import DegreeProfilesReview.Nullstellensatz

set_option autoImplicit false
open MvPolynomial DegreeProfilesReview.NS

namespace ClaudeUndec

variable {σ τ K : Type} [Field K]

theorem mdeg_eq_degree (m : σ →₀ ℕ) : DegreeProfilesReview.NS.mdeg m = m.degree := by
  unfold DegreeProfilesReview.NS.mdeg Finsupp.degree
  rfl

theorem totalDegree_monomial_one_le (m : σ →₀ ℕ) :
    (monomial m (1 : K)).totalDegree ≤ DegreeProfilesReview.NS.mdeg m := by
  classical
  unfold DegreeProfilesReview.NS.mdeg
  exact le_of_eq (totalDegree_monomial m one_ne_zero)

theorem NSspan_mono' {Γ : Set (MvPolynomial σ K)} {d d' : ℕ} (h : d ≤ d') :
    NSspan Γ d ≤ NSspan Γ d' := by
  apply Submodule.span_mono
  rintro g ⟨m, f, hf, hdeg, rfl⟩
  exact ⟨m, f, hf, le_trans hdeg h, rfl⟩

theorem mem_NSspan_of_mem {Γ : Set (MvPolynomial σ K)} {f : MvPolynomial σ K} (hf : f ∈ Γ) :
    f ∈ NSspan Γ f.totalDegree := by
  have := mul_mem_NSspan (d := f.totalDegree) (a := (1 : MvPolynomial σ K)) hf (by simp)
  simpa using this

/-- Multiplying by a polynomial of degree `≤ k` raises the NS degree by at most `k`. -/
theorem mul_mem_NSspan_of {Γ : Set (MvPolynomial σ K)} {e k : ℕ} {g h : MvPolynomial σ K}
    (hg : g ∈ NSspan Γ e) (hh : h.totalDegree ≤ k) : h * g ∈ NSspan Γ (e + k) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f, hf, hdeg, rfl⟩ := hx
    rw [← mul_assoc]
    apply mul_mem_NSspan hf
    have h1 := totalDegree_mul h (monomial m (1 : K))
    have h2 := totalDegree_monomial_one_le (K := K) m
    omega
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- Algebra maps sending variables to degree-`≤ 1` polynomials do not raise degree. -/
theorem totalDegree_map_le (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hX : ∀ i, (φ (X i)).totalDegree ≤ 1) (f : MvPolynomial σ K) :
    (φ f).totalDegree ≤ f.totalDegree := by
  classical
  have hm : ∀ (μ : σ →₀ ℕ) (c : K), (φ (monomial μ c)).totalDegree ≤ μ.sum fun _ e => e := by
    intro μ c
    have hc : φ (C c) = C c := φ.commutes c
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod, hc]
    refine le_trans (totalDegree_mul _ _) ?_
    rw [totalDegree_C, zero_add]
    refine le_trans (totalDegree_finset_prod _ _) ?_
    unfold Finsupp.sum
    apply Finset.sum_le_sum
    intro i _
    rw [map_pow]
    exact le_trans (totalDegree_pow _ _) (by simpa using Nat.mul_le_mul_left (μ i) (hX i))
  conv_lhs => rw [as_sum f, map_sum]
  refine le_trans (totalDegree_finset_sum _ _) ?_
  apply Finset.sup_le
  intro μ hμ
  exact le_trans (hm μ _) (le_totalDegree hμ)

/-- **NS simulation.** -/
theorem map_NSspan {Γ : Set (MvPolynomial σ K)} {Δ : Set (MvPolynomial τ K)}
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (hX : ∀ i, (φ (X i)).totalDegree ≤ 1)
    (hΓ : ∀ f ∈ Γ, φ f ∈ NSspan Δ f.totalDegree) {d : ℕ} {g : MvPolynomial σ K}
    (hg : g ∈ NSspan Γ d) : φ g ∈ NSspan Δ d := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f, hf, hdeg, rfl⟩ := hx
    rw [map_mul]
    have h1 := mul_mem_NSspan_of (hΓ f hf)
      (le_trans (totalDegree_map_le φ hX (monomial m 1)) (totalDegree_monomial_one_le m))
    exact NSspan_mono' (by omega) h1
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem nsRefutes_of_hom {Γ : Set (MvPolynomial σ K)} {Δ : Set (MvPolynomial τ K)}
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (hX : ∀ i, (φ (X i)).totalDegree ≤ 1)
    (hΓ : ∀ f ∈ Γ, φ f ∈ NSspan Δ f.totalDegree) {d : ℕ} (h : NSRefutes Γ d) :
    NSRefutes Δ d := by
  rw [nsRefutes_iff_one_mem_NSspan] at h ⊢
  have := map_NSspan φ hX hΓ h
  rwa [map_one] at this

theorem nsDegree_le_of_hom {Γ : Set (MvPolynomial σ K)} {Δ : Set (MvPolynomial τ K)}
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (hX : ∀ i, (φ (X i)).totalDegree ≤ 1)
    (hΓ : ∀ f ∈ Γ, φ f ∈ NSspan Δ f.totalDegree) : nsDegree Δ ≤ nsDegree Γ := by
  induction h : nsDegree Γ using ENat.recTopCoe with
  | top => exact le_top
  | coe d =>
    rw [nsDegree_le_iff]
    exact nsRefutes_of_hom φ hX hΓ ((nsDegree_le_iff Γ d).mp (le_of_eq h))

/-- Axioms that map to axioms (or to `0`) lie in the span at their degree. -/
theorem mem_NSspan_of_image {Δ : Set (MvPolynomial τ K)} {g : MvPolynomial τ K} {e : ℕ}
    (hg : g ∈ Δ ∨ g = 0) (hdeg : g.totalDegree ≤ e) : g ∈ NSspan Δ e := by
  rcases hg with hg | rfl
  · exact NSspan_mono' hdeg (mem_NSspan_of_mem hg)
  · exact Submodule.zero_mem _

/-- **Soundness.** A system with a common root has no NS refutation. -/
theorem not_nsRefutes_of_root {Γ : Set (MvPolynomial σ K)} (x : σ → K)
    (hx : ∀ f ∈ Γ, eval x f = 0) (d : ℕ) : ¬ NSRefutes Γ d := by
  rintro ⟨s, a, hs, -, hsum⟩
  have h := congrArg (eval x) hsum
  rw [map_sum, map_one] at h
  rw [Finset.sum_eq_zero (fun f hf => by rw [map_mul, hx f (hs f hf), mul_zero])] at h
  exact zero_ne_one h

theorem nsDegree_eq_top_of_root {Γ : Set (MvPolynomial σ K)} (x : σ → K)
    (hx : ∀ f ∈ Γ, eval x f = 0) : nsDegree Γ = ⊤ := by
  classical
  unfold nsDegree
  rw [dif_neg]
  rintro ⟨d, hd⟩
  exact not_nsRefutes_of_root x hx d hd

end ClaudeUndec
