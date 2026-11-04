/-
Claude, 25 Sep 2026.  Agreement of the NS and PC types, conditional on one explicit
representation-theoretic hypothesis.

(★) `ChainBound R 𝒰`: for each degree `t` there is `L` such that, at every universe size `n`,
    no strictly increasing chain `W 0 < W 1 < ⋯ < W (L+1)` of relabelling-invariant subspaces of
    the polynomials of degree `≤ t` exists.  Equivalently: the polynomials of degree `≤ t`,
    as an `R[S_n]`-module, have composition length at most `L`, uniformly in `n`.

This is the input of Krajíček's Theorem 5.5 (his Corollary 3.2, from Ajtai's work); it is NOT
proved here.  From it, for any field and any template:

* Krajíček's chain argument: a degree-`t` PC refutation gives a degree-`t+L` NS refutation, so
  `NS(n) ≤ PC(n) + L(PC(n))` at every size;
* hence the size-independent upper comparison of Stage 5's `types_transfer`;
* in characteristic two, with `charTwo_periodic`, the NS and PC profiles have the same type.

Two implications need no hypothesis at all: NS in T1 ⇒ PC in T1, and PC in T2 ⇒ NS in T2.
-/
import C017Rates
import DegreeProfilesReview.TypeTransfer

set_option autoImplicit false
open MvPolynomial

namespace ClaudeC017
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.PC DegreeProfilesReview.NS
open ClaudeWitnessTransfer

/-! ### The hypothesis (★) -/

/-- **(★)** Uniformly bounded chains of invariant subspaces of low-degree polynomials. -/
def ChainBound (R : Type) [Field R] (𝒰 : BasisSystem) : Prop :=
  ∀ t : ℕ, ∃ L : ℕ, ∀ n : ℕ, ∀ W : Fin (L + 2) → Submodule R (MvPolynomial (𝒰.Rk n) R),
    (∀ i, W i ≤ restrictTotalDegree (𝒰.Rk n) R t) →
    (∀ i (g : Sfin n) (f : MvPolynomial (𝒰.Rk n) R), f ∈ W i →
      rename (fun v => g • v) f ∈ W i) →
    ¬ StrictMono W

/-! ### NS spans: monotonicity and multiplication by a variable -/

section Spans
variable {R : Type} [Field R] {σ : Type*}

theorem NSspan_mono {Γ : Set (MvPolynomial σ R)} {d d' : ℕ} (h : d ≤ d') :
    NSspan Γ d ≤ NSspan Γ d' := by
  apply Submodule.span_mono
  rintro g ⟨m, f, hf, hdeg, rfl⟩
  exact ⟨m, f, hf, le_trans hdeg h, rfl⟩

theorem ns_mdeg_add_single (m : σ →₀ ℕ) (i : σ) :
    DegreeProfilesReview.NS.mdeg (m + Finsupp.single i 1) = DegreeProfilesReview.NS.mdeg m + 1 := by
  unfold DegreeProfilesReview.NS.mdeg
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

theorem ns_mdeg_mapDomain {τ : Type*} (e : σ → τ) (m : σ →₀ ℕ) :
    DegreeProfilesReview.NS.mdeg (Finsupp.mapDomain e m) = DegreeProfilesReview.NS.mdeg m := by
  unfold DegreeProfilesReview.NS.mdeg
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

theorem X_mul_mem_NSspan {Γ : Set (MvPolynomial σ R)} {d : ℕ} (i : σ) {f : MvPolynomial σ R}
    (hf : f ∈ NSspan Γ d) : X i * f ∈ NSspan Γ (d + 1) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f0, hf0, hdeg, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨m + Finsupp.single i 1, f0, hf0, ?_, ?_⟩
    · rw [ns_mdeg_add_single]; omega
    · rw [← mul_assoc, X, monomial_mul, one_mul, add_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

end Spans

/-! ### Krajíček's chain argument -/

section ChainArgument
variable {R : Type} [Field R] {σ : Type*}

/-- If the NS-reachable part of `P_{≤ t}` does not grow from `u` to `u+1`, it contains the
whole degree-`t` PC closure. -/
theorem Vinf_le_of_stable (Γ : Set (MvPolynomial σ R)) {t u : ℕ} (htu : t ≤ u)
    (hstab : NSspan Γ (u + 1) ⊓ restrictTotalDegree σ R t =
      NSspan Γ u ⊓ restrictTotalDegree σ R t) :
    Vinf Γ t ≤ NSspan Γ u ⊓ restrictTotalDegree σ R t := by
  apply iSup_le
  intro j
  induction j with
  | zero =>
    apply Submodule.span_le.mpr
    rintro f ⟨hf, hdeg⟩
    refine Submodule.mem_inf.mpr ⟨?_, (mem_restrictTotalDegree _ _ _).mpr hdeg⟩
    apply Submodule.subset_span
    refine ⟨0, f, hf, ?_, ?_⟩
    · have : DegreeProfilesReview.NS.mdeg (0 : σ →₀ ℕ) = 0 := by unfold DegreeProfilesReview.NS.mdeg; simp
      omega
    · simp
  | succ j ih =>
    apply sup_le ih
    apply Submodule.span_le.mpr
    rintro h ⟨i, f, hfS, rfl⟩
    obtain ⟨hfV, hflow⟩ := Submodule.mem_inf.mp hfS
    have hf := Submodule.mem_inf.mp (ih hfV)
    rw [SetLike.mem_coe, ← hstab]
    exact Submodule.mem_inf.mpr ⟨X_mul_mem_NSspan i hf.1,
      (mem_restrictTotalDegree _ _ _).mpr (totalDegree_X_mul_lowDeg i hflow)⟩

/-- **Krajíček's Theorem 5.5, the chain step.**  If the NS-reachable parts of `P_{≤ t}` at
degrees `t, t+1, …, t+L+1` do not form a strictly increasing chain, a degree-`t` PC refutation
gives a degree-`(t+L)` NS refutation. -/
theorem nsRefutes_of_refutes (Γ : Set (MvPolynomial σ R)) {t L : ℕ}
    (hchain : ¬ StrictMono
      (fun i : Fin (L + 2) => NSspan Γ (t + i) ⊓ restrictTotalDegree σ R t))
    (h : Refutes Γ t) : NSRefutes Γ (t + L) := by
  have hex : ∃ u, u ≤ L ∧ NSspan Γ (t + u + 1) ⊓ restrictTotalDegree σ R t =
      NSspan Γ (t + u) ⊓ restrictTotalDegree σ R t := by
    by_contra hno
    push_neg at hno
    apply hchain
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    simp only [Fin.coe_castSucc, Fin.val_succ]
    refine lt_of_le_of_ne (inf_le_inf_right _ (NSspan_mono (by omega))) ?_
    intro heq
    exact hno i (by omega) (by rw [← add_assoc] at heq; exact heq.symm)
  obtain ⟨u, hu, heq⟩ := hex
  have h1 : (1 : MvPolynomial σ R) ∈ Vinf Γ t := refutes_iff_one_mem_Vinf.mp h
  have h2 := Vinf_le_of_stable Γ (by omega : t ≤ t + u) heq h1
  exact (nsRefutes_iff_one_mem_NSspan.mpr (Submodule.mem_inf.mp h2).1).mono (by omega)

end ChainArgument

/-! ### Relabelling invariance of the NS spans of a template -/

section Invariance
variable {R : Type} [Field R] (T : Template R) {n : ℕ}

theorem rename_poly (g : Sfin n) (i : T.Ax.Rk n) :
    rename (fun v : T.Var.Rk n => g • v) (T.poly n i) = T.poly n (g • i) := by
  have hinj : Function.Injective (fun v : T.Var.Rk n => g • v) := MulAction.injective g
  ext m
  obtain ⟨m', rfl⟩ : ∃ m', Finsupp.mapDomain (fun v : T.Var.Rk n => g • v) m' = m := by
    refine ⟨Finsupp.mapDomain (fun v => g⁻¹ • v) m, ?_⟩
    rw [← Finsupp.mapDomain_comp]
    have : ((fun v : T.Var.Rk n => g • v) ∘ fun v => g⁻¹ • v) = id := by
      funext v; simp
    rw [this, Finsupp.mapDomain_id]
  rw [coeff_rename_mapDomain _ hinj, T.coeff_poly, T.coeff_poly, up_smul]
  have hmon : T.Var.monUp n (Finsupp.mapDomain (fun v : T.Var.Rk n => g • v) m') =
      T.Var.monSMul g.1 (T.Var.monUp n m') := by
    unfold BasisSystem.monUp BasisSystem.monSMul
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext v
    exact up_smul g v
  rw [hmon, T.coeff_inv]

theorem rename_mem_NSspan (g : Sfin n) {u : ℕ} {f : MvPolynomial (T.Var.Rk n) R}
    (hf : f ∈ NSspan (T.inst n) u) : rename (fun v => g • v) f ∈ NSspan (T.inst n) u := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f0, ⟨i, rfl⟩, hdeg, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨Finsupp.mapDomain (fun v => g • v) m, T.poly n (g • i), ⟨g • i, rfl⟩, ?_, ?_⟩
    · rw [ns_mdeg_mapDomain, ← rename_poly T g i]
      have := totalDegree_rename_le (fun v : T.Var.Rk n => g • v) (T.poly n i)
      omega
    · rw [map_mul, rename_monomial, rename_poly T g i]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end Invariance

/-! ### From (★) to the upper comparison, for every field and every template -/

section Comparison
variable {R : Type} [Field R] (T : Template R)

/-- **NS is at most PC plus a size-independent constant** (for each PC degree), under (★). -/
theorem ns_le_pc_add (hC : ChainBound R T.Var) :
    ∀ t : ℕ, ∃ L : ℕ, ∀ n, T.pcProfile n ≤ (t : ℕ∞) → T.nsProfile n ≤ ((t + L : ℕ) : ℕ∞) := by
  intro t
  obtain ⟨L, hL⟩ := hC t
  refine ⟨L, fun n hn => ?_⟩
  have hchain := hL n (fun i : Fin (L + 2) =>
      NSspan (T.inst n) (t + i) ⊓ restrictTotalDegree (T.Var.Rk n) R t)
    (fun _ => inf_le_right) (by
      intro i g f hf
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hf
      refine Submodule.mem_inf.mpr ⟨rename_mem_NSspan T g h1, ?_⟩
      rw [mem_restrictTotalDegree] at h2 ⊢
      exact le_trans (totalDegree_rename_le _ f) h2)
  have hpc : Refutes (T.inst n) t := (pcDegree_le_iff _ _).mp hn
  exact (nsDegree_le_iff _ _).mpr (nsRefutes_of_refutes (T.inst n) hchain hpc)

/-- The size-independent upper comparison required by Stage 5's `types_transfer`. -/
theorem upperComparison_of_chainBound (hC : ChainBound R T.Var) :
    ∃ F : ℕ → ℕ, Monotone F ∧ UpperComparison F T.pcProfile T.nsProfile := by
  choose L hL using ns_le_pc_add T hC
  refine ⟨fun x => x + ∑ s ∈ Finset.range (x + 1), L s, ?_, ?_⟩
  · intro x y hxy
    have : ∑ s ∈ Finset.range (x + 1), L s ≤ ∑ s ∈ Finset.range (y + 1), L s :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    simp only
    omega
  · intro n x hx
    refine le_trans (hL x n (le_of_eq hx)) ?_
    have : L x ≤ ∑ s ∈ Finset.range (x + 1), L s :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    exact_mod_cast (by omega : x + L x ≤ x + ∑ s ∈ Finset.range (x + 1), L s)

/-- No hypothesis needed: a bounded NS profile has a bounded PC profile. -/
theorem ns_T1_pc_T1 (h : IsT1 T.nsProfile) : IsT1 T.pcProfile := by
  obtain ⟨B, M, hBM⟩ := h
  exact ⟨B, M, fun n hn => le_trans (T.pcProfile_le_nsProfile n) (hBM n hn)⟩

end Comparison

/-! ### Characteristic two: the common type -/

section CharTwo
variable {R : Type} [Field R] [CharP R 2] (T : Template R)

/-- No hypothesis needed: if no finite PC value recurs, no finite NS value recurs. -/
theorem charTwo_pc_T2_ns_T2
    (h2 : IsT2 T.pcProfile (wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2))) :
    IsT2 T.nsProfile (wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2)) := by
  unfold IsT2 at h2 ⊢
  ext d
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨n, hn, hnd⟩
  have hle : T.pcProfile n ≤ (d : ℕ∞) := hnd ▸ T.pcProfile_le_nsProfile n
  obtain ⟨x, hx, hxd⟩ := enat_exists_of_le_coe hle
  have hmem := mem_E_of_le (charTwo_periodic T).1 hn hx hxd
  rw [h2] at hmem
  exact hmem

/-- **Agreement of types (characteristic two), under (★).** -/
theorem charTwo_types_agree (hC : ChainBound R T.Var) :
    let N := wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2)
    (IsT1 T.pcProfile ↔ IsT1 T.nsProfile) ∧ (IsT2 T.pcProfile N ↔ IsT2 T.nsProfile N) ∧
    (IsT3 T.pcProfile N ↔ IsT3 T.nsProfile N) ∧ (IsT4 T.pcProfile N ↔ IsT4 T.nsProfile N) := by
  obtain ⟨F, hF, hub⟩ := upperComparison_of_chainBound T hC
  exact types_transfer (charTwo_periodic T).1 (charTwo_periodic T).2 hF
    T.pcProfile_le_nsProfile hub

/-- **The common type (characteristic two), under (★).**  Exactly one of T1–T4 holds for the
PC profile, and the same one holds for the NS profile. -/
theorem charTwo_common_type (hC : ChainBound R T.Var) :
    let N := wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2)
    (IsT1 T.pcProfile ∧ IsT1 T.nsProfile) ∨ (IsT2 T.pcProfile N ∧ IsT2 T.nsProfile N) ∨
    (IsT3 T.pcProfile N ∧ IsT3 T.nsProfile N) ∨ (IsT4 T.pcProfile N ∧ IsT4 T.nsProfile N) := by
  obtain ⟨e1, e2, e3, e4⟩ := charTwo_types_agree T hC
  rcases (charTwo_classification T).1 with h | h | h | h
  · exact Or.inl ⟨h.1, e1.mp h.1⟩
  · exact Or.inr (Or.inl ⟨h.2.1, e2.mp h.2.1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.2.2.1, e3.mp h.2.2.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h.2.2.2, e4.mp h.2.2.2⟩))

end CharTwo
end ClaudeC017
