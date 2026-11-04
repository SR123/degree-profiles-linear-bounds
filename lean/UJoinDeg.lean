/-
Claude, 27 Sep 2026.  Undecidability, part J2: degrees of the guarded join.

For well-formed `A`, `B`, every field `K` and every `n ≥ 1`, with `∞` allowed:

* `nsDegree_join_ge_left/right`, `pcDegree_join_ge_left/right`:
  `max (d A) (d B) ≤ d (A ∨_* B)`, for total-degree NS and for ordinary (line-degree) PC.
  Substitute `z_t ↦ 1` (resp. `0`) and put the inactive block at its structural point (all
  relations false, every function constantly `0`), which satisfies its totality, collision and
  Boolean axioms.  Every axiom of the join goes to an axiom of the active block or to `0`; for PC
  this uses the line-by-line substitution theorem of the project (`refutes_substitution`),
  variables going to variables or constants.
* `nsDegree_join_le`, `pcDegree_join_le`: `d (A ∨_* B) ≤ max (d A) (d B) + 1`.  Fix the label
  `0`.  Lift a refutation of `A` by the selector `z_0` and one of `B` by `1 - z_0`, and add.
  For NS this is a span computation (`ns_guard`).  For PC every line `g` of the `A` proof becomes
  the line `z_0 g` (`derives_guard_lift`: linear steps stay linear, `X_i`-steps commute with the
  multiplier, so degree drops by cancellation are harmless and every lifted line has degree at
  most `d + 1`); the lifted inputs `z_0 f` are axioms of the join (clauses) or are derived from
  the axiom `f` of the join by one multiplication inside the degree budget (structural axioms;
  `totalDegree_mul_of_isDomain`).
* `join_no_model`: a model of the join of size `n ≥ 1` gives a model of `A` or of `B`.
-/
import UJoin
import GuardUpper
import ComponentCompletion

set_option autoImplicit false
set_option linter.unusedSimpArgs false
open MvPolynomial DegreeProfilesReview.Uniform DegreeProfilesReview.NS DegreeProfilesReview.PC

namespace ClaudeUndec

/-! ### General tools -/

section Tools
variable {σ τ K : Type} [Field K]

theorem aeval_C_comp (y : σ → K) (g : MvPolynomial σ K) :
    aeval (fun w => (C (y w) : MvPolynomial τ K)) g = C (eval y g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, eval_X, map_mul]

/-- **Guarded NS simulation.** -/
theorem ns_guard {Γ : Set (MvPolynomial σ K)} {Δ : Set (MvPolynomial τ K)}
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (hX : ∀ i, (φ (X i)).totalDegree ≤ 1)
    (c : MvPolynomial τ K) (k : ℕ) (hΓ : ∀ f ∈ Γ, c * φ f ∈ NSspan Δ (f.totalDegree + k))
    {d : ℕ} {g : MvPolynomial σ K} (hg : g ∈ NSspan Γ d) : c * φ g ∈ NSspan Δ (d + k) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f, hf, hdeg, rfl⟩ := hx
    rw [map_mul, mul_left_comm]
    have h1 := mul_mem_NSspan_of (hΓ f hf)
      (le_trans (totalDegree_map_le φ hX (monomial m 1)) (totalDegree_monomial_one_le m))
    exact NSspan_mono' (by omega) h1
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul, mul_smul_comm]; exact Submodule.smul_mem _ a hx

theorem pcDegree_le_of {Γ : Set (MvPolynomial σ K)} {Δ : Set (MvPolynomial τ K)}
    (h : ∀ d, Refutes Γ d → Refutes Δ d) : pcDegree Δ ≤ pcDegree Γ := by
  induction hd : pcDegree Γ using ENat.recTopCoe with
  | top => exact le_top
  | coe d =>
    rw [pcDegree_le_iff]
    exact h d ((pcDegree_le_iff Γ d).mp (le_of_eq hd))

theorem totalDegree_one_sub_X_le (i : σ) : ((1 : MvPolynomial σ K) - X i).totalDegree ≤ 1 :=
  le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_X_le' i))

theorem one_sub_X_ne_zero (i : σ) : (1 : MvPolynomial σ K) - X i ≠ 0 := by
  intro h
  have h1 : (X i : MvPolynomial σ K) = 1 := (sub_eq_zero.mp h).symm
  have := congrArg totalDegree h1
  rw [totalDegree_X, totalDegree_one] at this
  exact one_ne_zero this

/-- One multiplication inside the degree budget (the multiplier is a nonzero polynomial). -/
theorem derives_mul_ax {Δ : Set (MvPolynomial σ K)} {D : ℕ} {c g : MvPolynomial σ K}
    (hc : c ≠ 0) (hg : g ∈ Δ) (hd : (c * g).totalDegree ≤ D) : Derives Δ D (c * g) := by
  by_cases h0 : g = 0
  · rw [h0, mul_zero]; exact (derivable Δ D).zero_mem
  · rw [totalDegree_mul_of_isDomain hc h0] at hd
    exact SelfContainedCycle081.derives_mul
      (SelfContainedCycle080.derives_ax hg (by omega)) hd

end Tools

/-! ### Substitutions into the join -/

section Subst
variable (A B : Sentence) (K : Type) [Field K] (n : ℕ)

open Classical in
/-- Substitute `fa` for the variables of `A`, `fb` for those of `B` and `fz` for the selectors. -/
noncomputable def subst3 {τ : Type} (fa : (VarSys A).Rk n → MvPolynomial τ K)
    (fb : (VarSys B).Rk n → MvPolynomial τ K) (fz : Fin n → MvPolynomial τ K) :
    MvPolynomial ((VarSys (join A B)).Rk n) K →ₐ[K] MvPolynomial τ K :=
  aeval fun v => if h : ∃ u, ιA A B n u = v then fa (Classical.choose h)
    else if h' : ∃ w, ιB A B n w = v then fb (Classical.choose h')
    else if h'' : ∃ t, zv A B n t = v then fz (Classical.choose h'') else 0

variable {τ : Type} (fa : (VarSys A).Rk n → MvPolynomial τ K)
  (fb : (VarSys B).Rk n → MvPolynomial τ K) (fz : Fin n → MvPolynomial τ K)

theorem subst3_A (u : (VarSys A).Rk n) : subst3 A B K n fa fb fz (X (ιA A B n u)) = fa u := by
  classical
  have h : ∃ u', ιA A B n u' = ιA A B n u := ⟨u, rfl⟩
  simp only [subst3, aeval_X, dif_pos h]
  rw [ιA_injective A B n (Classical.choose_spec h)]

theorem subst3_B (w : (VarSys B).Rk n) : subst3 A B K n fa fb fz (X (ιB A B n w)) = fb w := by
  classical
  have h0 : ¬ ∃ u, ιA A B n u = ιB A B n w := fun ⟨u, hu⟩ => ιA_ne_ιB A B n u w hu
  have h : ∃ w', ιB A B n w' = ιB A B n w := ⟨w, rfl⟩
  simp only [subst3, aeval_X, dif_neg h0, dif_pos h]
  rw [ιB_injective A B n (Classical.choose_spec h)]

theorem subst3_Z (t : Fin n) : subst3 A B K n fa fb fz (X (zv A B n t)) = fz t := by
  classical
  have h0 : ¬ ∃ u, ιA A B n u = zv A B n t := fun ⟨u, hu⟩ => ιA_ne_zv A B n u t hu
  have h1 : ¬ ∃ w, ιB A B n w = zv A B n t := fun ⟨w, hw⟩ => ιB_ne_zv A B n w t hw
  have h : ∃ t', zv A B n t' = zv A B n t := ⟨t, rfl⟩
  simp only [subst3, aeval_X, dif_neg h0, dif_neg h1, dif_pos h]
  rw [zv_injective A B n (Classical.choose_spec h)]

theorem subst3_renameA (f : MvPolynomial ((VarSys A).Rk n) K) :
    subst3 A B K n fa fb fz (rename (ιA A B n) f) = aeval fa f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, subst3_A, map_mul, aeval_X]

theorem subst3_renameB (f : MvPolynomial ((VarSys B).Rk n) K) :
    subst3 A B K n fa fb fz (rename (ιB A B n) f) = aeval fb f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, subst3_B, map_mul, aeval_X]

/-- Variables go to variables or constants. -/
theorem subst3_X (hfa : ∀ u, (∃ c, fa u = C c) ∨ ∃ j, fa u = X j)
    (hfb : ∀ w, (∃ c, fb w = C c) ∨ ∃ j, fb w = X j)
    (hfz : ∀ t, (∃ c, fz t = C c) ∨ ∃ j, fz t = X j)
    (v : (VarSys (join A B)).Rk n) :
    (∃ c, subst3 A B K n fa fb fz (X v) = C c) ∨ ∃ j, subst3 A B K n fa fb fz (X v) = X j := by
  rcases var_cases A B n v with ⟨u, rfl⟩ | ⟨w, rfl⟩ | ⟨t, rfl⟩
  · rw [subst3_A]; exact hfa u
  · rw [subst3_B]; exact hfb w
  · rw [subst3_Z]; exact hfz t

end Subst

/-! ### Lower bounds -/

section Lower
variable (A B : Sentence) (K : Type) [Field K] (n : ℕ)

/-- `z ↦ 1`, `B` at its structural point. -/
noncomputable def substA : MvPolynomial ((VarSys (join A B)).Rk n) K →ₐ[K]
    MvPolynomial ((VarSys A).Rk n) K :=
  subst3 A B K n X (fun w => C (spt B K n w)) (fun _ => 1)

/-- `z ↦ 0`, `A` at its structural point. -/
noncomputable def substB : MvPolynomial ((VarSys (join A B)).Rk n) K →ₐ[K]
    MvPolynomial ((VarSys B).Rk n) K :=
  subst3 A B K n (fun u => C (spt A K n u)) X (fun _ => 0)

theorem substA_X (v : (VarSys (join A B)).Rk n) :
    (∃ c, substA A B K n (X v) = C c) ∨ ∃ j, substA A B K n (X v) = X j :=
  subst3_X A B K n _ _ _ (fun u => Or.inr ⟨u, rfl⟩) (fun w => Or.inl ⟨_, rfl⟩)
    (fun _ => Or.inl ⟨1, by simp⟩) v

theorem substB_X (v : (VarSys (join A B)).Rk n) :
    (∃ c, substB A B K n (X v) = C c) ∨ ∃ j, substB A B K n (X v) = X j :=
  subst3_X A B K n _ _ _ (fun u => Or.inl ⟨_, rfl⟩) (fun w => Or.inr ⟨w, rfl⟩)
    (fun _ => Or.inl ⟨0, by simp⟩) v

theorem deg_le_one_of {σ τ : Type} (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (h : ∀ v, (∃ c, φ (X v) = C c) ∨ ∃ j, φ (X v) = X j) (v : σ) : (φ (X v)).totalDegree ≤ 1 := by
  rcases h v with ⟨c, hc⟩ | ⟨j, hj⟩
  · rw [hc, totalDegree_C]; omega
  · rw [hj]; exact totalDegree_X_le' j

/-- Every axiom of the join goes to an axiom of `A` or to `0` under `substA`. -/
theorem substA_ax (hA : WF A) (hB : WF B) (hn : 0 < n) {g : MvPolynomial ((VarSys (join A B)).Rk n) K}
    (hg : g ∈ (template (join A B) K).inst n) :
    substA A B K n g = 0 ∨ substA A B K n g ∈ (template A K).inst n := by
  rcases join_cases A B K n hA hB hg with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨t, rfl⟩ |
    ⟨f, hf, t, rfl⟩ | ⟨f, hf, t, rfl⟩
  · right; rw [substA, subst3_renameA, aeval_X_left_apply]; exact struct_mem A K n hf
  · left; rw [substA, subst3_renameB, aeval_C_comp, struct_spt B K n hn hf, map_zero]
  · left; rw [substA, map_sub, map_pow, subst3_Z]; ring
  · right; rw [substA, map_mul, subst3_Z, subst3_renameA, aeval_X_left_apply, one_mul]; exact hf
  · left; rw [substA, map_mul, map_sub, map_one, subst3_Z, sub_self, zero_mul]

/-- Every axiom of the join goes to an axiom of `B` or to `0` under `substB`. -/
theorem substB_ax (hA : WF A) (hB : WF B) (hn : 0 < n) {g : MvPolynomial ((VarSys (join A B)).Rk n) K}
    (hg : g ∈ (template (join A B) K).inst n) :
    substB A B K n g = 0 ∨ substB A B K n g ∈ (template B K).inst n := by
  rcases join_cases A B K n hA hB hg with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨t, rfl⟩ |
    ⟨f, hf, t, rfl⟩ | ⟨f, hf, t, rfl⟩
  · left; rw [substB, subst3_renameA, aeval_C_comp, struct_spt A K n hn hf, map_zero]
  · right; rw [substB, subst3_renameB, aeval_X_left_apply]; exact struct_mem B K n hf
  · left; rw [substB, map_sub, map_pow, subst3_Z]; ring
  · left; rw [substB, map_mul, subst3_Z, zero_mul]
  · right; rw [substB, map_mul, map_sub, map_one, subst3_Z, sub_zero, one_mul,
      subst3_renameB, aeval_X_left_apply]; exact hf

theorem nsDegree_join_ge_left (hA : WF A) (hB : WF B) (hn : 0 < n) :
    nsDegree ((template A K).inst n) ≤ nsDegree ((template (join A B) K).inst n) :=
  nsDegree_le_of_hom (substA A B K n) (deg_le_one_of K _ (substA_X A B K n))
    (fun _ hg => mem_NSspan_of_image ((substA_ax A B K n hA hB hn hg).symm)
      (totalDegree_map_le _ (deg_le_one_of K _ (substA_X A B K n)) _))

theorem nsDegree_join_ge_right (hA : WF A) (hB : WF B) (hn : 0 < n) :
    nsDegree ((template B K).inst n) ≤ nsDegree ((template (join A B) K).inst n) :=
  nsDegree_le_of_hom (substB A B K n) (deg_le_one_of K _ (substB_X A B K n))
    (fun _ hg => mem_NSspan_of_image ((substB_ax A B K n hA hB hn hg).symm)
      (totalDegree_map_le _ (deg_le_one_of K _ (substB_X A B K n)) _))

theorem pcDegree_join_ge_left (hA : WF A) (hB : WF B) (hn : 0 < n) :
    pcDegree ((template A K).inst n) ≤ pcDegree ((template (join A B) K).inst n) :=
  pcDegree_le_of fun _ h => SelfContainedCycle072.refutes_substitution (substA A B K n)
    (substA_X A B K n) (fun _ hg => substA_ax A B K n hA hB hn hg) h

theorem pcDegree_join_ge_right (hA : WF A) (hB : WF B) (hn : 0 < n) :
    pcDegree ((template B K).inst n) ≤ pcDegree ((template (join A B) K).inst n) :=
  pcDegree_le_of fun _ h => SelfContainedCycle072.refutes_substitution (substB A B K n)
    (substB_X A B K n) (fun _ hg => substB_ax A B K n hA hB hn hg) h

/-- **Lower bound** (NS): `max (d A) (d B) ≤ d (A ∨_* B)` at every `n ≥ 1`. -/
theorem nsDegree_join_ge (hA : WF A) (hB : WF B) (hn : 0 < n) :
    max (nsDegree ((template A K).inst n)) (nsDegree ((template B K).inst n)) ≤
      nsDegree ((template (join A B) K).inst n) :=
  max_le (nsDegree_join_ge_left A B K n hA hB hn) (nsDegree_join_ge_right A B K n hA hB hn)

/-- **Lower bound** (ordinary PC): `max (d A) (d B) ≤ d (A ∨_* B)` at every `n ≥ 1`. -/
theorem pcDegree_join_ge (hA : WF A) (hB : WF B) (hn : 0 < n) :
    max (pcDegree ((template A K).inst n)) (pcDegree ((template B K).inst n)) ≤
      pcDegree ((template (join A B) K).inst n) :=
  max_le (pcDegree_join_ge_left A B K n hA hB hn) (pcDegree_join_ge_right A B K n hA hB hn)

end Lower

/-! ### Upper bounds -/

section Upper
variable (A B : Sentence) (K : Type) [Field K] (n : ℕ)

theorem rename_deg_one {σ τ : Type} (e : σ → τ) (v : σ) :
    (rename e (X v : MvPolynomial σ K)).totalDegree ≤ 1 := by
  rw [rename_X]; exact totalDegree_X_le' _

/-- NS: a refutation of `A` of degree `d`, lifted by `z_t`. -/
theorem ns_lift_A (hA : WF A) (t : Fin n) {d : ℕ} (h : NSRefutes ((template A K).inst n) d) :
    X (zv A B n t) ∈ NSspan ((template (join A B) K).inst n) (d + 1) := by
  rw [nsRefutes_iff_one_mem_NSspan] at h
  have := ns_guard (rename (ιA A B n)) (rename_deg_one K _) (X (zv A B n t)) 1 (fun f hf => by
    rcases instA A B K n hA hf with h1 | h1
    · exact NSspan_mono' (by have := totalDegree_rename_le (ιA A B n) f; omega)
        (mul_mem_NSspan_of (mem_NSspan_of_mem h1) (totalDegree_X_le' (zv A B n t)))
    · refine mem_NSspan_of_image (Or.inl (h1 t)) ?_
      refine le_trans (totalDegree_mul _ _) ?_
      have := totalDegree_rename_le (ιA A B n) f
      have := totalDegree_X_le' (K := K) (zv A B n t)
      omega) h
  rwa [map_one, mul_one] at this

/-- NS: a refutation of `B` of degree `d`, lifted by `1 - z_t`. -/
theorem ns_lift_B (hB : WF B) (t : Fin n) {d : ℕ} (h : NSRefutes ((template B K).inst n) d) :
    1 - X (zv A B n t) ∈ NSspan ((template (join A B) K).inst n) (d + 1) := by
  rw [nsRefutes_iff_one_mem_NSspan] at h
  have := ns_guard (rename (ιB A B n)) (rename_deg_one K _) (1 - X (zv A B n t)) 1 (fun f hf => by
    rcases instB A B K n hB hf with h1 | h1
    · exact NSspan_mono' (by have := totalDegree_rename_le (ιB A B n) f; omega)
        (mul_mem_NSspan_of (mem_NSspan_of_mem h1) (totalDegree_one_sub_X_le (zv A B n t)))
    · refine mem_NSspan_of_image (Or.inl (h1 t)) ?_
      refine le_trans (totalDegree_mul _ _) ?_
      have := totalDegree_rename_le (ιB A B n) f
      have := totalDegree_one_sub_X_le (K := K) (zv A B n t)
      omega) h
  rwa [map_one, mul_one] at this

/-- **Upper bound** (NS): `d (A ∨_* B) ≤ max (d A) (d B) + 1` at every `n ≥ 1`. -/
theorem nsDegree_join_le (hA : WF A) (hB : WF B) (hn : 0 < n) :
    nsDegree ((template (join A B) K).inst n) ≤
      max (nsDegree ((template A K).inst n)) (nsDegree ((template B K).inst n)) + 1 := by
  induction ha : nsDegree ((template A K).inst n) using ENat.recTopCoe with
  | top => simp
  | coe a =>
    induction hb : nsDegree ((template B K).inst n) using ENat.recTopCoe with
    | top => simp
    | coe b =>
      have hA' := (nsDegree_le_iff _ a).mp (le_of_eq ha)
      have hB' := (nsDegree_le_iff _ b).mp (le_of_eq hb)
      have e : ((max (a : ℕ∞) b) + 1 : ℕ∞) = ((max a b + 1 : ℕ) : ℕ∞) := by
        push_cast; rfl
      rw [e, nsDegree_le_iff, nsRefutes_iff_one_mem_NSspan]
      have h1 := NSspan_mono' (show a + 1 ≤ max a b + 1 by omega)
        (ns_lift_A A B K n hA ⟨0, hn⟩ hA')
      have h2 := NSspan_mono' (show b + 1 ≤ max a b + 1 by omega)
        (ns_lift_B A B K n hB ⟨0, hn⟩ hB')
      have := add_mem h1 h2
      rwa [add_sub_cancel] at this

/-- PC: a refutation of `A` of degree `d`, lifted line by line by `z_t`. -/
theorem pc_lift_A (hA : WF A) (t : Fin n) {d : ℕ} (h : Refutes ((template A K).inst n) d) :
    Derives ((template (join A B) K).inst n) (d + 1) (X (zv A B n t)) := by
  -- rename the proof into the variables of the join
  have h1 : Derives (rename (ιA A B n) '' (template A K).inst n) d 1 := by
    have := SelfContainedCycle075.derives_substitution (rename (ιA A B n))
      (Δ := rename (ιA A B n) '' (template A K).inst n)
      (fun v => Or.inr ⟨ιA A B n v, rename_X _ _⟩)
      (fun f hf => Or.inr ⟨f, hf, rfl⟩) h
    rwa [map_one] at this
  -- multiply every line by `z_t`
  have h2 := SelfContainedCycle081.derives_guard_lift (X (zv A B n t))
    (Δ := (fun f => X (zv A B n t) * f) '' (rename (ιA A B n) '' (template A K).inst n))
    (fun f hf => ⟨f, hf, rfl⟩) h1
  rw [totalDegree_X, mul_one] at h2
  -- the lifted inputs are derivable in the join
  refine SelfContainedCycle081.derives_of_derived_inputs (href := h2) ?_
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ hdeg
  rcases instA A B K n hA hf with h3 | h3
  · exact derives_mul_ax (X_ne_zero _) h3 hdeg
  · exact SelfContainedCycle080.derives_ax (h3 t) hdeg

/-- PC: a refutation of `B` of degree `d`, lifted line by line by `1 - z_t`. -/
theorem pc_lift_B (hB : WF B) (t : Fin n) {d : ℕ} (h : Refutes ((template B K).inst n) d) :
    Derives ((template (join A B) K).inst n) (d + 1) (1 - X (zv A B n t)) := by
  have h1 : Derives (rename (ιB A B n) '' (template B K).inst n) d 1 := by
    have := SelfContainedCycle075.derives_substitution (rename (ιB A B n))
      (Δ := rename (ιB A B n) '' (template B K).inst n)
      (fun v => Or.inr ⟨ιB A B n v, rename_X _ _⟩)
      (fun f hf => Or.inr ⟨f, hf, rfl⟩) h
    rwa [map_one] at this
  have h2 := SelfContainedCycle081.derives_guard_lift (1 - X (zv A B n t))
    (Δ := (fun f => (1 - X (zv A B n t)) * f) '' (rename (ιB A B n) '' (template B K).inst n))
    (fun f hf => ⟨f, hf, rfl⟩) h1
  rw [mul_one] at h2
  have h2' := Derives.mono (show d + (1 - X (zv A B n t) : MvPolynomial _ K).totalDegree ≤ d + 1 by
    have := totalDegree_one_sub_X_le (K := K) (zv A B n t); omega) h2
  refine SelfContainedCycle081.derives_of_derived_inputs (href := h2') ?_
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ hdeg
  rcases instB A B K n hB hf with h3 | h3
  · exact derives_mul_ax (one_sub_X_ne_zero _) h3 hdeg
  · exact SelfContainedCycle080.derives_ax (h3 t) hdeg

/-- **Upper bound** (ordinary PC): `d (A ∨_* B) ≤ max (d A) (d B) + 1` at every `n ≥ 1`. -/
theorem pcDegree_join_le (hA : WF A) (hB : WF B) (hn : 0 < n) :
    pcDegree ((template (join A B) K).inst n) ≤
      max (pcDegree ((template A K).inst n)) (pcDegree ((template B K).inst n)) + 1 := by
  induction ha : pcDegree ((template A K).inst n) using ENat.recTopCoe with
  | top => simp
  | coe a =>
    induction hb : pcDegree ((template B K).inst n) using ENat.recTopCoe with
    | top => simp
    | coe b =>
      have hA' := (pcDegree_le_iff _ a).mp (le_of_eq ha)
      have hB' := (pcDegree_le_iff _ b).mp (le_of_eq hb)
      have e : ((max (a : ℕ∞) b) + 1 : ℕ∞) = ((max a b + 1 : ℕ) : ℕ∞) := by
        push_cast; rfl
      rw [e, pcDegree_le_iff]
      have h1 := Derives.mono (show a + 1 ≤ max a b + 1 by omega)
        (pc_lift_A A B K n hA ⟨0, hn⟩ hA')
      have h2 := Derives.mono (show b + 1 ≤ max a b + 1 by omega)
        (pc_lift_B A B K n hB ⟨0, hn⟩ hB')
      have := SelfContainedCycle080.derives_add h1 h2
      rwa [add_sub_cancel] at this

end Upper

/-! ### Models -/

section Models
variable (A B : Sentence) (n : ℕ)

/-- A model of the join (size `n ≥ 1`) gives a model of `A` or of `B`. -/
theorem join_no_model (hA : WF A) (hB : WF B) (hn : 0 < n) (h : HasModelOfSize (join A B) n) :
    HasModelOfSize A n ∨ HasModelOfSize B n := by
  obtain ⟨x, hx⟩ := (hasRoot_iff (join A B) ℚ hn).mpr h
  have hz := hx _ (bool_mem (join A B) ℚ (zv A B n ⟨0, hn⟩))
  rw [map_sub, map_pow, eval_X] at hz
  have hz' : x (zv A B n ⟨0, hn⟩) = 0 ∨ x (zv A B n ⟨0, hn⟩) = 1 := by
    have : x (zv A B n ⟨0, hn⟩) * (x (zv A B n ⟨0, hn⟩) - 1) = 0 := by rw [← hz]; ring
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  rcases hz' with h0 | h1
  · right
    refine (hasRoot_iff B ℚ hn).mp ⟨x ∘ ιB A B n, fun f hf => ?_⟩
    rcases instB A B ℚ n hB hf with h3 | h3
    · rw [← eval_rename]; exact hx _ h3
    · have := hx _ (h3 ⟨0, hn⟩)
      rwa [map_mul, map_sub, map_one, eval_X, h0, sub_zero, one_mul, eval_rename] at this
  · left
    refine (hasRoot_iff A ℚ hn).mp ⟨x ∘ ιA A B n, fun f hf => ?_⟩
    rcases instA A B ℚ n hA hf with h3 | h3
    · rw [← eval_rename]; exact hx _ h3
    · have := hx _ (h3 ⟨0, hn⟩)
      rwa [map_mul, eval_X, h1, one_mul, eval_rename] at this

/-- The join is well formed. -/
theorem join_WF (hA : WF A) (hB : WF B) : WF (join A B) := by
  intro c hc l hl
  rw [join_clauses, List.mem_append] at hc
  rcases hc with hc | hc
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨by rw [join_rels_length]; omega, by rw [getD_join_rels_z]; rfl⟩
    · have h := hA c0 hc0 l hl
      obtain ⟨s, a⟩ := l
      rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
      · obtain ⟨h1, h2⟩ := h
        exact ⟨by rw [join_rels_length]; omega, by rw [getD_join_rels_left A B h1]; exact h2⟩
      · obtain ⟨h1, h2⟩ := h
        exact ⟨by rw [join_funs_length]; omega, by rw [getD_join_funs_left A B h1]; exact h2⟩
      · trivial
  · obtain ⟨c1, hc1, rfl⟩ := List.mem_map.mp hc
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc1
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨by rw [join_rels_length]; omega, by rw [getD_join_rels_z]; rfl⟩
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      have h := hB c0 hc0 l' hl'
      obtain ⟨s, a⟩ := l'
      rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
      · obtain ⟨h1, h2⟩ := h
        show AtomWF (join A B) (Sum.inl (A.rels.length + R, args))
        exact ⟨by rw [join_rels_length]; omega, by rw [getD_join_rels_right A B h1]; exact h2⟩
      · obtain ⟨h1, h2⟩ := h
        show AtomWF (join A B) (Sum.inr (Sum.inl ((A.funs.length + f, args), out)))
        exact ⟨by rw [join_funs_length]; omega, by rw [getD_join_funs_right A B f]; exact h2⟩
      · trivial

end Models

end ClaudeUndec
