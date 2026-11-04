/-
Uniform consequences, Claude return 001 (5 October 2026).  Part 4: non-vacuity.

A NONCONSTANT stable target `G_n = x_0 + ⋯ + x_{n-1}` (coefficient rule "1 on every monomial of
degree one, 0 elsewhere"), in every field:

* with the unit axioms `Γ_n = {x_i : i < n}` both target profiles equal `1` for every `n ≥ 1`
  (type T1);
* with no axioms both target profiles equal `⊤` for every `n ≥ 1` (type T2, the value `∞`).

These are diagnostics, not evidence for the general theorem.
-/
import UCClassification
import DegreeProfilesReview.TemplateExample

set_option autoImplicit false

open MvPolynomial

namespace UniformConsequence.Example

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.Profiles
open UniformConsequence

variable (R : Type) [Field R]

open Classical in
/-- The template with the unit axioms `x_i`, one for each label. -/
noncomputable def unitAxioms : Template R where
  Var := points
  Ax := points
  k := 1
  s := 1
  D := 1
  n0 := 2
  hk := le_refl 1
  hn0 := by norm_num
  hn0' := le_refl 2
  var_bounded := points_bounded
  ax_bounded := points_bounded
  coeff := fun i m => if m = Finsupp.single i 1 then 1 else 0
  coeff_inv := fun g i m => by
    show (if points.monSMul g m = Finsupp.single (g • i) 1 then (1 : R) else 0) = _
    have : Finsupp.single (g • i) 1 = points.monSMul g (Finsupp.single i 1) :=
      (Finsupp.mapDomain_single).symm
    rw [this]
    exact if_congr (points.monSMul_injective g).eq_iff rfl rfl
  coeff_deg := fun i m h => by
    by_cases hm : m = Finsupp.single i 1
    · subst hm; rw [mdeg_single]
    · rw [if_neg hm] at h; exact absurd rfl h

/-- The template with no axioms (its index system is empty). -/
noncomputable def noAxioms : Template R where
  Var := points
  Ax := points.sub (fun _ => False) (fun _ _ => Iff.rfl)
  k := 1
  s := 1
  D := 0
  n0 := 1
  hk := le_refl 1
  hn0 := le_refl 1
  hn0' := le_refl 1
  var_bounded := points_bounded
  ax_bounded := sub_bounded points_bounded _ _
  coeff := fun _ _ => 0
  coeff_inv := fun _ _ _ => rfl
  coeff_deg := fun _ _ h => absurd rfl h

open Classical in
/-- The coefficient rule of `x_0 + ⋯ + x_{n-1}`: `1` on every monomial of degree one. -/
noncomputable def sumTarget (T : Template R) : Target T where
  DG := 1
  γ := fun m => if BasisSystem.mdeg m = 1 then 1 else 0
  γ_inv := fun g m => by
    show (if BasisSystem.mdeg (T.Var.monSMul g m) = 1 then (1 : R) else 0) = _
    rw [mdeg_monSMul]
  γ_deg := fun m h => by
    by_cases h1 : BasisSystem.mdeg m = 1
    · exact le_of_eq h1
    · rw [if_neg h1] at h; exact absurd rfl h

theorem unitAxioms_poly (t : ℕ) (i : (unitAxioms R).Ax.Rk t) :
    (unitAxioms R).poly t i = X i := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [Template.coeff_poly, coeff_X']
  show (if points.monUp t m = Finsupp.single (points.up t i) 1 then (1 : R) else 0) = _
  refine if_congr ?_ rfl rfl
  rw [← monUp_single, (points.monUp_injective t).eq_iff, eq_comm]

/-- The target polynomial is `∑ x_j` (for any template). -/
theorem sumTarget_poly (T : Template R) (t : ℕ) [Fintype (T.Var.Rk t)] :
    (sumTarget R T).poly t = ∑ j : T.Var.Rk t, X j := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [Target.coeff_poly, coeff_sum]
  show (if BasisSystem.mdeg (T.Var.monUp t m) = 1 then (1 : R) else 0) = _
  rw [mdeg_monUp]
  by_cases h1 : BasisSystem.mdeg m = 1
  · obtain ⟨j0, rfl⟩ := eq_single_of_mdeg_eq_one (α := T.Var.Rk t) h1
    rw [if_pos h1]
    have : ∀ j : T.Var.Rk t, coeff (Finsupp.single j0 1) (X j : MvPolynomial (T.Var.Rk t) R) =
        if j = j0 then 1 else 0 := by
      intro j
      rw [coeff_X']
      refine if_congr ?_ rfl rfl
      constructor
      · intro h
        exact (Finsupp.single_left_injective one_ne_zero) h
      · rintro rfl; rfl
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_ite_eq' Finset.univ j0]
    simp
  · rw [if_neg h1]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_X', if_neg]
    rintro rfl
    exact h1 (mdeg_single j 1)

/-- The stable degree of `∑ x_j` is one, for any template with the single-label variables. -/
theorem sumTarget_deg (T : Template R) (hk : T.k = 1) (hV : T.Var = points) :
    (sumTarget R T).deg = 1 := by
  have hnG : (sumTarget R T).nG ≤ 1 := by
    rw [Target.nG_eq]
    show max 1 (T.k * 1) ≤ 1
    rw [hk]
    norm_num
  rw [← (sumTarget R T).totalDegree_poly hnG]
  cases T with
  | mk Var Ax k s D n0 hk' hn0 hn0' vb ab coeff coeff_inv coeff_deg =>
    subst hV
    rw [@sumTarget_poly R _ _ 1 (Fin.fintype 1)]
    show (∑ j : Fin 1, (X j : MvPolynomial (Fin 1) R)).totalDegree = 1
    rw [Fin.sum_univ_one, totalDegree_X]

/-- **Finite nonconstant example.**  With the unit axioms, `x_0 + ⋯ + x_{n-1}` has PC and NS
target degree exactly `1` at every `n ≥ 1`. -/
theorem unitAxioms_profiles {n : ℕ} (hn : 1 ≤ n) :
    (sumTarget R (unitAxioms R)).pcProfile n = 1 ∧
    (sumTarget R (unitAxioms R)).nsProfile n = 1 := by
  set G := sumTarget R (unitAxioms R)
  have hdeg : G.deg = 1 := sumTarget_deg R _ rfl rfl
  have hnG : G.nG ≤ n := by
    rw [Target.nG_eq]
    show max 1 (1 * 1) ≤ n
    simpa using hn
  have hmem : G.poly n ∈ NSspan ((unitAxioms R).inst n) 1 := by
    rw [show G.poly n = ∑ j : Fin n, (X j : MvPolynomial (Fin n) R) from
      @sumTarget_poly R _ (unitAxioms R) n (Fin.fintype n)]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.subset_span
    refine ⟨0, X j, ⟨j, unitAxioms_poly R n j⟩, ?_, ?_⟩
    · rw [totalDegree_X]; simp [NS.mdeg]
    · exact (one_mul (X j)).symm
  have hns : G.nsProfile n ≤ ((1 : ℕ) : ℕ∞) := (G.nsProfile_le_iff n 1).mpr hmem
  have hlow := G.deg_le_pcProfile hnG
  rw [hdeg] at hlow
  have hpc := le_trans (G.pcProfile_le_nsProfile n) hns
  have hlow' := le_trans hlow (G.pcProfile_le_nsProfile n)
  exact ⟨le_antisymm (by exact_mod_cast hpc) (by exact_mod_cast hlow),
    le_antisymm (by exact_mod_cast hns) (by exact_mod_cast hlow')⟩

/-- With no axioms every line of an ordinary PC derivation is zero. -/
theorem isProof_empty_lines {σ : Type*} {l : List (MvPolynomial σ R)}
    (h : IsProof (∅ : Set (MvPolynomial σ R)) l) : ∀ g ∈ l, g = 0 := by
  induction h with
  | nil => intro g hg; simp at hg
  | ax _ hf _ => exact absurd hf (Set.notMem_empty _)
  | @lin l f _ hf ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · have hle : Submodule.span R {g | g ∈ l} ≤ ⊥ := Submodule.span_le.mpr (fun x hx => by
          rw [SetLike.mem_coe, Submodule.mem_bot]; exact ih x hx)
      exact (Submodule.mem_bot R).mp (hle hf)
    · exact ih g hg'
  | mulX i _ hg0 ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · rw [ih _ hg0, mul_zero]
    · exact ih g hg'

theorem noAxioms_inst (t : ℕ) : (noAxioms R).inst t = ∅ := by
  ext f
  simp only [Template.inst, Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨i, _⟩
  exact i.2

/-- **Infinite nonconstant example.**  With no axioms, `x_0 + ⋯ + x_{n-1}` is not derivable at
any `n ≥ 1`: both target profiles are `⊤`. -/
theorem noAxioms_profiles {n : ℕ} (hn : 1 ≤ n) :
    (sumTarget R (noAxioms R)).pcProfile n = ⊤ ∧
    (sumTarget R (noAxioms R)).nsProfile n = ⊤ := by
  set G := sumTarget R (noAxioms R)
  have hne : G.poly n ≠ 0 := by
    intro h0
    have hnG : G.nG ≤ n := by
      rw [Target.nG_eq]; show max 1 (1 * 1) ≤ n; simpa using hn
    have := G.totalDegree_poly hnG
    rw [h0, totalDegree_zero, sumTarget_deg R _ rfl rfl] at this
    exact absurd this (by norm_num)
  have hpc : G.pcProfile n = ⊤ := by
    unfold Target.pcProfile tpcDegree
    rw [dif_neg]
    rintro ⟨d, l, hl, -, hm⟩
    rw [noAxioms_inst] at hl
    exact hne (isProof_empty_lines R hl _ hm)
  refine ⟨hpc, ?_⟩
  have := G.pcProfile_le_nsProfile n
  rw [hpc] at this
  exact top_le_iff.mp this

/-- The two examples have different types: T1 with unit axioms, T2 (value `⊤`) without. -/
theorem example_types :
    IsT1 (sumTarget R (unitAxioms R)).pcProfile ∧
    IsT2 (sumTarget R (noAxioms R)).pcProfile
      (onset (noAxioms R).k (noAxioms R).s (sumTarget R (noAxioms R)).nstar) := by
  constructor
  · exact ⟨1, 1, fun n hn => le_of_eq ((unitAxioms_profiles R hn).1.trans (by norm_num))⟩
  · ext d
    simp only [E, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨n, hn, hval⟩
    have h1 : 1 ≤ n := le_trans (le_trans (sumTarget R (noAxioms R)).one_le_nstar
      (n0_le_onset _ _ _ d)) hn
    rw [(noAxioms_profiles R h1).1] at hval
    exact ENat.top_ne_coe d hval

end UniformConsequence.Example
