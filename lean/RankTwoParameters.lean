/- Non-vacuity and genuine genericity of the coefficients in the certificate. -/
import RankTwoIdentity
import DegreeProfilesReview.ShiftedElemAb
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.ComputeDegree

set_option autoImplicit false
namespace SelfContainedCycle006
variable {K : Type} [Field K] [CharP K 2]

def rootCoefficients (t : K) : Fin 2 → K := ![1, t]

theorem root_coefficients_generic (t : K) (ht : t ^ 2 + t + 1 = 0) :
    DegreeProfilesReview.Shifted.Generic 2 (rootCoefficients t) := by
  have hne := root_nonzero_and_ne_one t ht
  have hs : 1 + t ≠ 0 := fun h => hne.2 (CharTwo.add_eq_zero.mp h).symm
  have binary (x : ZMod 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp
  intro g hg
  rcases binary (g 0) with h0 | h0 <;> rcases binary (g 1) with h1 | h1
  · funext j
    fin_cases j <;> simp [h0, h1]
  all_goals simp [rootCoefficients, Fin.sum_univ_two, h0, h1, hne.1, hs] at hg

omit [CharP K 2] in
/-- Such a parameter exists over an explicit extension field of the prime field. -/
theorem parameter_exists [IsAlgClosed K] : ∃ t : K, t ^ 2 + t + 1 = 0 := by
  let p : Polynomial K := Polynomial.X ^ 2 + Polynomial.X + 1
  have hd : p.degree = 2 := by dsimp [p]; compute_degree <;> norm_num; decide
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p (by rw [hd]; decide)
  exact ⟨t, by simpa [Polynomial.IsRoot, p] using ht⟩

/-- The exact matrix identity and actual genericity are jointly inhabited. -/
theorem nonvacuity : ∃ t : AlgebraicClosure (ZMod 2),
    DegreeProfilesReview.Shifted.Generic 2 (rootCoefficients t) ∧
      (Z0 + t • Z1) * (A0 + t • A1) * (Z0 + t • Z1) =
        (Z0 + t • Z1 : Matrix Pair Pair (AlgebraicClosure (ZMod 2))) := by
  obtain ⟨t, ht⟩ := parameter_exists (K := AlgebraicClosure (ZMod 2))
  exact ⟨t, root_coefficients_generic t ht, rank_two_inner_inverse t ht⟩
end SelfContainedCycle006
