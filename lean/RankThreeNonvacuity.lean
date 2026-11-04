/- Cycle 009: the concrete matrix theorem has an inhabited coefficient scope. -/
import RankThreeMatrixInverse
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.ComputeDegree

set_option autoImplicit false
namespace SelfContainedCycle009

theorem parameter_nonvacuity : ∃ t : AlgebraicClosure (ZMod 2),
    t^2+t+1=0 ∧ candidateMatrix t * inverseMatrix t = 1 := by
  let P : Polynomial (AlgebraicClosure (ZMod 2)) := Polynomial.X^2+Polynomial.X+1
  have hd : P.degree = 2 := by dsimp [P]; compute_degree <;> norm_num; decide
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_root P (by rw [hd]; decide)
  have hr : t^2+t+1=0 := by simpa [Polynomial.IsRoot, P] using ht
  exact ⟨t,hr,candidate_right_inverse t hr⟩

end SelfContainedCycle009
