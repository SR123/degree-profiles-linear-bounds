/- Cycle 009: the finite matrix is invertible over every stated coefficient field.
Identification with the actual injection-module action is a separate obligation. -/
import RankThreeInverseData
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
namespace SelfContainedCycle009

variable {K : Type} [Field K] [CharP K 2]

def candidateMatrix (t : K) : Matrix Coord Coord K := sparseMatrix t sparseRows
def inverseMatrix (t : K) : Matrix Coord Coord K := bitsMatrix t inverseRows

theorem candidate_right_inverse (t : K) (ht : t^2+t+1=0) :
    candidateMatrix t * inverseMatrix t = 1 :=
  inverse_certificate_sound t ht sparseRows inverseRows inverse_bits

theorem candidate_left_inverse (t : K) (ht : t^2+t+1=0) :
    inverseMatrix t * candidateMatrix t = 1 :=
  Matrix.mul_eq_one_comm.mp (candidate_right_inverse t ht)

theorem candidate_injective (t : K) (ht : t^2+t+1=0) :
    Function.Injective (Matrix.toLinAlgEquiv' (candidateMatrix t)) := by
  intro x y h
  have hi := congrArg (fun M : Matrix Coord Coord K => Matrix.toLinAlgEquiv' M)
    (candidate_left_inverse t ht)
  simp only [map_mul, map_one] at hi
  have he := congrArg (fun v => Matrix.toLinAlgEquiv' (inverseMatrix t) v) h
  change (Matrix.toLinAlgEquiv' (inverseMatrix t) *
    Matrix.toLinAlgEquiv' (candidateMatrix t)) x =
      (Matrix.toLinAlgEquiv' (inverseMatrix t) *
        Matrix.toLinAlgEquiv' (candidateMatrix t)) y at he
  simpa only [hi, Module.End.one_apply] using he

end SelfContainedCycle009
