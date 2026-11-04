/- Cycle 010: literal coordinate identities over all stated coefficient fields. -/
import SparseRectangular
import RankThreeRowCertificate
import RankThreeMatrixInverse

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SelfContainedCycle010
open SelfContainedCycle009
variable {K : Type} [Field K] [CharP K 2]

def EMatrix (t : K) : Matrix Raw ImageCoord K := rectSparse t Erow
def LMatrix (t : K) : Matrix ImageCoord Raw K := rectSparse t Lrow
def ZMatrix (t : K) : Matrix Raw Raw K := rectSparse t Zrow
def AMatrix (t : K) : Matrix Raw Raw K := rectSparse t Arow

theorem coordinate_reconstruction (t : K) (ht : t^2+t+1=0) :
    EMatrix t * LMatrix t * ZMatrix t = ZMatrix t := by
  unfold EMatrix LMatrix ZMatrix
  rw [Matrix.mul_assoc, rectSparse_eq_bits t ht Zrow,
    rectSparse_mul_rectBits t ht, rectSparse_mul_rectBits t ht]
  congr 1
  funext x
  exact reconstruction_bits x

theorem coordinate_compression (t : K) (ht : t^2+t+1=0) :
    LMatrix t * ZMatrix t * AMatrix t * EMatrix t = candidateMatrix t := by
  unfold LMatrix ZMatrix AMatrix EMatrix
  rw [Matrix.mul_assoc, Matrix.mul_assoc,
    rectSparse_eq_bits t ht Erow, rectSparse_mul_rectBits t ht,
    rectSparse_mul_rectBits t ht, rectSparse_mul_rectBits t ht]
  change rectBits t _ = rectSparse t sparseRows
  rw [rectSparse_eq_bits t ht]
  congr 1
  funext i
  exact compression_bits i

end SelfContainedCycle010
