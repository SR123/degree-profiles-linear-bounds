/- Cycle 010: sound sparse-row composition for rectangular matrices. -/
import BitPairMatrix

set_option autoImplicit false
namespace SelfContainedCycle010
open SelfContainedCycle009
variable {K : Type} [Field K] [CharP K 2]

def rectSparse {m n : ℕ} (t : K) (rows : Fin m → List (Fin n × Fin 4)) :
    Matrix (Fin m) (Fin n) K :=
  fun i j => rowValue t (rows i) (fun k => if k=j then 1 else 0)

def rectBits {m n : ℕ} (t : K) (rows : Fin m → Bits) : Matrix (Fin m) (Fin n) K :=
  fun i j => bitsValue t (rows i) j.val

theorem rectSparse_eq_bits {m n : ℕ} (t : K) (ht : t^2+t+1=0)
    (rows : Fin m → List (Fin n × Fin 4)) :
    rectSparse t rows = rectBits t (fun i => combineBits (rows i) (fun j => (1 <<< j.val,0))) := by
  ext i j
  simp only [rectSparse, rectBits, combineBits_sound t ht, Nat.shiftLeft_eq, Nat.one_mul, bitsValue_unit, Fin.val_inj]

theorem rectSparse_mul_rectBits {l m n : ℕ} (t : K) (ht : t^2+t+1=0)
    (rows : Fin l → List (Fin m × Fin 4)) (v : Fin m → Bits) :
    rectSparse t rows * (rectBits t v : Matrix (Fin m) (Fin n) K) =
      rectBits t (fun i => combineBits (rows i) v) := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑ k, rowValue t (rows i) (fun a => if a=k then 1 else 0) *
    bitsValue t (v k) j.val) = bitsValue t (combineBits (rows i) v) j.val
  rw [rowValue_mul, combineBits_sound t ht]

end SelfContainedCycle010
