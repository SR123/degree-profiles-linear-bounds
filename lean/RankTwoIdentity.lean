/- Interpret the finite parity certificate as a genuine matrix inner inverse. -/
import RankTwoCertificate

set_option autoImplicit false
namespace SelfContainedCycle006
/-- The finite witness uses genuine permutations, a necessary application premise. -/
theorem maps_are_permutations :
    ∀ s ∈ a0List ++ a1List ++ z0List ++ z1List, Function.Bijective s := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using certificate_bijective

variable {K : Type} [Field K]

theorem mapMatrix_comp (s t : Map7) :
    mapMatrix (K := K) s * mapMatrix t = mapMatrix (s ∘ t) := by
  ext x y
  rw [Matrix.mul_apply]
  apply (Finset.sum_eq_single (pairMap t y) ?_ ?_).trans
  · simp [mapMatrix, pairMap]
  · intro b _ hb
    simp [mapMatrix, hb]
  · simp

theorem listMatrix_post (s : Map7) (R : List Map7) :
    listMatrix (K := K) (R.map (fun t => s ∘ t)) = mapMatrix s * listMatrix R := by
  induction R with
  | nil => simp [listMatrix]
  | cons t R ih => simp [listMatrix, ih, mul_add, mapMatrix_comp]

theorem listMatrix_comp (L R : List Map7) :
    listMatrix (K := K) (compList L R) = listMatrix L * listMatrix R := by
  induction L with
  | nil => simp [compList, listMatrix]
  | cons s L ih =>
    simpa only [compList, List.flatMap_cons, listMatrix_append, listMatrix_post,
      listMatrix, add_mul] using congrArg (fun M => mapMatrix s * listMatrix R + M) ih

def Z0 : Matrix Pair Pair K := listMatrix z0List
def Z1 : Matrix Pair Pair K := listMatrix z1List
def A0 : Matrix Pair Pair K := listMatrix a0List
def A1 : Matrix Pair Pair K := listMatrix a1List

variable [CharP K 2]

theorem constant_identity :
    Z0 * A0 * Z0 + Z1 * A1 * Z0 + Z1 * A0 * Z1 + Z0 * A1 * Z1 + Z1 * A1 * Z1 =
      (Z0 : Matrix Pair Pair K) := by
  have h := even0_matrix_zero (K := K)
  simp only [even0, listMatrix_append, triple, listMatrix_comp] at h
  ext x y
  apply CharTwo.add_eq_zero.mp
  have he := congrArg (fun M : Matrix Pair Pair K => M x y) h
  simpa only [Z0, Z1, A0, A1, Matrix.add_apply, Matrix.zero_apply, add_assoc] using he

theorem linear_identity :
    Z1 * A0 * Z0 + Z0 * A1 * Z0 + Z0 * A0 * Z1 +
      Z1 * A1 * Z0 + Z1 * A0 * Z1 + Z0 * A1 * Z1 = (Z1 : Matrix Pair Pair K) := by
  have h := even1_matrix_zero (K := K)
  simp only [even1, listMatrix_append, triple, listMatrix_comp] at h
  ext x y
  apply CharTwo.add_eq_zero.mp
  have he := congrArg (fun M : Matrix Pair Pair K => M x y) h
  simpa only [Z0, Z1, A0, A1, Matrix.add_apply, Matrix.zero_apply, add_assoc] using he

omit [CharP K 2] in
theorem cubic_expand {R : Type} [Ring R] [Algebra K R]
    (t : K) (z0 z1 a0 a1 : R) :
    (z0 + t • z1) * (a0 + t • a1) * (z0 + t • z1) =
      z0 * a0 * z0 + t • (z1 * a0 * z0 + z0 * a1 * z0 + z0 * a0 * z1) +
      t ^ 2 • (z1 * a1 * z0 + z1 * a0 * z1 + z0 * a1 * z1) +
      t ^ 3 • (z1 * a1 * z1) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add,
    pow_succ, pow_zero, one_mul, mul_assoc]
  abel

/-- The 44-term certificate gives an inner inverse over any characteristic-two field
with t²+t+1=0, not merely over the search implementation's finite field. -/
theorem rank_two_inner_inverse (t : K) (ht : t ^ 2 + t + 1 = 0) :
    (Z0 + t • Z1) * (A0 + t • A1) * (Z0 + t • Z1) =
      (Z0 + t • Z1 : Matrix Pair Pair K) := by
  have h2 : t ^ 2 = t + 1 := by
    apply CharTwo.add_eq_zero.mp
    simpa only [add_assoc] using ht
  have h3 : t ^ 3 = 1 := by
    rw [pow_succ, h2, add_mul, one_mul, ← pow_two, h2]
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  rw [cubic_expand, h2, h3, add_smul, one_smul, one_smul]
  calc
    _ = (Z0 * A0 * Z0 + Z1 * A1 * Z0 + Z1 * A0 * Z1 + Z0 * A1 * Z1 + Z1 * A1 * Z1) +
        t • (Z1 * A0 * Z0 + Z0 * A1 * Z0 + Z0 * A0 * Z1 +
          Z1 * A1 * Z0 + Z1 * A0 * Z1 + Z0 * A1 * Z1) := by
      simp only [smul_add]
      abel
    _ = _ := by rw [constant_identity, linear_identity]

/-- The coefficient restriction is genuine and gives the required F2 independence. -/
theorem root_nonzero_and_ne_one (t : K) (ht : t ^ 2 + t + 1 = 0) : t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · intro h
    simp [h] at ht
  · intro h
    simp [h, CharTwo.add_self_eq_zero] at ht

end SelfContainedCycle006
