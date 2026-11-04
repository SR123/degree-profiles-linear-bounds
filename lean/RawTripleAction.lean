/- Cycle 010: faithful embedding of the actual injection module into all triple coordinates. -/
import RawTripleEncoding
import DegreeProfilesReview.PermFromTuples
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open CategoryTheory
namespace SelfContainedCycle010
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4

def rawAction (g : Sfin 11) (x : Raw) : Raw :=
  encodeTriple (fun i => ⟨g.1 (decodeTriple x i), Sfin_lt g.2 (decodeTriple x i).isLt⟩)

theorem rawAction_one (x : Raw) : rawAction 1 x = x := encode_decode x

theorem rawAction_mul (g h : Sfin 11) (x : Raw) :
    rawAction (g*h) x = rawAction g (rawAction h x) := by
  unfold rawAction
  simp only [decode_encode]
  rfl

theorem rawAction_inverse_iff (g : Sfin 11) (x y : Raw) :
    x = rawAction g⁻¹ y ↔ rawAction g x = y := by
  constructor
  · intro h
    rw [h, ← rawAction_mul, mul_inv_cancel, rawAction_one]
  · intro h
    rw [← h, ← rawAction_mul, inv_mul_cancel, rawAction_one]

variable {K : Type} [Field K]

def rawMapMatrix (f : Raw → Raw) : Matrix Raw Raw K := fun x y => if x=f y then 1 else 0

theorem rawMapMatrix_comp (f g : Raw → Raw) :
    rawMapMatrix (K := K) f * rawMapMatrix g = rawMapMatrix (f ∘ g) := by
  ext x y
  rw [Matrix.mul_apply]
  apply (Finset.sum_eq_single (g y) ?_ ?_).trans
  · simp [rawMapMatrix]
  · intro b _ hb
    simp [rawMapMatrix, hb]
  · simp

def rawMatrixHom : Sfin 11 →* Matrix Raw Raw K where
  toFun g := rawMapMatrix (rawAction g)
  map_one' := by ext x y; simp [rawMapMatrix, rawAction_one, Matrix.one_apply]
  map_mul' g h := by rw [rawMapMatrix_comp]; congr 1; funext x; exact rawAction_mul g h x

noncomputable def rawAlgebra : MonoidAlgebra K (Sfin 11) →ₐ[K] Matrix Raw Raw K :=
  MonoidAlgebra.lift K (Sfin 11) _ rawMatrixHom

def actualCode (x : (injTuples 3).Rk 11) : Raw := encodeTriple x.1

theorem actualCode_injective : Function.Injective actualCode := by
  intro x y h
  apply Subtype.ext
  exact rawEquiv.injective h

theorem actualCode_smul (g : Sfin 11) (x : (injTuples 3).Rk 11) :
    actualCode (g • x) = rawAction g (actualCode x) := by
  unfold actualCode rawAction
  simp only [decode_encode]
  congr 1
  funext i
  apply Fin.ext
  exact tupleVal_smul g x i

noncomputable def rawEmbed : (permRep K (injTuples 3) 11).V →ₗ[K] (Raw → K) :=
  (Finsupp.linearEquivFunOnFinite K K Raw).toLinearMap.comp
    (Finsupp.lmapDomain K K actualCode)

theorem rawEmbed_single (x : (injTuples 3).Rk 11) :
    rawEmbed (K := K) (Finsupp.single x 1) = Pi.single (actualCode x) 1 := by
  simp [rawEmbed, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.linearEquivFunOnFinite_single]

theorem rawEmbed_injective : Function.Injective (rawEmbed (K := K)) :=
  (Finsupp.linearEquivFunOnFinite K K Raw).injective.comp
    (Finsupp.mapDomain_injective actualCode_injective)

/-- Intertwining holds for every group-algebra element, not only the block generators. -/
theorem rawEmbed_action (a : MonoidAlgebra K (Sfin 11)) (v : (permRep K (injTuples 3) 11).V) :
    rawEmbed ((permRep K (injTuples 3) 11).ρ.asAlgebraHom a v) =
      Matrix.toLinAlgEquiv' (rawAlgebra a) (rawEmbed v) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    have hlin : (rawEmbed (K := K)).comp ((permRep K (injTuples 3) 11).ρ g) =
        (Matrix.toLinAlgEquiv' (rawMapMatrix (rawAction g))).comp rawEmbed := by
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      change rawEmbed (Representation.ofMulAction K (Sfin 11) ((injTuples 3).Rk 11)
        g (Finsupp.single x 1)) = Matrix.toLinAlgEquiv' (rawMapMatrix (rawAction g))
          (rawEmbed (Finsupp.single x 1))
      rw [Representation.ofMulAction_single, rawEmbed_single, rawEmbed_single,
        Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_single_one]
      funext y
      simp [rawMapMatrix, actualCode_smul, Pi.single_apply]
    simpa [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, rawAlgebra,
      MonoidAlgebra.lift_single, rawMatrixHom] using LinearMap.congr_fun hlin v
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | hsmul c a ha => simp only [map_smul, LinearMap.smul_apply, ha]

def rawProjection : Matrix Raw Raw K :=
  Matrix.diagonal (fun x => if good x.val then 1 else 0)

theorem rawProjection_embed (v : (permRep K (injTuples 3) 11).V) :
    Matrix.toLinAlgEquiv' (rawProjection (K := K)) (rawEmbed v) = rawEmbed v := by
  have hlin : (Matrix.toLinAlgEquiv' (rawProjection (K := K))).comp rawEmbed = rawEmbed := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change Matrix.toLinAlgEquiv' (rawProjection (K := K)) (rawEmbed (Finsupp.single x 1)) =
      rawEmbed (Finsupp.single x 1)
    rw [rawEmbed_single, Matrix.toLinAlgEquiv'_apply,
      Matrix.mulVec_single_one]
    have hg : good (actualCode x).val = true :=
      good_encode x.1 (fun _ _ h => x.2 (congrArg Fin.val h))
    funext y
    by_cases hy : y=actualCode x
    · subst y; simp [rawProjection, hg]
    · simp [rawProjection, hy]
  exact LinearMap.congr_fun hlin v

end SelfContainedCycle010
