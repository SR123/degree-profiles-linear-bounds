/- Cycle 010: identify the finite sparse rows with genuine group-algebra actions. -/
import RawTripleAction
import RankThreeCoordinateIdentities

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open CategoryTheory
namespace SelfContainedCycle010
open DegreeProfilesReview.SymRep
open SelfContainedCycle009

def rowLabelFn (k : Fin 5) : ℕ → ℕ :=
  if k=0 then (fun a => if a<4 then a ^^^ 1 else a) else
  if k=1 then (fun a => if a<4 then a ^^^ 2 else a) else
  if k=2 then inversePerm0 else if k=3 then inversePerm1 else inversePerm2

def rowFinMap (k : Fin 5) (i : Label) : Label := Fin.ofNat 11 (rowLabelFn k i.val)

theorem row_bounds : ∀ (k : Fin 5) (i : Label), rowLabelFn k i.val < 11 := by decide +kernel
theorem row_bijective : ∀ k : Fin 5, Function.Bijective (rowFinMap k) := by decide +kernel

noncomputable def rowPerm (k : Fin 5) : Sfin 11 :=
  ⟨Equiv.Perm.extendDomain (Equiv.ofBijective (rowFinMap k) (row_bijective k)) Fin.equivSubtype,
    fun j hj => Equiv.Perm.extendDomain_apply_not_subtype _ Fin.equivSubtype (by omega)⟩

theorem rowPerm_apply (k : Fin 5) (i : Label) : (rowPerm k).1 i = (rowFinMap k i).val :=
  Equiv.Perm.extendDomain_apply_image _ Fin.equivSubtype i

theorem rowFinMap_val (k : Fin 5) (i : Label) : (rowFinMap k i).val = rowLabelFn k i.val :=
  Nat.mod_eq_of_lt (row_bounds k i)

theorem row_rawAction (k : Fin 5) (x : Raw) :
    rawAction (rowPerm k) x = Fin.ofNat 1331 (mapCode (rowLabelFn k) x.val) := by
  have he : rawAction (rowPerm k) x = encodeTriple (rowFinMap k ∘ decodeTriple x) := by
    unfold rawAction
    congr 1
    funext i
    apply Fin.ext
    exact rowPerm_apply k (decodeTriple x i)
  rw [he]
  have hv : (encodeTriple (rowFinMap k ∘ decodeTriple x)).val = mapCode (rowLabelFn k) x.val := by
    change encode ((rowFinMap k (decodeTriple x 0)).val)
      ((rowFinMap k (decodeTriple x 1)).val) ((rowFinMap k (decodeTriple x 2)).val) = _
    rw [rowFinMap_val, rowFinMap_val, rowFinMap_val]
    rfl
  apply Fin.ext
  rw [hv]
  exact (Nat.mod_eq_of_lt (hv ▸ (encodeTriple (rowFinMap k ∘ decodeTriple x)).isLt)).symm

variable {K : Type} [Field K]

noncomputable def rowElt (k : Fin 5) : MonoidAlgebra K (Sfin 11) :=
  MonoidAlgebra.single (rowPerm k)⁻¹ 1

theorem rawAlgebra_rowElt (k : Fin 5) (x y : Raw) :
    rawAlgebra (rowElt (K := K) k) x y =
      if Fin.ofNat 1331 (mapCode (rowLabelFn k) x.val)=y then 1 else 0 := by
  simp only [rowElt, rawAlgebra, MonoidAlgebra.lift_single, one_smul]
  change (if x=rawAction (rowPerm k)⁻¹ y then (1 : K) else 0) = _
  simp only [rawAction_inverse_iff, row_rawAction]

noncomputable def prototypeZ (t : K) : MonoidAlgebra K (Sfin 11) :=
  (1+t) • 1 + rowElt 0 + t • rowElt 1

noncomputable def prototypeA (t : K) : MonoidAlgebra K (Sfin 11) :=
  t • rowElt 2 + (1+t) • rowElt 3 + t • rowElt 4

theorem prototypeA_matrix [CharP K 2] (t : K) : rawAlgebra (prototypeA t) = AMatrix t := by
  ext x y
  simp [prototypeA, map_add, map_smul, Matrix.add_apply, Matrix.smul_apply,
    rawAlgebra_rowElt, AMatrix, rectSparse, Arow, rowValue, codeValue, rowLabelFn, add_assoc]

/-- ZMatrix is the genuine block operator followed by the injection-support projection. -/
theorem prototypeZ_projected_matrix [CharP K 2] (t : K) :
    rawProjection * rawAlgebra (prototypeZ t) = ZMatrix t := by
  ext x y
  rw [rawProjection, Matrix.diagonal_mul]
  by_cases hg : good x.val = true
  · simp [hg, prototypeZ, map_add, map_smul, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, rawAlgebra_rowElt, ZMatrix, rectSparse, Zrow, rowValue, codeValue,
      rowLabelFn, blockCode, add_assoc]
  · simp [hg, ZMatrix, rectSparse, Zrow, rowValue]

end SelfContainedCycle010
