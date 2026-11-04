/- Cycle 011: lift and relabel the actual rank-eleven relation to every n ≥ 7. -/
import RankThreeActualRelation
import RankTwoRelabel

set_option autoImplicit false
set_option maxHeartbeats 2000000
open CategoryTheory
namespace SelfContainedCycle011
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4 DegreeProfilesReview.ConcreteM5
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle010
open SelfContainedCycle006 (rootCoefficients)
open SelfContainedCycle007 (blockPoint blockPoint_bounds blockPoint_ne_low
  blockPoint_eq generator_blockPoint generator_low wordShift exists_blockPoint
  conjugateAlgebra conjugate_relation)

def genIndex (j : Fin 2) : Fin 5 := ⟨j.val, by omega⟩

theorem generator_involutive : ∀ (j : Fin 2) (i : Fin 11),
    rowFinMap (genIndex j) (rowFinMap (genIndex j) i) = i := by decide +kernel

theorem row_generator_inverse (j : Fin 2) : (rowPerm (genIndex j))⁻¹ = rowPerm (genIndex j) := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (rowPerm (genIndex j)).1 ((rowPerm (genIndex j)).1 x) = x
  by_cases hx : x < 11
  · let i : Fin 11 := ⟨x,hx⟩
    change (rowPerm (genIndex j)).1 ((rowPerm (genIndex j)).1 i) = i.val
    rw [rowPerm_apply, rowPerm_apply, generator_involutive]
  · rw [(rowPerm (genIndex j)).2 x (by omega), (rowPerm (genIndex j)).2 x (by omega)]

noncomputable def labelImages (n : ℕ) : Fin 11 → ℕ :=
  ![blockPoint n 0, blockPoint n 1, blockPoint n 2, blockPoint n 3, 0,1,2,3,4,5,6]

theorem labelImages_lt (n : ℕ) (hn : 7 ≤ n) (i : Fin 11) : labelImages n i < n+4 := by
  fin_cases i
  · exact (blockPoint_bounds n 0).2
  · exact (blockPoint_bounds n 1).2
  · exact (blockPoint_bounds n 2).2
  · exact (blockPoint_bounds n 3).2
  · change 0 < n+4; omega
  · change 1 < n+4; omega
  · change 2 < n+4; omega
  · change 3 < n+4; omega
  · change 4 < n+4; omega
  · change 5 < n+4; omega
  · change 6 < n+4; omega

theorem labelImages_injective (n : ℕ) (hn : 7 ≤ n) : Function.Injective (labelImages n) := by
  have h (i : Fin 4) (k : Fin 7) : blockPoint n i ≠ k.val :=
    blockPoint_ne_low n i k.val (by omega)
  have h0 (i : Fin 4) := h i 0
  have h1 (i : Fin 4) := h i 1
  have h2 (i : Fin 4) := h i 2
  have h3 (i : Fin 4) := h i 3
  have h4 (i : Fin 4) := h i 4
  have h5 (i : Fin 4) := h i 5
  have h6 (i : Fin 4) := h i 6
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [labelImages, eq_comm]

noncomputable def blockRelabel (n : ℕ) (hn : 7 ≤ n) : Sfin (n+4) :=
  Classical.choose (exists_Sfin_map (fun i : Fin 11 => i.val) (labelImages n)
    Fin.val_injective (labelImages_injective n hn) (fun i => by dsimp; have := i.isLt; omega)
    (labelImages_lt n hn))

theorem blockRelabel_spec (n : ℕ) (hn : 7 ≤ n) (i : Fin 11) :
    (blockRelabel n hn).1 i = labelImages n i :=
  Classical.choose_spec (exists_Sfin_map (fun i : Fin 11 => i.val) (labelImages n)
    Fin.val_injective (labelImages_injective n hn) (fun i => by dsimp; have := i.isLt; omega)
    (labelImages_lt n hn)) i

theorem labelImages_generator (n : ℕ) (hn : 7 ≤ n) (j : Fin 2) (i : Fin 11) :
    labelImages n (rowFinMap (genIndex j) i) = (σgen 2 2 n j).1 (labelImages n i) := by
  fin_cases j <;> fin_cases i
  · exact (generator_blockPoint n 0 0).symm
  · exact (generator_blockPoint n 0 1).symm
  · exact (generator_blockPoint n 0 2).symm
  · exact (generator_blockPoint n 0 3).symm
  · exact (generator_low n 0 0 (by omega)).symm
  · exact (generator_low n 0 1 (by omega)).symm
  · exact (generator_low n 0 2 (by omega)).symm
  · exact (generator_low n 0 3 (by omega)).symm
  · exact (generator_low n 0 4 (by omega)).symm
  · exact (generator_low n 0 5 (by omega)).symm
  · exact (generator_low n 0 6 (by omega)).symm
  · exact (generator_blockPoint n 1 0).symm
  · exact (generator_blockPoint n 1 1).symm
  · exact (generator_blockPoint n 1 2).symm
  · exact (generator_blockPoint n 1 3).symm
  · exact (generator_low n 1 0 (by omega)).symm
  · exact (generator_low n 1 1 (by omega)).symm
  · exact (generator_low n 1 2 (by omega)).symm
  · exact (generator_low n 1 3 (by omega)).symm
  · exact (generator_low n 1 4 (by omega)).symm
  · exact (generator_low n 1 5 (by omega)).symm
  · exact (generator_low n 1 6 (by omega)).symm

theorem labelImages_first_four (n : ℕ) (i : Fin 4) :
    labelImages n ⟨i.val, by omega⟩ = blockPoint n i := by
  fin_cases i <;> rfl

theorem blockRelabel_outside (n : ℕ) (hn : 7 ≤ n) (x : ℕ) (hx : 11 ≤ x) :
    ¬ (n ≤ (blockRelabel n hn).1 x ∧ (blockRelabel n hn).1 x < n+4) := by
  intro hh
  obtain ⟨i, hi⟩ := exists_blockPoint n _ hh
  have hm := blockRelabel_spec n hn (⟨i.val, by omega⟩ : Fin 11)
  rw [labelImages_first_four, hi] at hm
  have he := (blockRelabel n hn).1.injective hm
  have := i.isLt
  omega

/-- Equality with the existing Stage 5 generators, including its arbitrary block ordering. -/
theorem generator_conjugate (n : ℕ) (hn : 7 ≤ n) (j : Fin 2) :
    blockRelabel n hn * rankIncl (by omega : 11 ≤ n+4)
      (rowPerm (genIndex j)) * (blockRelabel n hn)⁻¹ = σgen 2 2 n j := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (blockRelabel n hn).1 ((rowPerm (genIndex j)).1 x) =
    (σgen 2 2 n j).1 ((blockRelabel n hn).1 x)
  by_cases hx : x < 11
  · let i : Fin 11 := ⟨x,hx⟩
    have hp : (rowPerm (genIndex j)).1 x = (rowFinMap (genIndex j) i).val := rowPerm_apply _ i
    rw [hp, blockRelabel_spec]
    change labelImages n (rowFinMap (genIndex j) i) = (σgen 2 2 n j).1 ((blockRelabel n hn).1 i)
    rw [blockRelabel_spec, labelImages_generator n hn]
  · rw [(rowPerm (genIndex j)).2 x (by omega)]
    exact (blockHom_apply_not_block 2 2 n _ (blockRelabel_outside n hn x (by omega))).symm

variable {K : Type} [Field K]

noncomputable def transportAlgebra {N : ℕ} (hN : 11 ≤ N) (u : Sfin N) :
    MonoidAlgebra K (Sfin 11) →ₐ[K] MonoidAlgebra K (Sfin N) :=
  (conjugateAlgebra u).comp (MonoidAlgebra.mapDomainAlgHom K K (rankIncl hN))

theorem transport_relation {N r : ℕ} (hN : 11 ≤ N) (u : Sfin N)
    (a : MonoidAlgebra K (Sfin 11)) (ha : a ∈ TupleRelations K r 11) :
    transportAlgebra hN u a ∈ TupleRelations K r N :=
  conjugate_relation u _ (lift_relations hN r a ha)

theorem transport_generator (n : ℕ) (hn : 7 ≤ n) (j : Fin 2) :
    transportAlgebra (by omega : 11 ≤ n+4) (blockRelabel n hn)
      (rowElt (genIndex j) : MonoidAlgebra K (Sfin 11)) =
      MonoidAlgebra.single (σgen 2 2 n j) 1 := by
  simp only [transportAlgebra, AlgHom.comp_apply, conjugateAlgebra, rowElt, row_generator_inverse,
    MonoidAlgebra.mapDomainAlgHom_apply, Finsupp.mapDomain_single, MulAut.conj_apply,
    generator_conjugate]

theorem prototypeZ_formula [CharP K 2] (t : K) :
    prototypeZ t = (rowElt (genIndex 0) - 1) + t • (rowElt (genIndex 1) - 1) := by
  have hm : (-1 : MonoidAlgebra K (Sfin 11)) = 1 := by
    apply neg_eq_iff_add_eq_zero.mpr
    have hh : (2 : K) = 0 := CharTwo.two_eq_zero
    simpa only [two_smul, zero_smul] using
      congrArg (fun c : K => c • (1 : MonoidAlgebra K (Sfin 11))) hh
  simp only [prototypeZ, genIndex, sub_eq_add_neg, hm, smul_add, add_smul, one_smul]
  abel

theorem transportedZ_actual [CharP K 2] (n : ℕ) (hn : 7 ≤ n) (t : K)
    (M : Rep K (Sfin (n+2^2))) :
    M.ρ.asAlgebraHom (transportAlgebra (by omega : 11 ≤ n+4) (blockRelabel n hn)
      (prototypeZ t)) = zOp (σgen 2 2 n) (rootCoefficients t) M.ρ := by
  rw [prototypeZ_formula]
  simp only [map_add, map_smul, map_sub, map_one, transport_generator,
    Representation.asAlgebraHom_single, one_smul, zOp, Fin.sum_univ_two,
    rootCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

variable [CharP K 2]

/-- Chosen once in the source algebra, independently of any representation or map. -/
noncomputable def prototypeWitness (t : K) (ht : t^2+t+1=0) : MonoidAlgebra K (Sfin 11) :=
  Classical.choose (actual_tuple_relation t ht)

theorem prototypeWitness_relation (t : K) (ht : t^2+t+1=0) :
    prototypeZ t * prototypeWitness t ht * prototypeZ t - prototypeZ t ∈ TupleRelations K 3 11 :=
  Classical.choose_spec (actual_tuple_relation t ht)

noncomputable def actualWitness (n : ℕ) (hn : 7 ≤ n) (t : K) (ht : t^2+t+1=0) :
    MonoidAlgebra K (Sfin (n+2^2)) :=
  transportAlgebra (by omega : 11 ≤ n+4) (blockRelabel n hn) (prototypeWitness t ht)

theorem actual_rank_three_innerInverse (n : ℕ) (hn : 7 ≤ n) (t : K) (ht : t^2+t+1=0)
    (M : Rep K (Sfin (n+2^2))) (hM : CanonicalClass K 3 (n+2^2) M) :
    let z := zOp (σgen 2 2 n) (rootCoefficients t) M.ρ
    z * M.ρ.asAlgebraHom (actualWitness n hn t ht) * z = z := by
  have hh := hM.2 _ (transport_relation (by omega : 11 ≤ n+4) (blockRelabel n hn) _
    (prototypeWitness_relation t ht))
  dsimp only
  rw [← transportedZ_actual n hn t M]
  simpa only [map_sub, map_mul, sub_eq_zero] using hh

theorem actualWitness_comm (n : ℕ) (hn : 7 ≤ n) (t : K) (ht : t^2+t+1=0)
    {X Y : Rep K (Sfin (n+2^2))} (f : X ⟶ Y) (x : X.V) :
    f.hom.hom (X.ρ.asAlgebraHom (actualWitness n hn t ht) x) =
      Y.ρ.asAlgebraHom (actualWitness n hn t ht) (f.hom.hom x) :=
  algebra_action_comm f _ x

end SelfContainedCycle011
