/- Cycle 007: match the prototype with the actual Stage 5 block generators. -/
import RankTwoActionRelation
import DegreeProfilesReview.ShiftedM5

set_option autoImplicit false
open CategoryTheory
namespace SelfContainedCycle007
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4 DegreeProfilesReview.ConcreteM5
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open SelfContainedCycle006 SelfContainedCycle004 SelfContainedCycle003

/-- Coordinates chosen to match (01)(23) and (02)(13), not a new block convention. -/
def blockWords : Fin 4 → ElemAb 2 2 :=
  ![Multiplicative.ofAdd ![0,0], Multiplicative.ofAdd ![1,0],
    Multiplicative.ofAdd ![0,1], Multiplicative.ofAdd ![1,1]]

theorem blockWords_bijective : Function.Bijective blockWords := by decide

noncomputable def blockPoint (n : ℕ) (i : Fin 4) : ℕ := (blockEquiv 2 2 n (blockWords i)).1

theorem blockPoint_bounds (n : ℕ) (i : Fin 4) : n ≤ blockPoint n i ∧ blockPoint n i < n + 4 :=
  (blockEquiv 2 2 n (blockWords i)).2

theorem blockPoint_injective (n : ℕ) : Function.Injective (blockPoint n) :=
  Subtype.val_injective.comp ((blockEquiv 2 2 n).injective.comp blockWords_bijective.1)

@[simp] theorem blockPoint_eq (n : ℕ) (i j : Fin 4) : blockPoint n i = blockPoint n j ↔ i = j :=
  (blockPoint_injective n).eq_iff

theorem blockPoint_ne_low (n : ℕ) (i : Fin 4) (k : ℕ) (hk : k < n) : blockPoint n i ≠ k := by
  have hh := (blockPoint_bounds n i).1
  omega

noncomputable def labelImages (n : ℕ) : Label → ℕ :=
  ![blockPoint n 0, blockPoint n 1, blockPoint n 2, blockPoint n 3, 0, 1, 2]

theorem labelImages_lt (n : ℕ) (hn : 3 ≤ n) (i : Label) : labelImages n i < n + 4 := by
  fin_cases i
  · exact (blockPoint_bounds n 0).2
  · exact (blockPoint_bounds n 1).2
  · exact (blockPoint_bounds n 2).2
  · exact (blockPoint_bounds n 3).2
  · change 0 < n + 4; omega
  · change 1 < n + 4; omega
  · change 2 < n + 4; omega

theorem labelImages_injective (n : ℕ) (hn : 3 ≤ n) : Function.Injective (labelImages n) := by
  have h0 (i : Fin 4) : blockPoint n i ≠ 0 := blockPoint_ne_low n i 0 (by omega)
  have h1 (i : Fin 4) : blockPoint n i ≠ 1 := blockPoint_ne_low n i 1 (by omega)
  have h2 (i : Fin 4) : blockPoint n i ≠ 2 := blockPoint_ne_low n i 2 (by omega)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [labelImages, eq_comm]

noncomputable def blockRelabel (n : ℕ) (hn : 3 ≤ n) : Sfin (n + 4) :=
  Classical.choose (exists_Sfin_map (fun i : Label => i.val) (labelImages n)
    Fin.val_injective (labelImages_injective n hn) (fun i => by dsimp; have := i.isLt; omega)
    (labelImages_lt n hn))

theorem blockRelabel_spec (n : ℕ) (hn : 3 ≤ n) (i : Label) :
    (blockRelabel n hn).1 i = labelImages n i :=
  Classical.choose_spec (exists_Sfin_map (fun i : Label => i.val) (labelImages n)
    Fin.val_injective (labelImages_injective n hn) (fun i => by dsimp; have := i.isLt; omega)
    (labelImages_lt n hn)) i

def wordShift (j : Fin 2) : Fin 4 → Fin 4 := ![![1,0,3,2], ![2,3,0,1]] j

theorem blockWords_shift (j : Fin 2) (i : Fin 4) :
    blockWords (wordShift j i) = Multiplicative.ofAdd (Pi.single j 1) * blockWords i := by
  revert j i
  decide

theorem generator_blockPoint (n : ℕ) (j : Fin 2) (i : Fin 4) :
    (σgen 2 2 n j).1 (blockPoint n i) = blockPoint n (wordShift j i) := by
  change blockHom 2 2 n (Multiplicative.ofAdd (Pi.single j 1)) (blockPoint n i) = _
  rw [blockHom_apply_block 2 2 n _ (blockPoint_bounds n i)]
  change (blockEquiv 2 2 n (Multiplicative.ofAdd (Pi.single j 1) *
    (blockEquiv 2 2 n).symm (blockEquiv 2 2 n (blockWords i)))).1 = _
  rw [Equiv.symm_apply_apply, ← blockWords_shift]
  rfl

theorem generator_low (n : ℕ) (j : Fin 2) (k : ℕ) (hk : k < n) : (σgen 2 2 n j).1 k = k :=
  blockHom_apply_not_block 2 2 n _ (by omega)

def prototypeMap (j : Fin 2) : Map7 := ![firstGen, secondGen] j

theorem prototypeMap_bijective (j : Fin 2) : Function.Bijective (prototypeMap j) := by
  apply maps_are_permutations
  fin_cases j <;> simp [prototypeMap, z0List, z1List]

theorem labelImages_generator (n : ℕ) (hn : 3 ≤ n) (j : Fin 2) (i : Label) :
    labelImages n (prototypeMap j i) = (σgen 2 2 n j).1 (labelImages n i) := by
  have h0 (j : Fin 2) := generator_low n j 0 (by omega)
  have h1 (j : Fin 2) := generator_low n j 1 (by omega)
  have h2 (j : Fin 2) := generator_low n j 2 (by omega)
  fin_cases j <;> fin_cases i <;>
    simp [labelImages, prototypeMap, firstGen, secondGen, generator_blockPoint, wordShift, h0, h1, h2]

/-- All labels in the actual block occur among the first four specified images. -/
theorem exists_blockPoint (n : ℕ) (x : ℕ) (hx : n ≤ x ∧ x < n + 4) :
    ∃ i : Fin 4, blockPoint n i = x := by
  obtain ⟨i, hi⟩ := blockWords_bijective.2 ((blockEquiv 2 2 n).symm ⟨x, hx⟩)
  refine ⟨i, ?_⟩
  unfold blockPoint
  rw [hi, Equiv.apply_symm_apply]

theorem labelImages_first_four (n : ℕ) (i : Fin 4) :
    labelImages n ⟨i.val, by omega⟩ = blockPoint n i := by
  fin_cases i <;> rfl

theorem blockRelabel_outside (n : ℕ) (hn : 3 ≤ n) (x : ℕ) (hx : 7 ≤ x) :
    ¬ (n ≤ (blockRelabel n hn).1 x ∧ (blockRelabel n hn).1 x < n + 4) := by
  intro hh
  obtain ⟨i, hi⟩ := exists_blockPoint n _ hh
  have hm := blockRelabel_spec n hn (⟨i.val, by omega⟩ : Label)
  rw [labelImages_first_four, hi] at hm
  have he := (blockRelabel n hn).1.injective hm
  have := i.isLt
  omega

/-- Exact equality with Stage 5's generators, including its fixed arbitrary block bijection. -/
theorem generator_conjugate (n : ℕ) (hn : 3 ≤ n) (j : Fin 2) :
    blockRelabel n hn * rankIncl (by omega : 7 ≤ n + 4)
      (liftPerm (asPerm (prototypeMap j))) * (blockRelabel n hn)⁻¹ = σgen 2 2 n j := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (blockRelabel n hn).1 ((liftPerm (asPerm (prototypeMap j))).1 x) =
    (σgen 2 2 n j).1 ((blockRelabel n hn).1 x)
  by_cases hx : x < 7
  · let i : Label := ⟨x, hx⟩
    have hp : (liftPerm (asPerm (prototypeMap j))).1 x = (prototypeMap j i).val := by
      have he := congrFun (labelMap_liftPerm (asPerm (prototypeMap j))) i
      rw [asPerm_apply _ (prototypeMap_bijective j)] at he
      exact congrArg Fin.val he
    rw [hp, blockRelabel_spec]
    change labelImages n (prototypeMap j i) = (σgen 2 2 n j).1 ((blockRelabel n hn).1 i)
    rw [blockRelabel_spec, labelImages_generator n hn]
  · rw [(liftPerm (asPerm (prototypeMap j))).2 x (by omega)]
    exact (blockHom_apply_not_block 2 2 n _ (blockRelabel_outside n hn x (by omega))).symm

theorem asPerm_id : asPerm id = 1 := by
  apply Equiv.ext
  intro i
  exact congrFun (asPerm_apply id Function.bijective_id) i

theorem liftPerm_one : liftPerm (1 : Equiv.Perm Label) = 1 := by
  apply Subtype.ext
  exact Equiv.Perm.extendDomain_refl Fin.equivSubtype

variable {K : Type} [Field K]

theorem mapElt_id : (mapElt id : MonoidAlgebra K (Sfin 7)) = 1 := by
  simp only [mapElt, asPerm_id, liftPerm_one]
  rfl

theorem transport_generator (n : ℕ) (hn : 3 ≤ n) (j : Fin 2) :
    transportAlgebra (by omega : 7 ≤ n + 4) (blockRelabel n hn)
      (mapElt (prototypeMap j) : MonoidAlgebra K (Sfin 7)) =
      MonoidAlgebra.single (σgen 2 2 n j) 1 := by
  simp only [transportAlgebra, AlgHom.comp_apply, conjugateAlgebra, mapElt,
    MonoidAlgebra.mapDomainAlgHom_apply, Finsupp.mapDomain_single, MulAut.conj_apply,
    generator_conjugate]

theorem prototypeZ_formula [CharP K 2] (t : K) :
    prototypeZ t = (mapElt (prototypeMap 0) - 1) + t • (mapElt (prototypeMap 1) - 1) := by
  have hm : (-1 : MonoidAlgebra K (Sfin 7)) = 1 := by
    apply neg_eq_iff_add_eq_zero.mpr
    have hh : (2 : K) = 0 := CharTwo.two_eq_zero
    simpa only [two_smul, zero_smul] using
      congrArg (fun c : K => c • (1 : MonoidAlgebra K (Sfin 7))) hh
  simp only [prototypeZ, prototypeMap, z0List, z1List, listAlgebra, mapElt_id,
    add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg, hm, smul_add]
  abel

/-- This is the actual Stage 5 operator, not a replacement action. -/
theorem transportedZ_actual [CharP K 2] (n : ℕ) (hn : 3 ≤ n) (t : K)
    (M : Rep K (Sfin (n + 2^2))) :
    M.ρ.asAlgebraHom (transportAlgebra (by omega : 7 ≤ n + 4) (blockRelabel n hn)
      (prototypeZ t)) = zOp (σgen 2 2 n) (rootCoefficients t) M.ρ := by
  rw [prototypeZ_formula]
  simp only [map_add, map_smul, map_sub, map_one, transport_generator,
    Representation.asAlgebraHom_single, one_smul, zOp, Fin.sum_univ_two,
    rootCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

noncomputable def actualWitness (n : ℕ) (hn : 3 ≤ n) (t : K) :
    MonoidAlgebra K (Sfin (n + 2^2)) :=
  transportAlgebra (by omega : 7 ≤ n + 4) (blockRelabel n hn) (prototypeA t)

theorem actual_rank_two_innerInverse [CharP K 2] (n : ℕ) (hn : 3 ≤ n) (t : K)
    (ht : t^2+t+1=0) (M : Rep K (Sfin (n + 2^2))) (hM : CanonicalClass K 2 (n + 2^2) M) :
    let z := zOp (σgen 2 2 n) (rootCoefficients t) M.ρ
    z * M.ρ.asAlgebraHom (actualWitness n hn t) * z = z := by
  have hh := transported_innerInverse (by omega : 7 ≤ n + 4) (blockRelabel n hn) t ht M hM
  dsimp only
  rw [← transportedZ_actual n hn t M]
  exact hh

end SelfContainedCycle007
