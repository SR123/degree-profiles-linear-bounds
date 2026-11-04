/- Cycle 007: turn the certified pair matrix into the actual action-algebra relation. -/
import RankTwoParameters
import RestrictionRelations
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
open CategoryTheory
namespace SelfContainedCycle007
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4 SelfContainedCycle003 SelfContainedCycle004
open SelfContainedCycle006

variable {K : Type} [Field K]

/-- Restrict an actual finite-support permutation to the seven labels. -/
def labelMap (g : Sfin 7) : Map7 := fun i => ⟨g.1 i, Sfin_lt g.2 i.2⟩

theorem labelMap_mul (g h : Sfin 7) : labelMap (g * h) = labelMap g ∘ labelMap h := rfl

def pairMatrixHom : Sfin 7 →* Matrix Pair Pair K where
  toFun g := mapMatrix (labelMap g)
  map_one' := by
    ext x y
    simp [mapMatrix, pairMap, labelMap, Matrix.one_apply]
  map_mul' g h := by rw [labelMap_mul, ← mapMatrix_comp]

noncomputable def pairAlgebra : MonoidAlgebra K (Sfin 7) →ₐ[K] Matrix Pair Pair K :=
  MonoidAlgebra.lift K (Sfin 7) _ pairMatrixHom

/-- Extend a genuine seven-label permutation by the identity. -/
def liftPerm (s : Equiv.Perm Label) : Sfin 7 :=
  ⟨s.extendDomain Fin.equivSubtype, fun k hk =>
    Equiv.Perm.extendDomain_apply_not_subtype s Fin.equivSubtype (by omega)⟩

theorem labelMap_liftPerm (s : Equiv.Perm Label) : labelMap (liftPerm s) = s := by
  funext i
  apply Fin.ext
  exact Equiv.Perm.extendDomain_apply_image s Fin.equivSubtype i

noncomputable def asPerm (s : Map7) : Equiv.Perm Label :=
  if h : Function.Bijective s then Equiv.ofBijective s h else 1

theorem asPerm_apply (s : Map7) (hs : Function.Bijective s) : (asPerm s : Map7) = s := by
  unfold asPerm
  rw [dif_pos hs]
  rfl

noncomputable def mapElt (s : Map7) : MonoidAlgebra K (Sfin 7) :=
  Finsupp.single (liftPerm (asPerm s)) 1

noncomputable def listAlgebra : List Map7 → MonoidAlgebra K (Sfin 7)
  | [] => 0
  | s :: L => mapElt s + listAlgebra L

theorem pairAlgebra_mapElt (s : Map7) (hs : Function.Bijective s) :
    pairAlgebra (mapElt s : MonoidAlgebra K (Sfin 7)) = mapMatrix s := by
  simp [pairAlgebra, mapElt, MonoidAlgebra.lift_single, pairMatrixHom,
    labelMap_liftPerm, asPerm_apply s hs]

theorem pairAlgebra_list (L : List Map7) (hL : ∀ s ∈ L, Function.Bijective s) :
    pairAlgebra (listAlgebra L : MonoidAlgebra K (Sfin 7)) = listMatrix L := by
  induction L with
  | nil => simp [listAlgebra, listMatrix]
  | cons s L ih =>
    rw [listAlgebra, map_add, pairAlgebra_mapElt s (hL s (by simp)),
      ih (fun t ht => hL t (by simp [ht]))]
    rfl

noncomputable def prototypeZ (t : K) : MonoidAlgebra K (Sfin 7) :=
  listAlgebra z0List + t • listAlgebra z1List
noncomputable def prototypeA (t : K) : MonoidAlgebra K (Sfin 7) :=
  listAlgebra a0List + t • listAlgebra a1List

theorem pairAlgebra_prototypeZ (t : K) : pairAlgebra (prototypeZ t) = Z0 + t • Z1 := by
  rw [prototypeZ, map_add, map_smul, pairAlgebra_list, pairAlgebra_list]
  · rfl
  all_goals intro s hs; exact maps_are_permutations s (by simp only [List.mem_append]; tauto)

theorem pairAlgebra_prototypeA (t : K) : pairAlgebra (prototypeA t) = A0 + t • A1 := by
  rw [prototypeA, map_add, map_smul, pairAlgebra_list, pairAlgebra_list]
  · rfl
  all_goals intro s hs; exact maps_are_permutations s (by simp only [List.mem_append]; tauto)

theorem prototype_pair_relation [CharP K 2] (t : K) (ht : t^2+t+1=0) :
    pairAlgebra (prototypeZ t * prototypeA t * prototypeZ t - prototypeZ t) = 0 := by
  rw [map_sub, map_mul, map_mul, pairAlgebra_prototypeZ, pairAlgebra_prototypeA,
    rank_two_inner_inverse t ht, sub_self]

/-- Embed a tuple permutation module into pair coordinates through an injective basis map. -/
noncomputable def pairEmbed {b : ℕ} (e : (injTuples b).Rk 7 → Pair) :
    (permRep K (injTuples b) 7).V →ₗ[K] (Pair → K) :=
  (Finsupp.linearEquivFunOnFinite K K Pair).toLinearMap.comp (Finsupp.lmapDomain K K e)

theorem pairEmbed_single {b : ℕ} (e : (injTuples b).Rk 7 → Pair)
    (x : (injTuples b).Rk 7) : pairEmbed (K := K) e (Finsupp.single x 1) = Pi.single (e x) 1 := by
  simp [pairEmbed, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.linearEquivFunOnFinite_single]

theorem pairEmbed_injective {b : ℕ} (e : (injTuples b).Rk 7 → Pair)
    (he : Function.Injective e) : Function.Injective (pairEmbed (K := K) e) :=
  (Finsupp.linearEquivFunOnFinite K K Pair).injective.comp (Finsupp.mapDomain_injective he)

/-- Compatibility is for the full group algebra, not just the two block generators. -/
theorem pairEmbed_action {b : ℕ} (e : (injTuples b).Rk 7 → Pair)
    (he : ∀ (g : Sfin 7) (x : (injTuples b).Rk 7), e (g • x) = pairMap (labelMap g) (e x))
    (a : MonoidAlgebra K (Sfin 7)) (v : (permRep K (injTuples b) 7).V) :
    pairEmbed e ((permRep K (injTuples b) 7).ρ.asAlgebraHom a v) =
      Matrix.toLinAlgEquiv' (pairAlgebra a) (pairEmbed e v) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
    have hlin : (pairEmbed (K := K) e).comp ((permRep K (injTuples b) 7).ρ g) =
        (Matrix.toLinAlgEquiv' (mapMatrix (labelMap g))).comp (pairEmbed e) := by
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      change pairEmbed e (Representation.ofMulAction K (Sfin 7) ((injTuples b).Rk 7)
        g (Finsupp.single x 1)) = Matrix.toLinAlgEquiv' (mapMatrix (labelMap g))
          (pairEmbed e (Finsupp.single x 1))
      rw [Representation.ofMulAction_single, pairEmbed_single, pairEmbed_single,
        Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_single_one]
      funext y
      simp [mapMatrix, he g x, Pi.single_apply]
    simpa [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, pairAlgebra,
      MonoidAlgebra.lift_single, pairMatrixHom] using LinearMap.congr_fun hlin v
  | hadd a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | hsmul c a ha => simp only [map_smul, LinearMap.smul_apply, ha]

theorem pair_kernel_kills_tuples {b : ℕ} (e : (injTuples b).Rk 7 → Pair)
    (hi : Function.Injective e)
    (he : ∀ (g : Sfin 7) (x : (injTuples b).Rk 7), e (g • x) = pairMap (labelMap g) (e x))
    (a : MonoidAlgebra K (Sfin 7)) (ha : pairAlgebra a = 0) :
    (permRep K (injTuples b) 7).ρ.asAlgebraHom a = 0 := by
  apply LinearMap.ext
  intro v
  apply pairEmbed_injective e hi
  rw [pairEmbed_action e he, ha]
  simp

def onePair (x : (injTuples 1).Rk 7) : Pair := (x.1 0, x.1 0)
def twoPair (x : (injTuples 2).Rk 7) : Pair := (x.1 0, x.1 1)

theorem onePair_injective : Function.Injective onePair := by
  intro x y h
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa [onePair, hi] using congrArg Prod.fst h

theorem twoPair_injective : Function.Injective twoPair := by
  intro x y h
  apply Subtype.ext
  funext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem onePair_smul (g : Sfin 7) (x : (injTuples 1).Rk 7) :
    onePair (g • x) = pairMap (labelMap g) (onePair x) := by
  apply Prod.ext <;> apply Fin.ext <;> exact tupleVal_smul g x 0

theorem twoPair_smul (g : Sfin 7) (x : (injTuples 2).Rk 7) :
    twoPair (g • x) = pairMap (labelMap g) (twoPair x) := by
  apply Prod.ext <;> apply Fin.ext
  · exact tupleVal_smul g x 0
  · exact tupleVal_smul g x 1

/-- The empty injection module is trivial. -/
theorem zeroTuple_action (g : Sfin 7) : (permRep K (injTuples 0) 7).ρ g = 1 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  have hx : g • x = x := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  simp [permRep, Representation.ofMulAction_single, hx]

theorem prototypeZ_zeroTuple [CharP K 2] (t : K) :
    (permRep K (injTuples 0) 7).ρ.asAlgebraHom (prototypeZ t) = 0 := by
  have he (s : Map7) : (permRep K (injTuples 0) 7).ρ.asAlgebraHom
      (mapElt s : MonoidAlgebra K (Sfin 7)) = 1 := by
    unfold mapElt
    rw [Representation.asAlgebraHom_single, one_smul, zeroTuple_action]
  simp only [prototypeZ, z0List, z1List, listAlgebra, map_add, add_zero,
    map_smul, he]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  have hv : v + v = 0 := by
    have hh : (2 : K) = 0 := CharTwo.two_eq_zero
    simpa only [two_smul, zero_smul] using congrArg (fun c : K => c • v) hh
  rw [hv, smul_zero, add_zero]

/-- The concrete certificate is an actual support-two annihilator relation. -/
theorem prototype_relation [CharP K 2] (t : K) (ht : t^2+t+1=0) :
    prototypeZ t * prototypeA t * prototypeZ t - prototypeZ t ∈ TupleRelations K 2 7 := by
  intro b hb
  have hc : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rw [map_sub, map_mul, map_mul, prototypeZ_zeroTuple, zero_mul, zero_mul, sub_self]
  · exact pair_kernel_kills_tuples onePair onePair_injective onePair_smul _
      (prototype_pair_relation t ht)
  · exact pair_kernel_kills_tuples twoPair twoPair_injective twoPair_smul _
      (prototype_pair_relation t ht)

/-- Relabelling by a genuine symmetric-group element. -/
noncomputable def conjugateAlgebra {N : ℕ} (u : Sfin N) :
    MonoidAlgebra K (Sfin N) →ₐ[K] MonoidAlgebra K (Sfin N) :=
  MonoidAlgebra.mapDomainAlgHom K K (MulAut.conj u)

theorem conjugateAlgebra_formula {N : ℕ} (u : Sfin N) (a : MonoidAlgebra K (Sfin N)) :
    conjugateAlgebra u a = MonoidAlgebra.single u (1 : K) * a * MonoidAlgebra.single u⁻¹ 1 := by
  induction a using MonoidAlgebra.induction_on with
  | hM g => simp [conjugateAlgebra, MonoidAlgebra.mapDomainAlgHom,
      MonoidAlgebra.single_mul_single, MonoidAlgebra.of_apply, MulAut.conj_apply]
  | hadd a b ha hb => simp only [map_add, ha, hb, mul_add, add_mul]
  | hsmul c a ha => simp only [map_smul, ha, mul_smul_comm, smul_mul_assoc]

theorem conjugate_relation {N r : ℕ} (u : Sfin N) (a : MonoidAlgebra K (Sfin N))
    (ha : a ∈ TupleRelations K r N) : conjugateAlgebra u a ∈ TupleRelations K r N := by
  intro b hb
  rw [conjugateAlgebra_formula, map_mul, map_mul, ha b hb, mul_zero, zero_mul]

noncomputable def transportAlgebra {N : ℕ} (hN : 7 ≤ N) (u : Sfin N) :
    MonoidAlgebra K (Sfin 7) →ₐ[K] MonoidAlgebra K (Sfin N) :=
  (conjugateAlgebra u).comp (MonoidAlgebra.mapDomainAlgHom K K (rankIncl hN))

theorem transport_relation {N r : ℕ} (hN : 7 ≤ N) (u : Sfin N)
    (a : MonoidAlgebra K (Sfin 7)) (ha : a ∈ TupleRelations K r 7) :
    transportAlgebra hN u a ∈ TupleRelations K r N :=
  conjugate_relation u _ (lift_relations hN r a ha)

/-- The inner inverse holds on every canonical object at every larger rank and relabelling. -/
theorem transported_innerInverse [CharP K 2] {N : ℕ} (hN : 7 ≤ N) (u : Sfin N)
    (t : K) (ht : t^2+t+1=0) (M : Rep K (Sfin N)) (hM : CanonicalClass K 2 N M) :
    let z := M.ρ.asAlgebraHom (transportAlgebra hN u (prototypeZ t))
    let a := M.ρ.asAlgebraHom (transportAlgebra hN u (prototypeA t))
    z * a * z = z := by
  have hh := hM.2 _ (transport_relation hN u _ (prototype_relation t ht))
  simpa only [map_sub, map_mul, sub_eq_zero] using hh

/-- Naturality of the same transported witness for arbitrary representation morphisms. -/
theorem transported_witness_comm {N : ℕ} (hN : 7 ≤ N) (u : Sfin N) (t : K)
    {X Y : Rep K (Sfin N)} (f : X ⟶ Y) (x : X.V) :
    f.hom.hom (X.ρ.asAlgebraHom (transportAlgebra hN u (prototypeA t)) x) =
      Y.ρ.asAlgebraHom (transportAlgebra hN u (prototypeA t)) (f.hom.hom x) :=
  algebra_action_comm f _ x

end SelfContainedCycle007
