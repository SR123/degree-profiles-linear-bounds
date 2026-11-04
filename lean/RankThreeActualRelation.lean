/- Cycle 010: the certified finite matrix gives an actual support-three relation. -/
import RankThreePrototypeAction
import EmbeddingCompression
import TopTupleTest
import RankThreeNonvacuity

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
open CategoryTheory
namespace SelfContainedCycle010
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle008 SelfContainedCycle009

variable {K : Type} [Field K] [CharP K 2]

theorem raw_imageStep_injective (t : K) (ht : t^2+t+1=0) :
    Function.Injective (imageStep (Matrix.toLinAlgEquiv' (ZMatrix t))
      (Matrix.toLinAlgEquiv' (AMatrix t))) := by
  apply compressed_image_injective _ _ (Matrix.toLin' (EMatrix t))
    (Matrix.toLin' (LMatrix t)) (Matrix.toLinAlgEquiv' (candidateMatrix t))
  · have h := congrArg Matrix.toLin' (coordinate_reconstruction t ht)
    simpa only [Matrix.toLin'_mul, LinearMap.comp_assoc] using h
  · have h := congrArg Matrix.toLin' (coordinate_compression t ht)
    simpa only [Matrix.toLin'_mul, LinearMap.comp_assoc] using h
  · exact candidate_injective t ht

theorem rawEmbed_prototypeZ (t : K) (v : (permRep K (injTuples 3) 11).V) :
    rawEmbed ((permRep K (injTuples 3) 11).ρ.asAlgebraHom (prototypeZ t) v) =
      Matrix.toLinAlgEquiv' (ZMatrix t) (rawEmbed v) := by
  rw [← prototypeZ_projected_matrix, map_mul]
  change _ = Matrix.toLinAlgEquiv' rawProjection
    (Matrix.toLinAlgEquiv' (rawAlgebra (prototypeZ t)) (rawEmbed v))
  rw [← rawEmbed_action, rawProjection_embed]

theorem actual_imageStep_injective (t : K) (ht : t^2+t+1=0) :
    Function.Injective (imageStep
      ((permRep K (injTuples 3) 11).ρ.asAlgebraHom (prototypeZ t))
      ((permRep K (injTuples 3) 11).ρ.asAlgebraHom (prototypeA t))) := by
  apply imageStep_injective_of_embedding _ _
    (Matrix.toLinAlgEquiv' (ZMatrix t)) (Matrix.toLinAlgEquiv' (AMatrix t))
    rawEmbed rawEmbed_injective (rawEmbed_prototypeZ t)
  · intro v
    rw [rawEmbed_action, prototypeA_matrix]
  · exact raw_imageStep_injective t ht

/-- One witness in the actual group algebra annihilates every tuple module of support ≤3. -/
theorem actual_tuple_relation (t : K) (ht : t^2+t+1=0) :
    ∃ b : MonoidAlgebra K (Sfin 11),
      prototypeZ t * b * prototypeZ t - prototypeZ t ∈ TupleRelations K 3 11 := by
  let ρ := (permRep K (injTuples 3) 11).ρ.asAlgebraHom
  haveI : FiniteDimensional K (permRep K (injTuples 3) 11).V := by
    change Module.Finite K ((injTuples 3).Rk 11 →₀ K)
    infer_instance
  obtain ⟨P,h0,hP⟩ := imageStep_polynomial (ρ (prototypeZ t)) (ρ (prototypeA t))
    (actual_imageStep_injective t ht)
  refine ⟨polynomialInverse (prototypeZ t) (prototypeA t) P, ?_⟩
  rw [tupleRelations_iff_top (by decide : 3 ≤ 11)]
  have h := polynomial_action_innerInverse ρ (prototypeZ t) (prototypeA t) P h0 hP
  simpa only [map_sub, map_mul, sub_eq_zero] using h

/-- The same witness works on every canonical module, not a separately chosen inverse. -/
theorem common_canonical_innerInverse (t : K) (ht : t^2+t+1=0) :
    ∃ b : MonoidAlgebra K (Sfin 11), ∀ X : Rep K (Sfin 11),
      CanonicalClass K 3 11 X →
      X.ρ.asAlgebraHom (prototypeZ t) * X.ρ.asAlgebraHom b *
        X.ρ.asAlgebraHom (prototypeZ t) = X.ρ.asAlgebraHom (prototypeZ t) := by
  obtain ⟨b,hb⟩ := actual_tuple_relation t ht
  refine ⟨b,fun X hX => ?_⟩
  have h := hX.2 _ hb
  simpa only [map_sub, map_mul, sub_eq_zero] using h

/-- The common witness also commutes with every equivariant map. -/
theorem common_natural_innerInverse (t : K) (ht : t^2+t+1=0) :
    ∃ b : MonoidAlgebra K (Sfin 11),
      (∀ X : Rep K (Sfin 11), CanonicalClass K 3 11 X →
        X.ρ.asAlgebraHom (prototypeZ t) * X.ρ.asAlgebraHom b *
          X.ρ.asAlgebraHom (prototypeZ t) = X.ρ.asAlgebraHom (prototypeZ t)) ∧
      (∀ (X Y : Rep K (Sfin 11)) (f : X ⟶ Y) (v : X.V),
        f.hom.hom (X.ρ.asAlgebraHom b v) = Y.ρ.asAlgebraHom b (f.hom.hom v)) := by
  obtain ⟨b,hb⟩ := common_canonical_innerInverse t ht
  exact ⟨b,hb,fun _ _ f v => algebra_action_comm f b v⟩

/-- A genuine field and coefficient give the actual relation, not merely a matrix instance. -/
theorem actual_relation_nonvacuity :
    ∃ t : AlgebraicClosure (ZMod 2), t^2+t+1=0 ∧
      ∃ b : MonoidAlgebra (AlgebraicClosure (ZMod 2)) (Sfin 11),
        prototypeZ t * b * prototypeZ t - prototypeZ t ∈
          TupleRelations (AlgebraicClosure (ZMod 2)) 3 11 := by
  obtain ⟨t,ht,_⟩ := parameter_nonvacuity
  exact ⟨t,ht,actual_tuple_relation t ht⟩

end SelfContainedCycle010
