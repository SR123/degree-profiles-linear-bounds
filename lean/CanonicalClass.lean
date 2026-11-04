/-
Cycle 003: concrete category data for the bounded-support problem, without Schur theory.

TupleRelations consists of the group-algebra elements acting by zero on every injection
permutation module P_b(t), b ≤ r. CanonicalClass consists of the finite-dimensional
representations annihilated by these relations. This is precisely the annihilator
description of Cycle 002's action-algebra category. Its closure and required permutation
membership are proved, not assumed. No equivalence across ranks is asserted here.
-/
import DegreeProfilesReview.PermFromTuples
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace SelfContainedCycle003

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4 DegreeProfilesReview.ClosedSub

variable {K G : Type} [Field K] [Group G]

/-- Group-algebra actions commute with every representation morphism. -/
theorem algebra_action_comm {X Y : Rep K G} (f : X ⟶ Y)
    (a : MonoidAlgebra K G) (x : X.V) :
    f.hom.hom (X.ρ.asAlgebraHom a x) = Y.ρ.asAlgebraHom a (f.hom.hom x) := by
  exact Rep.to_Module_monoidAlgebra_map_aux X.V Y.V X.ρ Y.ρ f.hom.hom
    (fun g => ModuleCat.hom_ext_iff.mp (f.comm g)) a x

theorem biprod_decompose {X Y : Rep K G} (x : (X ⊞ Y).V) :
    (biprod.inl : X ⟶ X ⊞ Y).hom.hom ((biprod.fst : X ⊞ Y ⟶ X).hom.hom x) +
      (biprod.inr : Y ⟶ X ⊞ Y).hom.hom ((biprod.snd : X ⊞ Y ⟶ Y).hom.hom x) = x := by
  have h := congrArg (fun f : X ⊞ Y ⟶ X ⊞ Y => f.hom.hom x)
    (biprod.total (X := X) (Y := Y))
  exact h

noncomputable def biprodCoordinates (X Y : Rep K G) : (X ⊞ Y).V →ₗ[K] X.V × Y.V :=
  (biprod.fst : X ⊞ Y ⟶ X).hom.hom.prod (biprod.snd : X ⊞ Y ⟶ Y).hom.hom

theorem biprodCoordinates_injective (X Y : Rep K G) :
    Function.Injective (biprodCoordinates X Y) := by
  intro x y h
  have hf := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  change (biprod.fst : X ⊞ Y ⟶ X).hom.hom x =
    (biprod.fst : X ⊞ Y ⟶ X).hom.hom y at hf
  change (biprod.snd : X ⊞ Y ⟶ Y).hom.hom x =
    (biprod.snd : X ⊞ Y ⟶ Y).hom.hom y at hs
  calc
    x = _ := (biprod_decompose x).symm
    _ = _ := by rw [hf, hs]
    _ = y := biprod_decompose y

/-- Finite-dimensional representations killed by a specified set of algebra elements. -/
def AnnihilatedClass (I : Set (MonoidAlgebra K G)) : ObjectProperty (Rep K G) :=
  fun X => Module.Finite K X.V ∧ ∀ a ∈ I, X.ρ.asAlgebraHom a = 0

theorem annihilated_subobject (I : Set (MonoidAlgebra K G)) {X Y : Rep K G}
    (f : X ⟶ Y) [Mono f] (hY : AnnihilatedClass I Y) : AnnihilatedClass I X := by
  haveI := hY.1
  have hf := (Rep.mono_iff_injective f).mp inferInstance
  refine ⟨Module.Finite.of_injective f.hom.hom hf, ?_⟩
  intro a ha
  apply LinearMap.ext
  intro x
  apply hf
  change f.hom.hom (X.ρ.asAlgebraHom a x) = f.hom.hom 0
  rw [algebra_action_comm, hY.2 a ha]
  simp

theorem annihilated_quotient (I : Set (MonoidAlgebra K G)) {X Y : Rep K G}
    (f : X ⟶ Y) [Epi f] (hX : AnnihilatedClass I X) : AnnihilatedClass I Y := by
  haveI := hX.1
  have hf := (Rep.epi_iff_surjective f).mp inferInstance
  refine ⟨Module.Finite.of_surjective f.hom.hom hf, ?_⟩
  intro a ha
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  change Y.ρ.asAlgebraHom a (f.hom.hom x) = 0
  rw [← algebra_action_comm, hX.2 a ha]
  simp

theorem annihilated_biprod (I : Set (MonoidAlgebra K G)) {X Y : Rep K G}
    (hX : AnnihilatedClass I X) (hY : AnnihilatedClass I Y) :
    AnnihilatedClass I (X ⊞ Y) := by
  haveI := hX.1
  haveI := hY.1
  refine ⟨Module.Finite.of_injective (biprodCoordinates X Y)
    (biprodCoordinates_injective X Y), ?_⟩
  intro a ha
  apply LinearMap.ext
  intro x
  apply biprodCoordinates_injective X Y
  apply Prod.ext
  · change (biprod.fst : X ⊞ Y ⟶ X).hom.hom ((X ⊞ Y).ρ.asAlgebraHom a x) =
      (biprod.fst : X ⊞ Y ⟶ X).hom.hom 0
    rw [algebra_action_comm, hX.2 a ha]
    simp
  · change (biprod.snd : X ⊞ Y ⟶ Y).hom.hom ((X ⊞ Y).ρ.asAlgebraHom a x) =
      (biprod.snd : X ⊞ Y ⟶ Y).hom.hom 0
    rw [algebra_action_comm, hY.2 a ha]
    simp

/-- The relations of the finite sum G_t, expressed on its individual summands. -/
def TupleRelations (K : Type) [Field K] (r t : ℕ) : Set (MonoidAlgebra K (Sfin t)) :=
  {a | ∀ b : ℕ, b ≤ r → (permRep K (injTuples b) t).ρ.asAlgebraHom a = 0}

def CanonicalClass (K : Type) [Field K] (r t : ℕ) : ObjectProperty (Rep K (Sfin t)) :=
  AnnihilatedClass (TupleRelations K r t)

theorem canonical_tuple_mem (r t b : ℕ) (hb : b ≤ r) :
    CanonicalClass K r t (permRep K (injTuples b) t) := by
  refine ⟨?_, fun a ha => ha b hb⟩
  change Module.Finite K ((injTuples b).Rk t →₀ K)
  infer_instance

instance canonical_isExactClass (r t : ℕ) : IsExactClass (CanonicalClass K r t) where
  prop_of_mono := fun f _ h => annihilated_subobject _ f h
  prop_of_epi := fun f _ h => annihilated_quotient _ f h
  biprod := fun hX hY => annihilated_biprod _ hX hY
  nonempty := ⟨permRep K (injTuples 0) t, canonical_tuple_mem r t 0 (Nat.zero_le r)⟩

/-- Actual category data, constructed for every field and every pair of ranks/support bounds.
There is deliberately no input that assumes an equivalence. -/
noncomputable def canonicalSchurClass (K : Type) [Field K] (r t : ℕ) : SchurClass K r t :=
  SchurClass.ofInjTuples (CanonicalClass K r t) (canonical_tuple_mem r t)

theorem canonical_perm_mem (r t : ℕ) (𝒰 : BasisSystem) (hU : 𝒰.Bounded r) :
    CanonicalClass K r t (permRep K 𝒰 t) :=
  (canonicalSchurClass K r t).perm_mem 𝒰 hU

end SelfContainedCycle003
