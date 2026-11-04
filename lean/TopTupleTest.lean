/- Cycle 008: the top injection module alone detects the bounded-support relations. -/
import CanonicalClass

set_option autoImplicit false
open CategoryTheory
namespace SelfContainedCycle008
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4 SelfContainedCycle003

variable {K : Type} [Field K] {b r N : ℕ}

def tupleForget (h : b ≤ r) (x : (injTuples r).Rk N) : (injTuples b).Rk N :=
  ⟨fun i => x.1 (Fin.castLE h i), fun _ _ hij =>
    Fin.ext (congrArg (fun k : Fin r => k.val) (x.2 hij))⟩

theorem tupleForget_val (h : b ≤ r) (x : (injTuples r).Rk N) (i : Fin b) :
    tupleVal (tupleForget h x) i = tupleVal x (Fin.castLE h i) := rfl

theorem tupleForget_smul (h : b ≤ r) (g : Sfin N) (x : (injTuples r).Rk N) :
    tupleForget h (g • x) = g • tupleForget h x := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact (tupleVal_smul g x (Fin.castLE h i)).trans (tupleVal_smul g (tupleForget h x) i).symm

def standardTuple (h : r ≤ N) : (injTuples r).Rk N :=
  ⟨fun i => Fin.castLE h i, Fin.val_injective⟩

/-- Extend a smaller injective tuple by a finite permutation, with no division or averaging. -/
theorem tupleForget_surjective (h : b ≤ r) (hN : r ≤ N) :
    Function.Surjective (tupleForget (N := N) h) := by
  intro y
  obtain ⟨g, hg⟩ := exists_Sfin_map (fun i : Fin b => i.val) (tupleVal y)
    Fin.val_injective (tupleVal_injective y)
    (fun i => by dsimp; have := i.isLt; omega) (tupleVal_lt y)
  refine ⟨g • standardTuple hN, ?_⟩
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [← tupleVal, tupleForget_val, tupleVal_smul]
  exact hg i

noncomputable def tupleForgetHom (h : b ≤ r) :
    permRep K (injTuples r) N ⟶ permRep K (injTuples b) N where
  hom := ModuleCat.ofHom (Finsupp.lmapDomain K K (tupleForget h))
  comm g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change Finsupp.lmapDomain K K (tupleForget h)
      (Representation.ofMulAction K (Sfin N) ((injTuples r).Rk N) g (Finsupp.single x 1)) =
      Representation.ofMulAction K (Sfin N) ((injTuples b).Rk N) g
        (Finsupp.lmapDomain K K (tupleForget h) (Finsupp.single x 1))
    simp only [Representation.ofMulAction_single, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, tupleForget_smul]

theorem tupleForgetHom_surjective (h : b ≤ r) (hN : r ≤ N) :
    Function.Surjective ((tupleForgetHom (K := K) (N := N) h).hom.hom) :=
  Finsupp.mapDomain_surjective (tupleForget_surjective h hN)

/-- One top module replaces all lower-support tests when there are enough labels. -/
theorem tupleRelations_iff_top (hN : r ≤ N) (a : MonoidAlgebra K (Sfin N)) :
    a ∈ TupleRelations K r N ↔ (permRep K (injTuples r) N).ρ.asAlgebraHom a = 0 := by
  constructor
  · exact fun ha => ha r le_rfl
  · intro ha b hb
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := tupleForgetHom_surjective (K := K) hb hN v
    rw [← algebra_action_comm, ha]
    simp

end SelfContainedCycle008
