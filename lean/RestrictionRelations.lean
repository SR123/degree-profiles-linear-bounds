/-
Cycle 004. Restriction preserves the canonical annihilator categories.
This requires no characteristic, stable-rank or genericity hypothesis.
The proof constructs equivariant orbit maps using only retained support labels.
-/
import CanonicalClass

set_option autoImplicit false
open CategoryTheory
namespace SelfContainedCycle004
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep
open DegreeProfilesReview.ConcreteM4 SelfContainedCycle003

variable {K : Type} [Field K] {n N : ℕ}

def rankIncl (h : n ≤ N) : Sfin n →* Sfin N := Subgroup.inclusion (Sfin_mono h)

noncomputable def restrictRep (h : n ≤ N) (M : Rep K (Sfin N)) : Rep K (Sfin n) :=
  (Action.res (ModuleCat K) (rankIncl h)).obj M

section Orbit
variable {𝒰 : BasisSystem}

def retainedSupport (x : 𝒰.Rk N) (n : ℕ) : Finset ℕ :=
  (𝒰.supp (𝒰.up N x)).filter (fun l => l < n)

abbrev retainedCard (x : 𝒰.Rk N) (n : ℕ) := (retainedSupport x n).card

noncomputable def retainedEnum (x : 𝒰.Rk N) (n : ℕ) : Fin (retainedCard x n) → ℕ :=
  fun i => (retainedSupport x n).orderEmbOfFin rfl i

theorem retainedEnum_injective (x : 𝒰.Rk N) : Function.Injective (retainedEnum x n) :=
  ((retainedSupport x n).orderEmbOfFin rfl).injective

theorem retainedEnum_mem (x : 𝒰.Rk N) (i : Fin (retainedCard x n)) :
    retainedEnum x n i ∈ retainedSupport x n := Finset.orderEmbOfFin_mem _ rfl i

theorem retainedEnum_lt (x : 𝒰.Rk N) (i : Fin (retainedCard x n)) :
    retainedEnum x n i < n := (Finset.mem_filter.mp (retainedEnum_mem x i)).2

theorem exists_retainedEnum (x : 𝒰.Rk N) {l : ℕ} (hl : l ∈ retainedSupport x n) :
    ∃ i, retainedEnum x n i = l := by
  have hh := Finset.range_orderEmbOfFin (retainedSupport x n) rfl
  have hl' : l ∈ Set.range ((retainedSupport x n).orderEmbOfFin rfl) := by
    rw [hh]
    exact hl
  exact hl'

theorem retainedCard_le (x : 𝒰.Rk N) {r : ℕ} (hU : 𝒰.Bounded r) :
    retainedCard x n ≤ r :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (hU _)

theorem restricted_smul_eq_of_agree (h : n ≤ N) (x : 𝒰.Rk N) (g g' : Sfin n)
    (hg : ∀ l ∈ retainedSupport x n, g.1 l = g'.1 l) :
    rankIncl h g • x = rankIncl h g' • x := by
  apply smul_eq_of_agree
  intro l hl
  change g.1 l = g'.1 l
  by_cases hn : l < n
  · exact hg l (Finset.mem_filter.mpr ⟨hl, hn⟩)
  · rw [g.2 l (by omega), g'.2 l (by omega)]

noncomputable def retainedMover (x : 𝒰.Rk N)
    (τ : (injTuples (retainedCard x n)).Rk n) : Sfin n :=
  Classical.choose (exists_Sfin_map (retainedEnum x n) (tupleVal τ)
    (retainedEnum_injective x) (tupleVal_injective τ) (retainedEnum_lt x) (tupleVal_lt τ))

theorem retainedMover_spec (x : 𝒰.Rk N) (τ : (injTuples (retainedCard x n)).Rk n)
    (i : Fin (retainedCard x n)) :
    (retainedMover x τ).1 (retainedEnum x n i) = tupleVal τ i :=
  Classical.choose_spec (exists_Sfin_map (retainedEnum x n) (tupleVal τ)
    (retainedEnum_injective x) (tupleVal_injective τ) (retainedEnum_lt x) (tupleVal_lt τ)) i

noncomputable def restrictedOrbit (h : n ≤ N) (x : 𝒰.Rk N)
    (τ : (injTuples (retainedCard x n)).Rk n) : 𝒰.Rk N := rankIncl h (retainedMover x τ) • x

theorem restrictedOrbit_smul (h : n ≤ N) (x : 𝒰.Rk N) (g : Sfin n)
    (τ : (injTuples (retainedCard x n)).Rk n) :
    restrictedOrbit h x (g • τ) = rankIncl h g • restrictedOrbit h x τ := by
  unfold restrictedOrbit
  rw [← mul_smul, ← map_mul]
  apply restricted_smul_eq_of_agree
  intro l hl
  obtain ⟨i, rfl⟩ := exists_retainedEnum x hl
  rw [retainedMover_spec, tupleVal_smul, Subgroup.coe_mul, Equiv.Perm.mul_apply,
    retainedMover_spec]

noncomputable def retainedBase (x : 𝒰.Rk N) : (injTuples (retainedCard x n)).Rk n :=
  ⟨fun i => ⟨retainedEnum x n i, retainedEnum_lt x i⟩, retainedEnum_injective x⟩

theorem restrictedOrbit_base (h : n ≤ N) (x : 𝒰.Rk N) :
    restrictedOrbit h x (retainedBase x) = x := by
  have hg : rankIncl h (retainedMover x (retainedBase x)) • x = rankIncl h 1 • x := by
    apply restricted_smul_eq_of_agree
    intro l hl
    obtain ⟨i, rfl⟩ := exists_retainedEnum x hl
    rw [retainedMover_spec]
    rfl
  unfold restrictedOrbit
  rw [hg, map_one, one_smul]

variable (K)
theorem restrictedOrbit_comm (h : n ≤ N) (x : 𝒰.Rk N) (g : Sfin n) :
    Finsupp.lmapDomain K K (restrictedOrbit h x) ∘ₗ
      Representation.ofMulAction K (Sfin n) ((injTuples (retainedCard x n)).Rk n) g =
    Representation.ofMulAction K (Sfin N) (𝒰.Rk N) (rankIncl h g) ∘ₗ
      Finsupp.lmapDomain K K (restrictedOrbit h x) := by
  apply Finsupp.lhom_ext'
  intro τ
  apply LinearMap.ext_ring
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.lsingle_apply, Representation.ofMulAction_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Representation.ofMulAction_single, restrictedOrbit_smul]

noncomputable def restrictedOrbitHom (h : n ≤ N) (x : 𝒰.Rk N) :
    permRep K (injTuples (retainedCard x n)) n ⟶ restrictRep h (permRep K 𝒰 N) where
  hom := ModuleCat.ofHom (Finsupp.lmapDomain K K (restrictedOrbit h x))
  comm := fun g => by
    apply ModuleCat.hom_ext
    exact restrictedOrbit_comm K h x g

theorem restrictedOrbitHom_single (h : n ≤ N) (x : 𝒰.Rk N) :
    (restrictedOrbitHom K h x).hom.hom (Finsupp.single (retainedBase x) 1) =
      Finsupp.single x 1 := by
  show Finsupp.lmapDomain K K (restrictedOrbit h x) (Finsupp.single (retainedBase x) 1) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, restrictedOrbit_base]

/-- Every restricted bounded-support permutation module satisfies the smaller-rank relations. -/
theorem restricted_perm_mem (h : n ≤ N) (r : ℕ) (𝒰 : BasisSystem) (hU : 𝒰.Bounded r) :
    CanonicalClass K r n (restrictRep h (permRep K 𝒰 N)) := by
  refine ⟨?_, ?_⟩
  · change Module.Finite K (𝒰.Rk N →₀ K)
    infer_instance
  · intro a ha
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change (restrictRep h (permRep K 𝒰 N)).ρ.asAlgebraHom a (Finsupp.single x 1) = 0
    rw [← restrictedOrbitHom_single K h x, ← algebra_action_comm,
      ha _ (retainedCard_le x hU)]
    simp
end Orbit

/-- Natural group-algebra compatibility of restriction. -/
theorem restriction_algebra_action (h : n ≤ N) (M : Rep K (Sfin N))
    (a : MonoidAlgebra K (Sfin n)) :
    (restrictRep h M).ρ.asAlgebraHom a =
      M.ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom K K (rankIncl h) a) := by
  induction a using MonoidAlgebra.induction_on with
  | hM g => simp [restrictRep, Representation.asAlgebraHom_single, MonoidAlgebra.mapDomainAlgHom]
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hsmul k a ha => simp only [map_smul, ha]

/-- A smaller-rank relation lifts to zero in the larger action algebra. -/
theorem lift_relations (h : n ≤ N) (r : ℕ) (a : MonoidAlgebra K (Sfin n))
    (ha : a ∈ TupleRelations K r n) :
    MonoidAlgebra.mapDomainAlgHom K K (rankIncl h) a ∈ TupleRelations K r N := by
  intro b hb
  have hmem := restricted_perm_mem K h r (injTuples b)
    (fun x => (injTuples_bounded b x).trans hb)
  rw [← restriction_algebra_action h (permRep K (injTuples b) N) a]
  exact hmem.2 a ha

/-- Restriction preserves the canonical category, without stability assumptions. -/
theorem canonical_restrict (h : n ≤ N) (r : ℕ) (M : Rep K (Sfin N))
    (hM : CanonicalClass K r N M) : CanonicalClass K r n (restrictRep h M) := by
  refine ⟨hM.1, fun a ha => ?_⟩
  rw [restriction_algebra_action]
  exact hM.2 _ (lift_relations h r a ha)

end SelfContainedCycle004
