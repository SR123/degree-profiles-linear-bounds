/-
Claude, 25 Sep 2026.  Formalisation of Cycle 017, part A: localisation.

Setting: labels `< t` form `Ω`; the ambient rank is `M ≥ t`; `i : P_r(t) → P_r(M)` is the actual
basis inclusion and `p : P_r(M) → P_r(t)` the coordinate projection.  If a group-algebra element
`y` of `S_t` kills every `P_j(t)` with `j < r`, then its image in `S_M` acts on `P_r(M)` exactly
as `i ∘ y ∘ p`: it kills every tuple that uses a label `≥ t`.
-/
import RestrictionRelations
import ResidualSplitting

set_option autoImplicit false
open CategoryTheory

namespace ClaudeC017
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004

variable {K : Type} [Field K]

section Maps
variable (K) {t M : ℕ} (r : ℕ) (h : t ≤ M)

/-- The actual inclusion `P_r(t) → P_r(M)`. -/
noncomputable def iMap : ((injTuples r).Rk t →₀ K) →ₗ[K] ((injTuples r).Rk M →₀ K) :=
  Finsupp.lmapDomain K K (inclRk (injTuples r) h)

/-- The coordinate projection `P_r(M) → P_r(t)`. -/
noncomputable def pMap : ((injTuples r).Rk M →₀ K) →ₗ[K] ((injTuples r).Rk t →₀ K) :=
  Finsupp.lcomapDomain (inclRk (injTuples r) h) (inclRk_injective _ h)

variable {K r h}

theorem iMap_single (x : (injTuples r).Rk t) (c : K) :
    iMap K r h (Finsupp.single x c) = Finsupp.single (inclRk (injTuples r) h x) c := by
  simp [iMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem pMap_single_incl (x : (injTuples r).Rk t) (c : K) :
    pMap K r h (Finsupp.single (inclRk (injTuples r) h x) c) = Finsupp.single x c := by
  simp only [pMap, Finsupp.lcomapDomain_apply]
  exact Finsupp.comapDomain_single _ _ _ _

theorem pMap_single_not (x : (injTuples r).Rk M) (hx : x ∉ Set.range (inclRk (injTuples r) h))
    (c : K) : pMap K r h (Finsupp.single x c) = 0 := by
  classical
  ext y
  simp only [pMap, Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.coe_zero,
    Pi.zero_apply]
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact hx ⟨y, rfl⟩

theorem pMap_iMap (v : (injTuples r).Rk t →₀ K) : pMap K r h (iMap K r h v) = v :=
  Finsupp.leftInverse_lcomapDomain_mapDomain _ (inclRk_injective _ h) v

end Maps

section Equivariance
variable {t M r : ℕ} (h : t ≤ M)

/-- The inclusion intertwines every group-algebra element of `S_t` with its image in `S_M`. -/
theorem iMap_algebra (y : MonoidAlgebra K (Sfin t)) (v : (injTuples r).Rk t →₀ K) :
    iMap K r h ((permRep K (injTuples r) t).ρ.asAlgebraHom y v) =
      (permRep K (injTuples r) M).ρ.asAlgebraHom
        (MonoidAlgebra.mapDomainAlgHom K K (rankIncl h) y) (iMap K r h v) := by
  induction y using MonoidAlgebra.induction_on generalizing v with
  | hM g =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u w hu hw => simp only [map_add, hu, hw]
    | single x c =>
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainAlgHom_apply,
        MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single, one_smul]
      change iMap K r h (Representation.ofMulAction K (Sfin t) _ g (Finsupp.single x c)) =
        Representation.ofMulAction K (Sfin M) _ (rankIncl h g) (iMap K r h (Finsupp.single x c))
      rw [Representation.ofMulAction_single, iMap_single, iMap_single,
        Representation.ofMulAction_single, inclRk_smul]
      rfl
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | hsmul c a ha => simp only [map_smul, LinearMap.smul_apply, ha]

end Equivariance

section Localise
variable {t M r : ℕ} (h : t ≤ M)

/-- A tuple of `P_r(M)` that is not in the image of `P_r(t)` has fewer than `r` labels `< t`. -/
theorem retainedCard_lt (x : (injTuples r).Rk M) (hx : x ∉ Set.range (inclRk (injTuples r) h)) :
    retainedCard x t < r := by
  have hinj : Function.Injective (fun i => (x.1 i).val) := x.2
  have hsupp : ((injTuples r).supp ((injTuples r).up M x)).card = r := by
    change (Finset.univ.image (fun i => (x.1 i).val)).card = r
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [mem_range_inclRk] at hx
  unfold retainedCard retainedSupport
  calc _ < ((injTuples r).supp ((injTuples r).up M x)).card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro hsub
        apply hx
        intro l hl
        have := (Finset.mem_filter.mp (hsub hl)).2
        exact Finset.mem_range.mpr this
    _ = r := hsupp

/-- **Localisation.** If `y` kills `P_j(t)` for all `j < r`, its image kills every tuple of
`P_r(M)` that meets the new labels. -/
theorem lift_kills_outside (y : MonoidAlgebra K (Sfin t)) {s : ℕ} (hs : s + 1 = r)
    (hy : y ∈ TupleRelations K s t) (x : (injTuples r).Rk M)
    (hx : x ∉ Set.range (inclRk (injTuples r) h)) (c : K) :
    (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom K K (rankIncl h) y)
      (Finsupp.single x c) = 0 := by
  have hcard : retainedCard x t ≤ s := by have := retainedCard_lt h x hx; omega
  rw [← restriction_algebra_action h (permRep K (injTuples r) M) y]
  have key : (restrictRep h (permRep K (injTuples r) M)).ρ.asAlgebraHom y
      (Finsupp.single x 1) = 0 := by
    rw [← restrictedOrbitHom_single K h x, ← algebra_action_comm, hy _ hcard]
    simp
  have hc : Finsupp.single x c = c • Finsupp.single x (1 : K) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  change ((restrictRep h (permRep K (injTuples r) M)).ρ.asAlgebraHom y) (Finsupp.single x c) = 0
  rw [hc, LinearMap.map_smul]
  change c • ((restrictRep h (permRep K (injTuples r) M)).ρ.asAlgebraHom y) (Finsupp.single x 1) = 0
  rw [key, smul_zero]

/-- **Localised form** `Y = i ∘ y ∘ p` on `P_r(M)`. -/
theorem lift_eq_localised (y : MonoidAlgebra K (Sfin t)) {s : ℕ} (hs : s + 1 = r)
    (hy : y ∈ TupleRelations K s t) :
    (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom K K (rankIncl h) y) =
      (iMap K r h).comp (((permRep K (injTuples r) t).ρ.asAlgebraHom y).comp (pMap K r h)) := by
  apply Finsupp.lhom_ext
  intro x c
  by_cases hx : x ∈ Set.range (inclRk (injTuples r) h)
  · obtain ⟨x0, rfl⟩ := hx
    rw [LinearMap.comp_apply, LinearMap.comp_apply, pMap_single_incl, iMap_algebra, iMap_single]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, pMap_single_not x hx, map_zero, map_zero]
    exact lift_kills_outside h y hs hy x hx c

end Localise
end ClaudeC017
