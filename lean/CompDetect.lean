/-
Claude, 26 Sep 2026.  Uniform NS–PC comparison, part 1: exact deletion detects subquotients.

Setting (as in `PTransfer`): `N = n + q`, `q = p^a`, generic `c`, and a top-power witness `w` of
support `s` with `s < q`.  Put `e = topElt p a n c w`, an actual group-algebra element.  On every
object `M` of the canonical class of support `s`, the actual shifted quotient
`Ψhat M = ker z / (ker z ∩ im z)` is naturally the image of `e` acting on `M`
(`topProjectionEquiv`, `topProjection_natural`).

Main result (`detect`): let `𝒰` be a basis system of support `≤ r` with `r + r ≤ s`, and let
`S ≤ S'` be invariant subspaces of `P = K[𝒰_N]`.  If `e` maps `S'` into `S`, then `S' = S`.

Proof.  If `b ∈ S' \ S`, put `Y = S'/S`.  Then `e` acts as zero on `Y`, so `Ψhat Y = 0`, so
`Ψhat (P ⊗ Y) ≅ K[𝒰_n] ⊗ Ψhat Y = 0` (the actual `κ'`), so `e` acts as zero on `P ⊗ Y`, which lies
in the support-`s` class because `P ⊗ P ≅ K[(𝒰 × 𝒰)_N]` has support `≤ 2r ≤ s`.  Let `S^⊥` be the
orthogonal of `S` for the invariant dot product.  The pairing `S^⊥ ⊗ Y → K` is equivariant and
nonzero at `w ⊗ [b]`, and `S^⊥ ⊗ Y ⊆ P ⊗ Y`, so `e` acts as zero on the trivial module `K`.  But
`Ψhat K ≅ K ≠ 0` (the actual `δ'` for the one-point system), a contradiction.

No trace, dimension division or tensor equivalence is used.  All objects to which
`topProjectionEquiv` is applied are shown to lie in the canonical class of support `s`.
-/
import PFinal

set_option autoImplicit false
open CategoryTheory MonoidalCategory

namespace ClaudeComparison
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.Shifted SelfContainedCycle003 ClaudeCP

/-! ### Invariant subspaces and generic facts about representations -/

section Generic
variable {K G : Type} [Field K] [Group G]

/-- An invariant subspace, in the form required by `Rep.subrepresentation`. -/
def IsInv {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (S : Submodule K V) : Prop :=
  ∀ g, S ≤ S.comap (ρ g)

theorem iso_inv_hom_apply {X Y : Rep K G} (e : X ≅ Y) (x : X.V) :
    e.inv.hom.hom (e.hom.hom.hom x) = x := by
  have h := congrArg (fun f : X ⟶ X => f.hom.hom x) e.hom_inv_id
  exact h

theorem iso_hom_injective {X Y : Rep K G} (e : X ≅ Y) : Function.Injective e.hom.hom.hom := by
  intro x y h
  rw [← iso_inv_hom_apply e x, ← iso_inv_hom_apply e y, h]

/-- The range of a morphism of representations is invariant. -/
theorem range_isInv {X Y : Rep K G} (f : X ⟶ Y) : IsInv Y.ρ (LinearMap.range f.hom.hom) := by
  intro g y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨X.ρ g x, ?_⟩
  have h := congrArg (fun φ => φ.hom x) (f.comm g)
  exact h

theorem mono_subtype (X : Rep K G) (S : Submodule K X.V) (hS : IsInv X.ρ S) :
    Mono (Rep.subtype X S hS) :=
  (Rep.mono_iff_injective _).mpr (Submodule.injective_subtype S)

theorem epi_mkQ (X : Rep K G) (S : Submodule K X.V) (hS : IsInv X.ρ S) :
    Epi (Rep.mkQ X S hS) :=
  (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective S)

theorem mono_whiskerLeft (X : Rep K G) {Y Z : Rep K G} (f : Y ⟶ Z)
    (hf : Function.Injective f.hom.hom) : Mono (X ◁ f) :=
  (Rep.mono_iff_injective _).mpr (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

theorem epi_whiskerLeft (X : Rep K G) {Y Z : Rep K G} (f : Y ⟶ Z)
    (hf : Function.Surjective f.hom.hom) : Epi (X ◁ f) :=
  (Rep.epi_iff_surjective _).mpr (LinearMap.lTensor_surjective _ hf)

theorem whiskerRight_injective {Y Z : Rep K G} (f : Y ⟶ Z) (X : Rep K G)
    (hf : Function.Injective f.hom.hom) : Function.Injective (f ▷ X).hom.hom :=
  Module.Flat.rTensor_preserves_injective_linearMap _ hf

end Generic

/-! ### The invariant dot product on a permutation module -/

section Dot
variable {K : Type} [Field K] {X : Type} [Fintype X]

/-- `⟨v, x⟩ = Σ_i v_i x_i`. -/
noncomputable def dotB : (X →₀ K) →ₗ[K] (X →₀ K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun v x => ∑ i, v i * x i)
    (fun v v' x => by simp [add_mul, Finset.sum_add_distrib])
    (fun c v x => by simp [mul_assoc, Finset.mul_sum])
    (fun v x x' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c v x => by simp [Finset.mul_sum, mul_left_comm])

theorem dotB_apply (v x : X →₀ K) : dotB v x = ∑ i, v i * x i := rfl

theorem dotB_ofMulAction {G : Type} [Group G] [MulAction G X] (g : G) (v x : X →₀ K) :
    dotB (Representation.ofMulAction K G X g v) (Representation.ofMulAction K G X g x) =
      dotB v x := by
  simp only [dotB_apply, Representation.ofMulAction_apply]
  exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ (fun i => rfl)

/-- The orthogonal of a subspace for the dot product. -/
noncomputable def perp (S : Submodule K (X →₀ K)) : Submodule K (X →₀ K) where
  carrier := {v | ∀ x ∈ S, dotB v x = 0}
  add_mem' := fun {v v'} hv hv' x hx => by rw [map_add, LinearMap.add_apply, hv x hx, hv' x hx,
    add_zero]
  zero_mem' := fun x _ => by rw [map_zero, LinearMap.zero_apply]
  smul_mem' := fun c v hv x hx => by rw [map_smul, LinearMap.smul_apply, hv x hx, smul_zero]

theorem mem_perp {S : Submodule K (X →₀ K)} {v : X →₀ K} : v ∈ perp S ↔ ∀ x ∈ S, dotB v x = 0 :=
  Iff.rfl

theorem perp_isInv {G : Type} [Group G] [MulAction G X] {S : Submodule K (X →₀ K)}
    (hS : IsInv (Representation.ofMulAction K G X) S) :
    IsInv (Representation.ofMulAction K G X) (perp S) := by
  intro g v hv x hx
  have hx' : Representation.ofMulAction K G X g⁻¹ x ∈ S := hS g⁻¹ hx
  have h := dotB_ofMulAction (K := K) g v (Representation.ofMulAction K G X g⁻¹ x)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  rw [h]
  exact hv _ hx'

/-- Every vector outside `S` pairs nontrivially with some vector orthogonal to `S`. -/
theorem exists_perp_of_notMem {S : Submodule K (X →₀ K)} {b : X →₀ K} (hb : b ∉ S) :
    ∃ v ∈ perp S, dotB v b ≠ 0 := by
  obtain ⟨f, hfb, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
  let v : X →₀ K := Finsupp.equivFunOnFinite.symm fun i => f (Finsupp.single i 1)
  have hv : ∀ x : X →₀ K, dotB v x = f x := by
    intro x
    rw [dotB_apply]
    conv_rhs => rw [← Finsupp.univ_sum_single x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Finsupp.single i (x i) = x i • Finsupp.single i (1 : K) by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
    rfl
  refine ⟨v, fun x hx => ?_, by rw [hv]; exact hfb⟩
  rw [hv]
  have : f x ∈ S.map f := Submodule.mem_map_of_mem hx
  rw [hfS] at this
  exact this

end Dot

/-! ### The pairing `S^⊥ ⊗ S'/S → K` as a morphism of representations -/

section Pairing
variable {K G : Type} [Field K] [Group G] {X : Type} [Fintype X] [MulAction G X]

omit [Fintype X] in
theorem comap_isInv {S S' : Submodule K (X →₀ K)}
    (hS : IsInv (Representation.ofMulAction K G X) S)
    (hS' : IsInv (Representation.ofMulAction K G X) S') :
    IsInv (Rep.subrepresentation (Rep.ofMulAction K G X) S' hS').ρ (S.comap S'.subtype) :=
  fun g _ hy => hS g hy

/-- The bilinear pairing `S^⊥ × S'/S → K`. -/
noncomputable def pairLin (S S' : Submodule K (X →₀ K)) :
    ↥(perp S) →ₗ[K] (↥S' ⧸ S.comap S'.subtype) →ₗ[K] K :=
  ((S.comap S'.subtype).liftQ ((dotB.compl₁₂ (perp S).subtype S'.subtype).flip) (by
    intro y hy
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro z
    exact z.2 y.1 hy)).flip

theorem pairLin_mk (S S' : Submodule K (X →₀ K)) (z : ↥(perp S)) (y : ↥S') :
    pairLin S S' z (Submodule.Quotient.mk y) = dotB z.1 y.1 := rfl

/-- The pairing as a morphism into a one-point permutation module. -/
noncomputable def pairHom (S S' : Submodule K (X →₀ K))
    (hS : IsInv (Representation.ofMulAction K G X) S)
    (hS' : IsInv (Representation.ofMulAction K G X) S')
    {U : Type} [MulAction G U] [Subsingleton U] (u0 : U) :
    Rep.subrepresentation (Rep.ofMulAction K G X) (perp S) (perp_isInv hS) ⊗
      Rep.quotient (Rep.subrepresentation (Rep.ofMulAction K G X) S' hS') (S.comap S'.subtype)
        (comap_isInv hS hS') ⟶ Rep.ofMulAction K G U where
  hom := ModuleCat.ofHom ((Finsupp.lsingle u0) ∘ₗ TensorProduct.lift (pairLin S S'))
  comm g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro z y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    change Finsupp.single u0 (pairLin S S' ((Representation.ofMulAction K G X).subrepresentation
        (perp S) (perp_isInv hS) g z) (Submodule.Quotient.mk
          ((Representation.ofMulAction K G X).subrepresentation S' hS' g y))) =
      Representation.ofMulAction K G U g (Finsupp.single u0 (pairLin S S' z
        (Submodule.Quotient.mk y)))
    rw [pairLin_mk, pairLin_mk, Representation.ofMulAction_single,
      Subsingleton.elim (g • u0) u0]
    congr 1
    exact dotB_ofMulAction g z.1 y.1

theorem pairHom_tmul (S S' : Submodule K (X →₀ K))
    (hS : IsInv (Representation.ofMulAction K G X) S)
    (hS' : IsInv (Representation.ofMulAction K G X) S')
    {U : Type} [MulAction G U] [Subsingleton U] (u0 : U) (z : ↥(perp S)) (y : ↥S') :
    (pairHom S S' hS hS' u0).hom.hom (z ⊗ₜ Submodule.Quotient.mk y) =
      Finsupp.single u0 (dotB z.1 y.1) := rfl

end Pairing

/-! ### Detection -/

section Detect
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p]
  {a n : ℕ} {c : Fin a → K} {s : ℕ} {w : MonoidAlgebra K (Sfin (n + p ^ a))}

/-- `K[𝒰_N] ⊗ K[𝒰_N]` lies in the canonical class of support `s` when `2r ≤ s`. -/
theorem tensor_perm_mem {𝒰 : BasisSystem} {r : ℕ} (hU : 𝒰.Bounded r) (h2r : r + r ≤ s)
    (N : ℕ) : CanonicalClass K s N (permRep K 𝒰 N ⊗ permRep K 𝒰 N) :=
  annihilated_subobject _ (permProdIso (K := K) 𝒰 𝒰 N).hom
    (canonical_perm_mem s N (𝒰.prod 𝒰) ((BasisSystem.prod_bounded hU hU).mono h2r))

variable (hc : Generic p c) (hs : s < p ^ a) (hw : IsTopWitness p s a n c w)
include hc hs hw

theorem topProj_eq_zero_of_subsingleton {M : Rep K (Sfin (n + p ^ a))}
    (hM : CanonicalClass K s (n + p ^ a) M) (h : Subsingleton ((Ψhat p a n c).obj M).V) :
    topProj c w M = 0 := by
  haveI : Subsingleton (LinearMap.range (topProj c w M)) :=
    (topProjectionEquiv hc hs hw M hM).symm.injective.subsingleton
  apply LinearMap.ext
  intro x
  have h0 := Subsingleton.elim
    (⟨topProj c w M x, LinearMap.mem_range_self _ x⟩ : LinearMap.range (topProj c w M)) 0
  exact congrArg Subtype.val h0

theorem subsingleton_of_topProj_eq_zero {M : Rep K (Sfin (n + p ^ a))}
    (hM : CanonicalClass K s (n + p ^ a) M) (h : topProj c w M = 0) :
    Subsingleton ((Ψhat p a n c).obj M).V := by
  haveI : Subsingleton (LinearMap.range (topProj c w M)) := by
    rw [h, LinearMap.range_zero]
    infer_instance
  exact (topProjectionEquiv hc hs hw M hM).injective.subsingleton

/-- The trivial module survives deletion, so `e` does not act as zero on it. -/
theorem topProj_unit_ne_zero : topProj c w (permRep K BasisSystem.unit (n + p ^ a)) ≠ 0 := by
  intro h0
  have hmem : CanonicalClass K s (n + p ^ a) (permRep K BasisSystem.unit (n + p ^ a)) :=
    canonical_perm_mem s _ _ (BasisSystem.unit_bounded s)
  haveI := subsingleton_of_topProj_eq_zero hc hs hw hmem h0
  have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
  haveI : Subsingleton (permRep K BasisSystem.unit n).V :=
    (iso_hom_injective (δ' (K := K) (n := n) hc hpos (BasisSystem.unit_bounded 0)).symm).subsingleton
  have h1 := Subsingleton.elim
    (Finsupp.single (() : BasisSystem.unit.Rk n) (1 : K) : (permRep K BasisSystem.unit n).V) 0
  exact (Finsupp.single_ne_zero.mpr one_ne_zero) h1

/-- **Exact deletion at twice the support detects nonzero subquotients.**  If the actual
group-algebra element `e = topElt` maps an invariant `S'` into an invariant `S ≤ S'`, then
`S' = S`. -/
theorem detect {𝒰 : BasisSystem} {r : ℕ} (hU : 𝒰.Bounded r) (h2r : r + r ≤ s)
    {S S' : Submodule K (𝒰.Rk (n + p ^ a) →₀ K)}
    (hS : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S) (hS' : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S')
    (he : ∀ x ∈ S', topProj c w (permRep K 𝒰 (n + p ^ a)) x ∈ S) : S' ≤ S := by
  classical
  letI : Fintype (𝒰.Rk (n + p ^ a)) := Fintype.ofFinite _
  by_contra hne
  obtain ⟨b, hbS', hbS⟩ := SetLike.not_le_iff_exists.mp hne
  -- the objects
  let P := permRep K 𝒰 (n + p ^ a)
  let X' := Rep.subrepresentation P S' hS'
  let ι' := Rep.subtype P S' hS'
  let S0 : Submodule K ↥S' := S.comap S'.subtype
  have hS0 : IsInv X'.ρ S0 := comap_isInv hS hS'
  let Y := Rep.quotient X' S0 hS0
  let π := Rep.mkQ X' S0 hS0
  -- class membership, support `s`
  have hP : CanonicalClass K s (n + p ^ a) P := canonical_perm_mem s _ 𝒰 (hU.mono (by omega))
  haveI := mono_subtype P S' hS'
  have hX' : CanonicalClass K s (n + p ^ a) X' := annihilated_subobject _ ι' hP
  haveI := epi_mkQ X' S0 hS0
  have hY : CanonicalClass K s (n + p ^ a) Y := annihilated_quotient _ π hX'
  have hPP := tensor_perm_mem (K := K) hU h2r (n + p ^ a)
  haveI := mono_whiskerLeft P ι' (Submodule.injective_subtype S')
  have hPX' : CanonicalClass K s (n + p ^ a) (P ⊗ X') := annihilated_subobject _ (P ◁ ι') hPP
  haveI := epi_whiskerLeft P π (Submodule.mkQ_surjective S0)
  have hPY : CanonicalClass K s (n + p ^ a) (P ⊗ Y) := annihilated_quotient _ (P ◁ π) hPX'
  -- `e` kills `Y`
  have hY0 : topProj c w Y = 0 := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective S0 y
    have h1 : π.hom.hom (topProj c w X' x) = topProj c w Y (π.hom.hom x) :=
      algebra_action_comm π _ x
    have h2 : ι'.hom.hom (topProj c w X' x) = topProj c w P (ι'.hom.hom x) :=
      algebra_action_comm ι' _ x
    have h3 : topProj c w X' x ∈ S0 := by
      show (ι'.hom.hom (topProj c w X' x)) ∈ S
      rw [h2]
      exact he _ x.2
    change topProj c w Y (π.hom.hom x) = 0
    rw [← h1]
    exact (Submodule.Quotient.mk_eq_zero S0).mpr h3
  -- hence `Ψhat Y = 0`, `Ψhat (P ⊗ Y) = 0`, and `e` kills `P ⊗ Y`
  have hrq : r < p ^ a := by omega
  haveI hDY := subsingleton_of_topProj_eq_zero hc hs hw hY hY0
  have hDPY : Subsingleton ((Ψhat p a n c).obj (P ⊗ Y)).V := by
    haveI : Subsingleton (permRep K 𝒰 n ⊗ (Ψhat p a n c).obj Y).V := by
      change Subsingleton (TensorProduct K (𝒰.Rk n →₀ K) ((Ψhat p a n c).obj Y).V)
      infer_instance
    exact (iso_hom_injective (κ' hc hrq hU Y)).subsingleton
  have hPY0 : topProj c w (P ⊗ Y) = 0 := topProj_eq_zero_of_subsingleton hc hs hw hPY hDPY
  -- the orthogonal of `S` and the pairing
  obtain ⟨v, hv, hvb⟩ := exists_perp_of_notMem hbS
  let T := Rep.subrepresentation P (perp S) (perp_isInv hS)
  let ιT := Rep.subtype P (perp S) (perp_isInv hS)
  have hj : Function.Injective (ιT ▷ Y).hom.hom :=
    whiskerRight_injective ιT Y (Submodule.injective_subtype _)
  have hTY0 : topProj c w (T ⊗ Y) = 0 := by
    apply LinearMap.ext
    intro ξ
    apply hj
    have h := algebra_action_comm (ιT ▷ Y) (topElt p a n c w) ξ
    change (ιT ▷ Y).hom.hom (topProj c w (T ⊗ Y) ξ) = (ιT ▷ Y).hom.hom 0
    rw [map_zero]
    refine h.trans ?_
    change topProj c w (P ⊗ Y) _ = 0
    rw [hPY0, LinearMap.zero_apply]
  haveI : Subsingleton (BasisSystem.unit.Rk (n + p ^ a)) := inferInstanceAs (Subsingleton Unit)
  let Γ := @pairHom K (Sfin (n + p ^ a)) _ _ (𝒰.Rk (n + p ^ a)) _ _ S S' hS hS'
    (BasisSystem.unit.Rk (n + p ^ a)) (rkAction BasisSystem.unit (n + p ^ a)) this ()
  have hΓ : ∀ ξ, topProj c w (permRep K BasisSystem.unit (n + p ^ a)) (Γ.hom.hom ξ) = 0 := by
    intro ξ
    have h := algebra_action_comm Γ (topElt p a n c w) ξ
    change Γ.hom.hom (topProj c w (T ⊗ Y) ξ) =
      topProj c w (permRep K BasisSystem.unit (n + p ^ a)) (Γ.hom.hom ξ) at h
    rw [← h, hTY0, LinearMap.zero_apply, map_zero]
  apply topProj_unit_ne_zero hc hs hw
  apply LinearMap.ext
  intro x
  have hval : Γ.hom.hom ((⟨v, hv⟩ : ↥(perp S)) ⊗ₜ
      (Submodule.Quotient.mk (⟨b, hbS'⟩ : ↥S') : ↥S' ⧸ S0)) =
      Finsupp.single (() : BasisSystem.unit.Rk (n + p ^ a)) (dotB v b) :=
    pairHom_tmul S S' hS hS' _ ⟨v, hv⟩ ⟨b, hbS'⟩
  have hx : x = (x () * (dotB v b)⁻¹) • Γ.hom.hom ((⟨v, hv⟩ : ↥(perp S)) ⊗ₜ
      (Submodule.Quotient.mk (⟨b, hbS'⟩ : ↥S') : ↥S' ⧸ S0)) := by
    rw [hval, Finsupp.smul_single, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hvb, mul_one]
    ext u
    rw [Subsingleton.elim u (), Finsupp.single_eq_same]
  rw [hx, map_smul, hΓ, smul_zero, LinearMap.zero_apply]

end Detect

end ClaudeComparison
