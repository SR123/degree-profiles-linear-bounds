/-
Claude, 26 Sep 2026.  Uniform NS–PC comparison, part 2: a uniform bound on chains of invariant
subspaces of a bounded-support permutation module, over an algebraically closed field of
characteristic `p`.

* `delImg`: the image of an invariant subspace `S ⊆ K[𝒰_N]` under the actual deletion functor,
  `range (Ψhat (S ↪ K[𝒰_N]) ≫ δ')`, an `S_n`-invariant subspace of `K[𝒰_n]`.
* `delImg_strict`: strict inclusions stay strict (from `detect`).
* `chain_step`: every strict chain of invariant subspaces at rank `n + q` gives one of the same
  length at rank `n`.  The chain is arbitrary; no compatibility across ranks is used.
* `chainBoundPerm`: with `q = p^(2r+1) > 2r`, the unconditional quadratic witness theorem
  `topWitnessHypothesis_of_isAlgClosed` at support `2r`, and iterated deletion down to rank
  `≤ M = triW (2r) + q`, every strict chain has fewer than `#𝒰_M + 1` steps, at every rank.
-/
import CompDetect

set_option autoImplicit false
open CategoryTheory MonoidalCategory

namespace ClaudeComparison
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.Shifted SelfContainedCycle003 ClaudeCP

/-! ### Chains in a finite-dimensional space -/

theorem finrank_ge_of_strictMono {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {L : ℕ} {W : Fin (L + 1) → Submodule K V} (hW : StrictMono W) :
    ∀ i : Fin (L + 1), (i : ℕ) ≤ Module.finrank K (W i) := by
  intro i
  induction i using Fin.induction with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have h := Submodule.finrank_lt_finrank_of_lt (hW (Fin.castSucc_lt_succ (i := i)))
    rw [Fin.val_succ]
    rw [Fin.coe_castSucc] at ih
    omega

theorem not_strictMono_of_finrank_le {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {L : ℕ} (hL : Module.finrank K V ≤ L)
    (W : Fin (L + 2) → Submodule K V) : ¬ StrictMono W := by
  intro hW
  have h1 := finrank_ge_of_strictMono hW (Fin.last (L + 1))
  have h2 := Submodule.finrank_le (W (Fin.last (L + 1)))
  rw [Fin.val_last] at h1
  omega

/-! ### Deletion images -/

section Step
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p]
  {a n : ℕ} {c : Fin a → K} {𝒰 : BasisSystem} {r : ℕ}

/-- The inclusion of subrepresentations `S ⊆ S'`. -/
noncomputable def subIncl {G : Type} [Group G] (X : Rep K G) {S S' : Submodule K X.V} (hS : IsInv X.ρ S)
    (hS' : IsInv X.ρ S') (hle : S ≤ S') :
    Rep.subrepresentation X S hS ⟶ Rep.subrepresentation X S' hS' where
  hom := ModuleCat.ofHom (Submodule.inclusion hle)
  comm _ := rfl

theorem subIncl_comp {G : Type} [Group G] (X : Rep K G) {S S' : Submodule K X.V}
    (hS : IsInv X.ρ S) (hS' : IsInv X.ρ S') (hle : S ≤ S') :
    subIncl X hS hS' hle ≫ Rep.subtype X S' hS' = Rep.subtype X S hS := rfl

variable (hc : Generic p c) (hrq : r < p ^ a) (hU : 𝒰.Bounded r)

/-- The deletion image of an invariant subspace, inside `K[𝒰_n]`. -/
noncomputable def delImg (S : Submodule K (𝒰.Rk (n + p ^ a) →₀ K))
    (hS : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S) : Submodule K (𝒰.Rk n →₀ K) :=
  LinearMap.range ((Ψhat p a n c).map (Rep.subtype (permRep K 𝒰 (n + p ^ a)) S hS) ≫ (δ' hc hrq hU).hom).hom.hom

theorem delImg_isInv (S : Submodule K (𝒰.Rk (n + p ^ a) →₀ K))
    (hS : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S) :
    IsInv (permRep K 𝒰 n).ρ (delImg hc hrq hU S hS) :=
  range_isInv _

theorem delImg_mono {S S' : Submodule K (𝒰.Rk (n + p ^ a) →₀ K)}
    (hS : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S) (hS' : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S')
    (hle : S ≤ S') : delImg hc hrq hU S hS ≤ delImg hc hrq hU S' hS' := by
  rintro y ⟨d, rfl⟩
  refine ⟨((Ψhat p a n c).map (subIncl (permRep K 𝒰 (n + p ^ a)) hS hS' hle)).hom.hom d, ?_⟩
  rw [← subIncl_comp (permRep K 𝒰 (n + p ^ a)) hS hS' hle, Functor.map_comp]
  rfl

variable {s : ℕ} (hs : s < p ^ a) {w : MonoidAlgebra K (Sfin (n + p ^ a))}
  (hw : IsTopWitness p s a n c w) (h2r : r + r ≤ s)

include hs hw h2r in
/-- **Strict inclusions stay strict under exact deletion.** -/
theorem delImg_strict {S S' : Submodule K (𝒰.Rk (n + p ^ a) →₀ K)}
    (hS : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S) (hS' : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S')
    (hlt : S < S') : delImg hc hrq hU S hS < delImg hc hrq hU S' hS' := by
  refine lt_of_le_of_ne (delImg_mono hc hrq hU hS hS' hlt.le) fun heq => ?_
  apply (not_le_of_gt hlt)
  apply detect hc hs hw hU h2r hS hS'
  intro x hx
  let P := permRep K 𝒰 (n + p ^ a)
  have hP : CanonicalClass K s (n + p ^ a) P := canonical_perm_mem s _ 𝒰 (hU.mono (by omega))
  let X' := Rep.subrepresentation P S' hS'
  let ι' := Rep.subtype P S' hS'
  let X := Rep.subrepresentation P S hS
  let ι := Rep.subtype P S hS
  haveI := mono_subtype P S' hS'
  haveI := mono_subtype P S hS
  have hX' : CanonicalClass K s (n + p ^ a) X' := annihilated_subobject _ ι' hP
  have hX : CanonicalClass K s (n + p ^ a) X := annihilated_subobject _ ι hP
  let x' : X'.V := (⟨x, hx⟩ : ↥S')
  let d := (topProjectionEquiv hc hs hw X' hX').symm
    ⟨topProj c w X' x', LinearMap.mem_range_self _ x'⟩
  have hd : ((topProjectionEquiv hc hs hw X' hX' d : LinearMap.range (topProj c w X')) : X'.V) =
      topProj c w X' x' := by
    simp only [d, LinearEquiv.apply_symm_apply]
  -- the image of `d` lies in the image of `S`
  have hmem : ((Ψhat p a n c).map ι' ≫ (δ' hc hrq hU).hom).hom.hom d ∈
      delImg hc hrq hU S hS := by
    rw [heq]
    exact LinearMap.mem_range_self _ d
  obtain ⟨d0, hd0⟩ := hmem
  have hd0' : ((Ψhat p a n c).map ι).hom.hom d0 = ((Ψhat p a n c).map ι').hom.hom d :=
    iso_hom_injective (δ' hc hrq hU) hd0
  have e1 := topProjection_natural hc hs hw hX' hP ι' d
  have e2 := topProjection_natural hc hs hw hX hP ι d0
  rw [← hd0', e2] at e1
  have hcomm : ι'.hom.hom (topProj c w X' x') = topProj c w P (ι'.hom.hom x') :=
    algebra_action_comm ι' _ x'
  change topProj c w P (ι'.hom.hom x') ∈ S
  rw [← hcomm, ← hd, ← e1]
  exact (topProjectionEquiv hc hs hw X hX d0 : X.V).2

include hc hrq hU hs hw h2r in
/-- **One deletion step for an arbitrary strict invariant chain.** -/
theorem chain_step {L : ℕ} (W : Fin L → Submodule K (𝒰.Rk (n + p ^ a) →₀ K))
    (hW : ∀ i, IsInv (permRep K 𝒰 (n + p ^ a)).ρ (W i)) (hmono : StrictMono W) :
    ∃ W' : Fin L → Submodule K (𝒰.Rk n →₀ K),
      (∀ i, IsInv (permRep K 𝒰 n).ρ (W' i)) ∧ StrictMono W' :=
  ⟨fun i => delImg hc hrq hU (W i) (hW i), fun i => delImg_isInv hc hrq hU (W i) (hW i),
    fun _ _ hij => delImg_strict hc hrq hU hs hw h2r (hW _) (hW _) (hmono hij)⟩

end Step

/-! ### The uniform chain bound over an algebraically closed field -/

theorem card_rk_le (𝒰 : BasisSystem) {m M : ℕ} (h : m ≤ M) :
    Nat.card (𝒰.Rk m) ≤ Nat.card (𝒰.Rk M) :=
  Nat.card_le_card_of_injective _ (inclRk_injective 𝒰 h)

/-- **Uniformly bounded invariant chains** in `K[𝒰_N]`, for `𝒰` of bounded support, over an
algebraically closed field of characteristic `p`.  The bound `#𝒰_M` with
`M = triW (2r) + p^(2r+1)` does not depend on `N`. -/
theorem chainBoundPerm (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
    (𝒰 : BasisSystem) {r : ℕ} (hU : 𝒰.Bounded r) :
    ∃ L : ℕ, ∀ N (W : Fin (L + 2) → Submodule K (𝒰.Rk N →₀ K)),
      (∀ i, IsInv (permRep K 𝒰 N).ρ (W i)) → ¬ StrictMono W := by
  classical
  let a := r + r + 1
  have hs : r + r < p ^ a :=
    lt_trans (Nat.lt_succ_self _) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)
  let M := ClaudeC017.triW (r + r) + p ^ a
  refine ⟨Nat.card (𝒰.Rk M), fun N => ?_⟩
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W hW hmono
    by_cases hN : N ≤ M
    · letI : Fintype (𝒰.Rk N) := Fintype.ofFinite _
      apply not_strictMono_of_finrank_le _ W hmono
      rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
      exact card_rk_le 𝒰 hN
    · obtain ⟨n, rfl⟩ : ∃ n, N = n + p ^ a := ⟨N - p ^ a, by omega⟩
      have hn : ClaudeC017.triW (r + r) ≤ n := by omega
      obtain ⟨c, hc, w, hw⟩ :=
        topWitnessHypothesis_of_isAlgClosed p K (r + r) a n hs hn
      have hrq : r < p ^ a := by omega
      obtain ⟨W', hW', hmono'⟩ :=
        chain_step hc hrq hU hs hw le_rfl W hW hmono
      have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
      exact ih n (by omega) W' hW' hmono'

end ClaudeComparison
