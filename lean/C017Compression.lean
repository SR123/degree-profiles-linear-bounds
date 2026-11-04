/-
Claude, 25 Sep 2026.  Formalisation of Cycle 017, part B: compression with `r` fresh labels.

For `t + r ≤ M`, every linear endomorphism `d` of `P_r(t)` that commutes with the permutations
of tuple positions is the compression `p ∘ ρ(c) ∘ i` of an actual group-algebra element
`c ∈ K[S_M]`.  The fresh labels are `t, t+1, …, t+r-1`.
-/
import C017Localize

set_option autoImplicit false
open CategoryTheory

namespace ClaudeC017
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004

/-! ### Positions -/

section Positions
variable {r t : ℕ}

/-- Permuting the positions of an injective tuple. -/
def posSMul (π : Equiv.Perm (Fin r)) (τ : (injTuples r).Rk t) : (injTuples r).Rk t :=
  ⟨fun i => τ.1 (π⁻¹ i), fun _ _ hij => π⁻¹.injective (τ.2 hij)⟩

instance posAction : MulAction (Equiv.Perm (Fin r)) ((injTuples r).Rk t) where
  smul := posSMul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem pos_val (π : Equiv.Perm (Fin r)) (τ : (injTuples r).Rk t) (i : Fin r) :
    (π • τ).1 i = τ.1 (π⁻¹ i) := rfl

theorem tupleVal_pos (π : Equiv.Perm (Fin r)) (τ : (injTuples r).Rk t) (i : Fin r) :
    tupleVal (π • τ) i = tupleVal τ (π⁻¹ i) := rfl

/-- The set of labels of a tuple. -/
def tset (τ : (injTuples r).Rk t) : Finset ℕ := Finset.univ.image (tupleVal τ)

theorem mem_tset {τ : (injTuples r).Rk t} {l : ℕ} : l ∈ tset τ ↔ ∃ i, tupleVal τ i = l := by
  simp [tset]

theorem tset_card (τ : (injTuples r).Rk t) : (tset τ).card = r := by
  rw [tset, Finset.card_image_of_injective _ (tupleVal_injective τ), Finset.card_univ,
    Fintype.card_fin]

theorem tset_pos (π : Equiv.Perm (Fin r)) (τ : (injTuples r).Rk t) : tset (π • τ) = tset τ := by
  ext l
  simp only [mem_tset, tupleVal_pos]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨π i, by simp⟩

theorem tset_lt (τ : (injTuples r).Rk t) {l : ℕ} (hl : l ∈ tset τ) : l < t := by
  obtain ⟨i, rfl⟩ := mem_tset.mp hl
  exact tupleVal_lt τ i

theorem tset_smul (g : Sfin t) (τ : (injTuples r).Rk t) : tset (g • τ) = (tset τ).image g.1 := by
  ext l
  simp only [mem_tset, tupleVal_smul, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩

theorem smul_pos_comm (g : Sfin t) (π : Equiv.Perm (Fin r)) (τ : (injTuples r).Rk t) :
    g • (π • τ) = π • (g • τ) := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change tupleVal (g • (π • τ)) i = tupleVal (π • (g • τ)) i
  rw [tupleVal_smul, tupleVal_pos, tupleVal_pos, tupleVal_smul]

/-- Two injective `r`-tuples with the same label set differ by a position permutation. -/
theorem exists_pos_of_tset_eq (τ σ : (injTuples r).Rk t) (h : tset τ = tset σ) :
    ∃ π : Equiv.Perm (Fin r), π • σ = τ := by
  classical
  have hmem : ∀ i, ∃ j, tupleVal σ j = tupleVal τ i := fun i =>
    mem_tset.mp (h ▸ mem_tset.mpr ⟨i, rfl⟩)
  choose f hf using hmem
  have hinj : Function.Injective f := fun i i' hii' =>
    tupleVal_injective τ (by rw [← hf i, ← hf i', hii'])
  let e : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨e⁻¹, Subtype.ext (funext fun i => Fin.ext ?_)⟩
  change tupleVal σ ((e⁻¹)⁻¹ i) = tupleVal τ i
  rw [inv_inv]
  exact hf i

variable (K : Type) [Field K]

/-- The linear action of a position permutation. -/
noncomputable def posLin (π : Equiv.Perm (Fin r)) :
    ((injTuples r).Rk t →₀ K) →ₗ[K] ((injTuples r).Rk t →₀ K) :=
  Finsupp.lmapDomain K K (π • ·)

theorem posLin_single (π : Equiv.Perm (Fin r)) (τ : (injTuples r).Rk t) (c : K) :
    posLin K π (Finsupp.single τ c) = Finsupp.single (π • τ) c := by
  simp [posLin, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- Commuting with every position permutation. -/
def PosEquivariant (d : ((injTuples r).Rk t →₀ K) →ₗ[K] ((injTuples r).Rk t →₀ K)) : Prop :=
  ∀ π : Equiv.Perm (Fin r), d ∘ₗ posLin K π = posLin K π ∘ₗ d

end Positions

/-! ### Orbit representatives for the position action -/

section Reps
variable {r t : ℕ}

/-- A chosen representative of the position orbit. -/
noncomputable def posRep (τ : (injTuples r).Rk t) : (injTuples r).Rk t :=
  (Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin r)) ((injTuples r).Rk t)) τ).out

theorem exists_pos_rep (τ : (injTuples r).Rk t) : ∃ π : Equiv.Perm (Fin r), π • posRep τ = τ := by
  have h := Quotient.mk_out (s := MulAction.orbitRel (Equiv.Perm (Fin r)) ((injTuples r).Rk t)) τ
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨π, hπ⟩ := h
  have hπ' : π • τ = posRep τ := hπ
  exact ⟨π⁻¹, by rw [← hπ', inv_smul_smul]⟩

theorem posRep_eq_of_tset (τ σ : (injTuples r).Rk t) (h : tset τ = tset σ) :
    posRep τ = posRep σ := by
  obtain ⟨π, hπ⟩ := exists_pos_of_tset_eq τ σ h
  unfold posRep
  congr 1
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr ⟨π, hπ⟩

theorem tset_posRep (τ : (injTuples r).Rk t) : tset (posRep τ) = tset τ := by
  obtain ⟨π, hπ⟩ := exists_pos_rep τ
  conv_rhs => rw [← hπ]
  rw [tset_pos]

end Reps

/-! ### The projector built from `r` disjoint transpositions with fresh labels -/

section Projector
variable {K : Type} [Field K] {r t M : ℕ} (hM : t + r ≤ M)

/-- The transposition exchanging the `j`-th label of `u` with the fresh label `t + j`. -/
def binSwap (u : (injTuples r).Rk t) (j : Fin r) : Sfin M :=
  ⟨Equiv.swap (tupleVal u j) (t + j), fun i hi => by
    have h1 := tupleVal_lt u j
    have h2 := j.2
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)⟩

/-- Tuples of `P_r(M)` that use one of the first `k` fresh labels. -/
def usesBins (k : ℕ) : Set ((injTuples r).Rk M) :=
  {σ | ∃ j, j < k ∧ (t + j) ∈ tset σ}

/-- The partial product `∏_{j<k} (1 - (u_j, t+j))`. -/
noncomputable def partE (u : (injTuples r).Rk t) : ℕ → MonoidAlgebra K (Sfin M)
  | 0 => 1
  | k + 1 => if hk : k < r then
      (1 - MonoidAlgebra.single (binSwap hM u ⟨k, hk⟩) 1) * partE u k
    else partE u k

theorem swap_smul_fixes (u : (injTuples r).Rk t) (j : Fin r) (σ : (injTuples r).Rk M)
    (hu : tupleVal u j ∉ tset σ) (hb : t + j.1 ∉ tset σ) : binSwap hM u j • σ = σ := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change tupleVal (binSwap hM u j • σ) i = tupleVal σ i
  rw [tupleVal_smul]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; exact hu (mem_tset.mpr ⟨i, h⟩)
  · intro h; exact hb (mem_tset.mpr ⟨i, h⟩)

theorem swap_smul_uses (u : (injTuples r).Rk t) (j : Fin r) (σ : (injTuples r).Rk M)
    (hu : tupleVal u j ∈ tset σ) : t + j.1 ∈ tset (binSwap hM u j • σ) := by
  obtain ⟨i, hi⟩ := mem_tset.mp hu
  refine mem_tset.mpr ⟨i, ?_⟩
  rw [tupleVal_smul]
  change Equiv.swap (tupleVal u j) (t + j) (tupleVal σ i) = t + j
  rw [hi, Equiv.swap_apply_left]

theorem swap_preserves_uses (u : (injTuples r).Rk t) (j : Fin r) (k : ℕ) (hk : k ≤ j.1)
    (σ : (injTuples r).Rk M) (hσ : σ ∈ usesBins (t := t) k) :
    binSwap hM u j • σ ∈ usesBins (t := t) k := by
  obtain ⟨l, hl, hmem⟩ := hσ
  refine ⟨l, hl, ?_⟩
  rw [tset_smul]
  refine Finset.mem_image.mpr ⟨t + l, hmem, ?_⟩
  change Equiv.swap (tupleVal u j) (t + j) (t + l) = t + l
  have := tupleVal_lt u j
  exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

theorem usesBins_mono {k k' : ℕ} (h : k ≤ k') :
    usesBins (r := r) (t := t) (M := M) k ⊆ usesBins (r := r) (t := t) (M := M) k' := by
  intro σ hσ
  obtain ⟨j, hj, hm⟩ := hσ
  exact ⟨j, by omega, hm⟩

/-- The action of a group element on `P_r(M)`. -/
theorem action_single {N : ℕ} (g : Sfin N) (σ : (injTuples r).Rk N) (c : K) :
    (permRep K (injTuples r) N).ρ.asAlgebraHom (MonoidAlgebra.single g 1) (Finsupp.single σ c) =
      Finsupp.single (g • σ) c := by
  rw [Representation.asAlgebraHom_single, one_smul]
  exact Representation.ofMulAction_single g σ c

theorem action_supported (g : Sfin M) (k : ℕ)
    (hg : ∀ σ ∈ usesBins (r := r) (t := t) (M := M) k, g • σ ∈ usesBins (t := t) k)
    (v : (injTuples r).Rk M →₀ K) (hv : v ∈ Finsupp.supported K K (usesBins (t := t) k)) :
    (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.single g 1) v ∈
      Finsupp.supported K K (usesBins (t := t) k) := by
  rw [Representation.asAlgebraHom_single, one_smul]
  change Finsupp.lmapDomain K K (g • ·) v ∈ _
  have h1 : Finsupp.lmapDomain K K (g • ·) v ∈
      (Finsupp.supported K K (usesBins (t := t) k)).map (Finsupp.lmapDomain K K (g • ·)) :=
    Submodule.mem_map_of_mem hv
  rw [Finsupp.lmapDomain_supported] at h1
  refine Finsupp.supported_mono ?_ h1
  rintro _ ⟨σ, hσ, rfl⟩
  exact hg σ hσ

theorem tset_incl (h : t ≤ M) (τ : (injTuples r).Rk t) :
    tset (inclRk (injTuples r) h τ) = tset τ := by
  have hv : tupleVal (inclRk (injTuples r) h τ) = tupleVal τ := by
    rw [← up_injTuples, ← up_injTuples, up_inclRk]
  rw [tset, tset, hv]

/-- The invariant of the partial products. -/
theorem partE_invariant (u : (injTuples r).Rk t) (h : t ≤ M) :
    ∀ k, k ≤ r → ∀ τ : (injTuples r).Rk t,
      (permRep K (injTuples r) M).ρ.asAlgebraHom (partE hM u k)
          (Finsupp.single (inclRk (injTuples r) h τ) 1) -
        (if (∀ j : Fin r, j.1 < k → tupleVal u j ∈ tset τ)
          then Finsupp.single (inclRk (injTuples r) h τ) (1 : K) else 0) ∈
        Finsupp.supported K K (usesBins (t := t) k) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ τ
    simp [partE]
  | succ k ih =>
    intro hk τ
    have hkr : k < r := by omega
    have ih' := ih (by omega) τ
    set τ' := inclRk (injTuples r) h τ
    set w := (permRep K (injTuples r) M).ρ.asAlgebraHom (partE hM u k) (Finsupp.single τ' 1)
    set T := binSwap hM u ⟨k, hkr⟩
    have hT : ∀ σ ∈ usesBins (r := r) (t := t) (M := M) k, T • σ ∈ usesBins (t := t) k :=
      fun σ hσ => swap_preserves_uses hM u ⟨k, hkr⟩ k le_rfl σ hσ
    have hstep : (permRep K (injTuples r) M).ρ.asAlgebraHom (partE hM u (k+1))
        (Finsupp.single τ' 1) =
        w - (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.single T 1) w := by
      simp only [partE, dif_pos hkr, map_mul, map_sub, map_one, Module.End.mul_apply,
        LinearMap.sub_apply, Module.End.one_apply]
      rfl
    rw [hstep]
    -- split w = A + R
    set A : (injTuples r).Rk M →₀ K :=
      if (∀ j : Fin r, j.1 < k → tupleVal u j ∈ tset τ) then Finsupp.single τ' 1 else 0
    have hR : w - A ∈ Finsupp.supported K K (usesBins (t := t) k) := ih'
    have hRT := action_supported (K := K) T k hT _ hR
    have hmono := Finsupp.supported_mono (M := K) (R := K) (usesBins_mono (r := r) (t := t)
      (M := M) (Nat.le_succ k))
    have hτlab : ∀ l ∈ tset τ', l < t := by
      intro l hl; rw [tset_incl] at hl; exact tset_lt τ hl
    -- the main term
    have key : A - (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.single T 1) A -
        (if (∀ j : Fin r, j.1 < k + 1 → tupleVal u j ∈ tset τ)
          then Finsupp.single τ' (1 : K) else 0) ∈
        Finsupp.supported K K (usesBins (t := t) (k+1)) := by
      by_cases hc : ∀ j : Fin r, j.1 < k → tupleVal u j ∈ tset τ
      · simp only [A, if_pos hc]
        rw [action_single]
        by_cases hu : tupleVal u ⟨k, hkr⟩ ∈ tset τ
        · have hc' : ∀ j : Fin r, j.1 < k + 1 → tupleVal u j ∈ tset τ := by
            intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
            · exact hc j hj
            · have : j = ⟨k, hkr⟩ := Fin.ext hj
              rw [this]; exact hu
          rw [if_pos hc', sub_sub_cancel_left]
          refine Submodule.neg_mem _ (Finsupp.single_mem_supported K _ ?_)
          refine ⟨k, Nat.lt_succ_self k, ?_⟩
          apply swap_smul_uses
          rw [tset_incl]; exact hu
        · have hc' : ¬ ∀ j : Fin r, j.1 < k + 1 → tupleVal u j ∈ tset τ :=
            fun hh => hu (hh ⟨k, hkr⟩ (Nat.lt_succ_self k))
          have hfix : T • τ' = τ' := swap_smul_fixes hM u ⟨k, hkr⟩ τ'
            (by rw [tset_incl]; exact hu) (fun hb => by have := hτlab _ hb; omega)
          rw [if_neg hc', hfix]
          simp
      · have hc' : ¬ ∀ j : Fin r, j.1 < k + 1 → tupleVal u j ∈ tset τ :=
          fun hh => hc (fun j hj => hh j (by omega))
        simp [A, if_neg hc, if_neg hc']
    have hsplit : w - (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.single T 1) w -
        (if (∀ j : Fin r, j.1 < k + 1 → tupleVal u j ∈ tset τ)
          then Finsupp.single τ' (1 : K) else 0) =
        ((w - A) - (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.single T 1) (w - A)) +
        (A - (permRep K (injTuples r) M).ρ.asAlgebraHom (MonoidAlgebra.single T 1) A -
          (if (∀ j : Fin r, j.1 < k + 1 → tupleVal u j ∈ tset τ)
            then Finsupp.single τ' (1 : K) else 0)) := by
      rw [map_sub]; abel
    rw [hsplit]
    exact Submodule.add_mem _ (hmono (Submodule.sub_mem _ hR hRT)) key


/-- `p` kills every vector supported on tuples that use a fresh label. -/
theorem pMap_supported_zero (h : t ≤ M) (k : ℕ) (v : (injTuples r).Rk M →₀ K)
    (hv : v ∈ Finsupp.supported K K (usesBins (t := t) k)) : pMap K r h v = 0 := by
  ext y
  simp only [pMap, Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.coe_zero,
    Pi.zero_apply]
  apply (Finsupp.mem_supported' K v).mp hv
  rintro ⟨j, _, hj⟩
  rw [tset_incl] at hj
  have := tset_lt y hj
  omega

/-- **The projector.** `p ∘ ρ(E_u) ∘ i` keeps exactly the tuples with the label set of `u`. -/
theorem projector (u τ : (injTuples r).Rk t) (h : t ≤ M) :
    pMap K r h ((permRep K (injTuples r) M).ρ.asAlgebraHom (partE hM u r)
        (iMap K r h (Finsupp.single τ 1))) =
      if tset u = tset τ then Finsupp.single τ (1 : K) else 0 := by
  classical
  have hinv := partE_invariant (K := K) hM u h r le_rfl τ
  rw [iMap_single]
  have hp := pMap_supported_zero (K := K) h r _ hinv
  rw [map_sub, sub_eq_zero] at hp
  rw [hp]
  have hiff : (∀ j : Fin r, j.1 < r → tupleVal u j ∈ tset τ) ↔ tset u = tset τ := by
    constructor
    · intro hall
      apply Finset.eq_of_subset_of_card_le
      · intro l hl
        obtain ⟨j, rfl⟩ := mem_tset.mp hl
        exact hall j j.2
      · rw [tset_card, tset_card]
    · intro heq j _
      rw [← heq]
      exact mem_tset.mpr ⟨j, rfl⟩
  by_cases hc : tset u = tset τ
  · rw [if_pos (hiff.mpr hc), if_pos hc, pMap_single_incl]
  · rw [if_neg (fun hh => hc (hiff.mp hh)), if_neg hc, map_zero]

/-- The projection intertwines the actions of `S_t ⊆ S_M`. -/
theorem pMap_action (h : t ≤ M) (g : Sfin t) (w : (injTuples r).Rk M →₀ K) :
    pMap K r h ((permRep K (injTuples r) M).ρ.asAlgebraHom
        (MonoidAlgebra.single (rankIncl h g) 1) w) =
      (permRep K (injTuples r) t).ρ.asAlgebraHom (MonoidAlgebra.single g 1) (pMap K r h w) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single σ c =>
    rw [action_single]
    by_cases hσ : σ ∈ Set.range (inclRk (injTuples r) h)
    · obtain ⟨τ, rfl⟩ := hσ
      have hsm : rankIncl h g • inclRk (injTuples r) h τ = inclRk (injTuples r) h (g • τ) :=
        (inclRk_smul (injTuples r) h g τ).symm
      rw [hsm, pMap_single_incl, pMap_single_incl, action_single]
    · have hσ' : rankIncl h g • σ ∉ Set.range (inclRk (injTuples r) h) := by
        rintro ⟨τ, hτ⟩
        apply hσ
        refine ⟨g⁻¹ • τ, ?_⟩
        rw [inclRk_smul (injTuples r) h g⁻¹ τ, hτ]
        change (rankIncl h g)⁻¹ • rankIncl h g • σ = σ
        rw [inv_smul_smul]
      rw [pMap_single_not _ hσ', pMap_single_not _ hσ, map_zero]

end Projector

/-! ### The compression theorem -/

section Compression
variable {K : Type} [Field K] {r t M : ℕ} (hM : t + r ≤ M)

theorem exists_mover (u v : (injTuples r).Rk t) : ∃ g : Sfin t, g • u = v := by
  obtain ⟨g, hg⟩ := exists_Sfin_map (tupleVal u) (tupleVal v) (tupleVal_injective u)
    (tupleVal_injective v) (tupleVal_lt u) (tupleVal_lt v)
  refine ⟨g, Subtype.ext (funext fun i => Fin.ext ?_)⟩
  change tupleVal (g • u) i = tupleVal v i
  rw [tupleVal_smul, hg]

include hM in
/-- **Compression.** Every position-equivariant endomorphism of `P_r(t)` is `p ∘ ρ(c) ∘ i`
for an actual group-algebra element `c` of `S_M`, whenever `t + r ≤ M`. -/
theorem compression (h : t ≤ M)
    (d : ((injTuples r).Rk t →₀ K) →ₗ[K] ((injTuples r).Rk t →₀ K))
    (hd : PosEquivariant K d) :
    ∃ c : MonoidAlgebra K (Sfin M),
      (pMap K r h).comp (((permRep K (injTuples r) M).ρ.asAlgebraHom c).comp
        (iMap K r h)) = d := by
  classical
  haveI : Fintype ((injTuples r).Rk t) := Fintype.ofFinite _
  choose gm hgm using fun u v : (injTuples r).Rk t => exists_mover u v
  let reps : Finset ((injTuples r).Rk t) := Finset.univ.filter (fun τ => posRep τ = τ)
  let c : MonoidAlgebra K (Sfin M) := ∑ u ∈ reps, ∑ v : (injTuples r).Rk t,
    (d (Finsupp.single u 1) v) • (MonoidAlgebra.single (rankIncl h (gm u v)) 1 * partE hM u r)
  refine ⟨c, ?_⟩
  apply Finsupp.lhom_ext
  intro τ c0
  have hc0 : Finsupp.single τ c0 = c0 • Finsupp.single τ (1 : K) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hc0, map_smul, map_smul]
  congr 1
  -- evaluate on the basis vector
  simp only [LinearMap.comp_apply, c, map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, map_mul, Module.End.mul_apply]
  simp only [pMap_action h, projector hM _ τ h]
  set u0 := posRep τ
  have hu0 : u0 ∈ reps := by
    simp only [reps, Finset.mem_filter, Finset.mem_univ, true_and]
    exact posRep_eq_of_tset _ _ (tset_posRep τ)
  rw [Finset.sum_eq_single u0]
  · obtain ⟨π, hπ⟩ := exists_pos_rep τ
    rw [if_pos (tset_posRep τ)]
    have hterm : ∀ v : (injTuples r).Rk t,
        (d (Finsupp.single u0 1) v) • (permRep K (injTuples r) t).ρ.asAlgebraHom
          (MonoidAlgebra.single (gm u0 v) 1) (Finsupp.single τ 1) =
        Finsupp.single (π • v) (d (Finsupp.single u0 1) v) := by
      intro v
      rw [action_single, ← hπ, smul_pos_comm, hgm, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [hterm]
    have hd' := congrArg (fun f => f (Finsupp.single u0 (1 : K))) (hd π)
    simp only [LinearMap.comp_apply, posLin_single] at hd'
    rw [← hπ]
    change _ = d (Finsupp.single (π • u0) 1)
    rw [hd']
    conv_rhs => rw [← Finsupp.univ_sum_single (d (Finsupp.single u0 1))]
    rw [map_sum]
    simp only [posLin_single]
  · intro u hu hne
    have hne' : tset u ≠ tset τ := by
      intro heq
      apply hne
      have h1 : posRep u = u := (Finset.mem_filter.mp hu).2
      rw [← h1]
      exact posRep_eq_of_tset _ _ heq
    rw [if_neg hne']
    simp
  · intro h0; exact absurd hu0 h0

end Compression
end ClaudeC017
