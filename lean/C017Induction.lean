/-
Claude, 25 Sep 2026.  Formalisation of Cycle 017, part D: the induction on the support.

Over a finite field `F` of characteristic two, for generic coefficients `c`, every support
`r < 2^a` and every `n ≥ r(r+1)/2`, there is an actual group-algebra element `w` of
`S_{n+2^a}` with `z w z - z` in the tuple relations of support `r`.  The step `r → r+1`
normalises the previous witness (finite ring), splits off the residual, localises it to
the old labels, inverts it there by compressing the position-equivariant auxiliary inverse
onto `r+1` fresh labels, corrects, and finally relabels the block into place.
-/
import C017Auxiliary
import ClaudeWitnessTransfer
import FiniteGroupAlgebra

set_option autoImplicit false
open CategoryTheory

namespace ClaudeC017
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open DegreeProfilesReview.ConcreteM5 DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle007 SelfContainedCycle017
open ClaudeWitnessTransfer

/-! ### `S_t` is finite -/

instance Sfin_finite (t : ℕ) : Finite (Sfin t) := by
  refine Finite.of_injective
    (fun g : Sfin t => fun i : Fin t => (⟨g.1 i, Sfin_lt g.2 i.2⟩ : Fin t)) ?_
  intro g g' hgg'
  apply Subtype.ext
  apply Equiv.ext
  intro k
  by_cases hk : k < t
  · have := congrArg (fun f => (f ⟨k, hk⟩ : Fin t).val) hgg'
    exact this
  · rw [g.2 k (by omega), g'.2 k (by omega)]

/-! ### Rank zero -/

section RankZero
variable {K : Type} [Field K]

theorem rankZero_smul {t : ℕ} (g : Sfin t) (τ : (injTuples 0).Rk t) : g • τ = τ := by
  apply (injTuples 0).up_inj t
  apply Subtype.ext
  funext i
  exact i.elim0

theorem rankZero_rho {t : ℕ} (g : Sfin t) :
    (permRep K (injTuples 0) t).ρ g = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro τ c
  change Representation.ofMulAction K (Sfin t) _ g (Finsupp.single τ c) = _
  rw [Representation.ofMulAction_single, rankZero_smul]
  rfl

theorem zElt_rankZero (a n : ℕ) (c : Fin a → K) :
    (permRep K (injTuples 0) (n + 2 ^ a)).ρ.asAlgebraHom (zElt a n c) = 0 := by
  rw [zElt_action]
  unfold zOp
  apply Finset.sum_eq_zero
  intro i _
  rw [rankZero_rho (K := K) (σgen 2 a n i), sub_self, smul_zero]

theorem base_witness (a n : ℕ) (c : Fin a → K) : IsTupleInnerInverse 0 a n c 0 := by
  intro b hb
  obtain rfl : b = 0 := by omega
  rw [mul_zero, zero_mul, zero_sub, map_neg, zElt_rankZero, neg_zero]

end RankZero

/-! ### Moving the block -/

section Move
variable (p a : ℕ) [Fact p.Prime]

/-- Translating the block by `m` translates the block action. -/
theorem blockHom_translate (n m : ℕ) (v : ElemAb p a) (k : ℕ) :
    blockHom p a (n + m) v (k + m) = blockHom p a n v k + m := by
  by_cases hk : n ≤ k ∧ k < n + p ^ a
  · have hk' : n + m ≤ k + m ∧ k + m < n + m + p ^ a := by omega
    rw [blockHom_apply_block p a (n + m) v hk', blockHom_apply_block p a n v hk]
    simp only [blockEquiv, Equiv.trans_apply, Equiv.symm_trans_apply, finBlockEquiv,
      Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    have : k + m - (n + m) = k - n := by omega
    simp only [this]
    omega
  · rw [blockHom_apply_not_block p a (n + m) v (by omega), blockHom_apply_not_block p a n v hk]

theorem blockHom_mem_block (n : ℕ) (v : ElemAb p a) {k : ℕ} (hk : n ≤ k ∧ k < n + p ^ a) :
    n ≤ blockHom p a n v k ∧ blockHom p a n v k < n + p ^ a := by
  rw [blockHom_apply_block p a n v hk]
  exact (blockEquiv p a n _).2

end Move

section MovePerm
variable (n' m q : ℕ)

/-- The relabelling that moves the block `[n', n'+q)` up by `m` and the `m` labels
`[n'+q, n'+q+m)` down to `[n', n'+m)`. -/
def moveFun (k : ℕ) : ℕ :=
  if k < n' then k else if k < n' + q then k + m else if k < n' + q + m then k - q else k

def moveInv (k : ℕ) : ℕ :=
  if k < n' then k else if k < n' + m then k + q else if k < n' + q + m then k - m else k

def movePerm : Equiv.Perm ℕ where
  toFun := moveFun n' m q
  invFun := moveInv n' m q
  left_inv k := by
    unfold moveFun moveInv
    split_ifs <;> omega
  right_inv k := by
    unfold moveFun moveInv
    split_ifs <;> omega

theorem movePerm_mem {N : ℕ} (hN : n' + q + m ≤ N) : movePerm n' m q ∈ Sfin N := by
  intro k hk
  change moveFun n' m q k = k
  unfold moveFun
  split_ifs <;> omega

end MovePerm

section Conj
variable (a n' m : ℕ)

theorem move_blockHom (v : ElemAb 2 a) (k : ℕ) :
    movePerm n' m (2 ^ a) (blockHom 2 a n' v k) = blockHom 2 a (n' + m) v (movePerm n' m (2 ^ a) k) := by
  change moveFun n' m (2 ^ a) (blockHom 2 a n' v k) = blockHom 2 a (n' + m) v (moveFun n' m (2 ^ a) k)
  by_cases hk : n' ≤ k ∧ k < n' + 2 ^ a
  · have hb := blockHom_mem_block 2 a n' v hk
    have e1 : moveFun n' m (2 ^ a) k = k + m := by unfold moveFun; split_ifs <;> omega
    have e2 : moveFun n' m (2 ^ a) (blockHom 2 a n' v k) = blockHom 2 a n' v k + m := by
      unfold moveFun; split_ifs <;> omega
    rw [e1, e2, blockHom_translate]
  · rw [blockHom_apply_not_block 2 a n' v hk]
    rw [blockHom_apply_not_block 2 a (n' + m) v]
    unfold moveFun; split_ifs <;> omega

variable {K : Type} [Field K]

/-- The relabelling carries the old block generators to the new ones. -/
theorem move_σgen (h : n' + 2 ^ a ≤ n' + m + 2 ^ a) (i : Fin a) :
    MulAut.conj (⟨movePerm n' m (2 ^ a), movePerm_mem n' m (2 ^ a) (by omega)⟩ :
        Sfin (n' + m + 2 ^ a)) (rankIncl h (σgen 2 a n' i)) = σgen 2 a (n' + m) i := by
  apply Subtype.ext
  rw [MulAut.conj_apply]
  apply Equiv.ext
  intro k
  change movePerm n' m (2 ^ a) ((blockHom 2 a n' _) ((movePerm n' m (2 ^ a)).symm k)) =
    blockHom 2 a (n' + m) _ k
  rw [move_blockHom, Equiv.apply_symm_apply]

theorem move_zElt (h : n' + 2 ^ a ≤ n' + m + 2 ^ a) (c : Fin a → K) :
    conjugateAlgebra (⟨movePerm n' m (2 ^ a), movePerm_mem n' m (2 ^ a) (by omega)⟩ :
        Sfin (n' + m + 2 ^ a)) (MonoidAlgebra.mapDomainAlgHom K K (rankIncl h) (zElt a n' c)) =
      zElt a (n' + m) c := by
  simp only [zElt, map_sum, map_smul, map_sub, map_one, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single]
  simp only [conjugateAlgebra, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single, move_σgen]

end Conj

/-! ### The inductive step -/

section Step
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- **One step of Cycle 017.**  A support-`r` witness at `n'` gives a support-`(r+1)` witness
at `n' + (r+1)`. -/
theorem step (a : ℕ) (c : Fin a → F) (hc : Generic 2 c) (r n' : ℕ) (hr : r + 1 < 2 ^ a)
    (w' : MonoidAlgebra F (Sfin (n' + 2 ^ a))) (hw' : IsTupleInnerInverse r a n' c w') :
    ∃ w : MonoidAlgebra F (Sfin (n' + (r + 1) + 2 ^ a)),
      IsTupleInnerInverse (r + 1) a (n' + (r + 1)) c w := by
  have h : n' + 2 ^ a ≤ n' + (r + 1) + 2 ^ a := by omega
  have hM : n' + 2 ^ a + (r + 1) ≤ n' + (r + 1) + 2 ^ a := by omega
  set z' := zElt a n' c with hz'
  -- normalisation inside the finite group algebra
  obtain ⟨k, -, hb⟩ := groupAlgebra_adjustment z' w'
  set b := adjusted z' w' k with hb_def
  have hsmall : ∀ j ≤ r, (permRep F (injTuples j) (n' + 2 ^ a)).ρ.asAlgebraHom (z' * b * z') =
      (permRep F (injTuples j) (n' + 2 ^ a)).ρ.asAlgebraHom z' := by
    intro j hj
    have h1 := hw' j hj
    rw [map_sub, sub_eq_zero] at h1
    have h2 := adjusted_preserves_representation
      (permRep F (injTuples j) (n' + 2 ^ a)).ρ.asAlgebraHom.toRingHom z' w'
      (by simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul] using h1) k
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul] using h2
  -- the residual lies in the support-r relations
  set y := SelfContainedCycle017.residual z' b with hy_def
  have hy : y ∈ TupleRelations F r (n' + 2 ^ a) := by
    intro j hj
    simp only [y, SelfContainedCycle017.residual, map_sub, hsmall j hj, sub_self]
  -- the auxiliary inverse on P_{r+1}(n' + 2^a) and the residual inner identity there
  obtain ⟨d, hdpos, hd⟩ := aux_inverse (K := F) (n := n') c hc hr
  have hyQ : (permRep F (injTuples (r + 1)) (n' + 2 ^ a)).ρ.asAlgebraHom y * d *
      (permRep F (injTuples (r + 1)) (n' + 2 ^ a)).ρ.asAlgebraHom y =
      (permRep F (injTuples (r + 1)) (n' + 2 ^ a)).ρ.asAlgebraHom y := by
    have e : (permRep F (injTuples (r + 1)) (n' + 2 ^ a)).ρ.asAlgebraHom y =
        SelfContainedCycle017.residual ((permRep F (injTuples (r + 1)) (n' + 2 ^ a)).ρ.asAlgebraHom z')
          ((permRep F (injTuples (r + 1)) (n' + 2 ^ a)).ρ.asAlgebraHom b) := by
      simp only [y, SelfContainedCycle017.residual, map_sub, map_mul]
    rw [e]
    apply residual_inner
    · simpa only [map_mul] using congrArg (permRep F (injTuples (r + 1)) (n' + 2 ^ a)).ρ.asAlgebraHom hb
    · rw [hz', zElt_action]; exact hd
  -- compression onto r+1 fresh labels
  obtain ⟨cc, hcc⟩ := compression hM h d hdpos
  set ι := MonoidAlgebra.mapDomainAlgHom F F (rankIncl h) with hι
  set Z := ι z' with hZ
  set B := ι b with hB
  set A := B + (1 - B * Z) * cc * (1 - Z * B) with hA_def
  have hYres : ι y = SelfContainedCycle017.residual Z B := by
    simp only [y, SelfContainedCycle017.residual, map_sub, map_mul, Z, B]
  have hA : Z * A * Z - Z ∈ TupleRelations F (r + 1) (n' + (r + 1) + 2 ^ a) := by
    intro j hj
    rw [map_sub, sub_eq_zero]
    have key : ∀ φ : MonoidAlgebra F (Sfin (n' + (r + 1) + 2 ^ a)) →ₐ[F] Module.End F
        ((permRep F (injTuples j) (n' + (r + 1) + 2 ^ a)).V),
        φ (ι y) * φ cc * φ (ι y) = φ (ι y) → φ (Z * A * Z) = φ Z := by
      intro φ hφ
      rw [hYres, show φ (SelfContainedCycle017.residual Z B) = SelfContainedCycle017.residual (φ Z) (φ B) by
        simp only [SelfContainedCycle017.residual, map_sub, map_mul]] at hφ
      have := residual_lift (φ Z) (φ B) (φ cc) hφ
      simpa only [A, map_mul, map_add, map_sub, map_one] using this
    apply key
    rcases Nat.lt_or_ge j (r + 1) with hj' | hj'
    · have hz0 : (permRep F (injTuples j) (n' + (r + 1) + 2 ^ a)).ρ.asAlgebraHom (ι y) = 0 :=
        lift_relations h r y hy j (by omega)
      rw [hz0, mul_zero]
    · obtain rfl : j = r + 1 := by omega
      exact compression_inner (iMap F (r + 1) h) (pMap F (r + 1) h) _ _ _ d
        (lift_eq_localised h y rfl hy) hcc hyQ
  -- relabel the block into place
  let u : Sfin (n' + (r + 1) + 2 ^ a) :=
    ⟨movePerm n' (r + 1) (2 ^ a), movePerm_mem n' (r + 1) (2 ^ a) (by omega)⟩
  refine ⟨conjugateAlgebra u A, ?_⟩
  have hmove : conjugateAlgebra u Z = zElt a (n' + (r + 1)) c := move_zElt a n' (r + 1) h c
  unfold IsTupleInnerInverse
  rw [← hmove, ← map_mul, ← map_mul, ← map_sub]
  exact conjugate_relation u _ hA

/-- The triangular budget. -/
theorem budget (r : ℕ) : (r + 1) * (r + 1 + 1) / 2 = r * (r + 1) / 2 + (r + 1) := by
  have e : (r + 1) * (r + 1 + 1) = r * (r + 1) + 2 * (r + 1) := by ring
  rw [e, Nat.add_mul_div_left _ _ two_pos]

/-- **Cycle 017, finite-field form.** -/
theorem witness_exists (a : ℕ) (c : Fin a → F) (hc : Generic 2 c) :
    ∀ r, r < 2 ^ a → ∀ n, r * (r + 1) / 2 ≤ n → ∃ w, IsTupleInnerInverse r a n c w := by
  intro r
  induction r with
  | zero => intro _ n _; exact ⟨0, base_witness a n c⟩
  | succ r ih =>
    intro hr n hn
    rw [budget] at hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + (r + 1) := ⟨n - (r + 1), by omega⟩
    obtain ⟨w', hw'⟩ := ih (by omega) n' (by omega)
    exact step a c hc r n' hr w' hw'

end Step
end ClaudeC017
