/-
Claude, 25 Sep 2026.  Every prime characteristic, part C: the support induction for top-power
witnesses (Cycle 017's construction with `u = z^(p-1)` in place of `z`).

Over a finite field `F` of characteristic `p`, for generic `c`, every `r < p^a` and every
`n ≥ r(r+1)/2`, there is an actual group-algebra element `w` of `S_{n+p^a}` with
`u w u - u` in the tuple relations of support `r`.  The step is the characteristic-two step
verbatim, with the top-power auxiliary inverse of `PAuxiliary`.
-/
import C017Induction
import PTransfer

set_option autoImplicit false
open CategoryTheory

namespace ClaudeCP
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open DegreeProfilesReview.ConcreteM5 DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle007 SelfContainedCycle017
open ClaudeC017 ClaudeWitnessTransfer

/-! ### Rank zero -/

section RankZero
variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

theorem zEltP_rankZero (a n : ℕ) (c : Fin a → K) :
    (permRep K (injTuples 0) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c) = 0 := by
  rw [zEltP_action]
  unfold zOp
  apply Finset.sum_eq_zero
  intro i _
  rw [rankZero_rho (K := K) (σgen p a n i), sub_self, smul_zero]

theorem base_top_witness (a n : ℕ) (c : Fin a → K) : IsTopWitness p 0 a n c 0 := by
  intro b hb
  obtain rfl : b = 0 := by omega
  rw [mul_zero, zero_mul, zero_sub, map_neg, map_pow, zEltP_rankZero,
    zero_pow (by have := (Fact.out : p.Prime).two_le; omega), neg_zero]

end RankZero

/-! ### Moving the block of size `p^a` -/

section Conj
variable (p : ℕ) [Fact p.Prime] (a n' m : ℕ)

theorem move_blockHomP (v : ElemAb p a) (k : ℕ) :
    movePerm n' m (p ^ a) (blockHom p a n' v k) =
      blockHom p a (n' + m) v (movePerm n' m (p ^ a) k) := by
  change moveFun n' m (p ^ a) (blockHom p a n' v k) = blockHom p a (n' + m) v (moveFun n' m (p ^ a) k)
  by_cases hk : n' ≤ k ∧ k < n' + p ^ a
  · have hb := blockHom_mem_block p a n' v hk
    have e1 : moveFun n' m (p ^ a) k = k + m := by unfold moveFun; split_ifs <;> omega
    have e2 : moveFun n' m (p ^ a) (blockHom p a n' v k) = blockHom p a n' v k + m := by
      unfold moveFun; split_ifs <;> omega
    rw [e1, e2, blockHom_translate]
  · rw [blockHom_apply_not_block p a n' v hk]
    rw [blockHom_apply_not_block p a (n' + m) v]
    unfold moveFun; split_ifs <;> omega

variable {K : Type} [Field K]

theorem move_σgenP (h : n' + p ^ a ≤ n' + m + p ^ a) (i : Fin a) :
    MulAut.conj (⟨movePerm n' m (p ^ a), movePerm_mem n' m (p ^ a) (by omega)⟩ :
        Sfin (n' + m + p ^ a)) (rankIncl h (σgen p a n' i)) = σgen p a (n' + m) i := by
  apply Subtype.ext
  rw [MulAut.conj_apply]
  apply Equiv.ext
  intro k
  change movePerm n' m (p ^ a) ((blockHom p a n' _) ((movePerm n' m (p ^ a)).symm k)) =
    blockHom p a (n' + m) _ k
  rw [move_blockHomP, Equiv.apply_symm_apply]

theorem move_zEltP (h : n' + p ^ a ≤ n' + m + p ^ a) (c : Fin a → K) :
    conjugateAlgebra (⟨movePerm n' m (p ^ a), movePerm_mem n' m (p ^ a) (by omega)⟩ :
        Sfin (n' + m + p ^ a)) (MonoidAlgebra.mapDomainAlgHom K K (rankIncl h) (zEltP p a n' c)) =
      zEltP p a (n' + m) c := by
  simp only [zEltP, map_sum, map_smul, map_sub, map_one, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single]
  simp only [conjugateAlgebra, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single, move_σgenP]

end Conj

/-! ### The inductive step -/

section Step
variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- **One step, every prime.**  A support-`r` top-power witness at `n'` gives a
support-`(r+1)` top-power witness at `n' + (r+1)`. -/
theorem stepP (a : ℕ) (c : Fin a → F) (hc : Generic p c) (r n' : ℕ) (hr : r + 1 < p ^ a)
    (w' : MonoidAlgebra F (Sfin (n' + p ^ a))) (hw' : IsTopWitness p r a n' c w') :
    ∃ w : MonoidAlgebra F (Sfin (n' + (r + 1) + p ^ a)),
      IsTopWitness p (r + 1) a (n' + (r + 1)) c w := by
  have h : n' + p ^ a ≤ n' + (r + 1) + p ^ a := by omega
  have hM : n' + p ^ a + (r + 1) ≤ n' + (r + 1) + p ^ a := by omega
  set z' := zEltP p a n' c ^ (p - 1) with hz'
  -- normalisation inside the finite group algebra
  obtain ⟨k, -, hb⟩ := groupAlgebra_adjustment z' w'
  set b := adjusted z' w' k with hb_def
  have hsmall : ∀ j ≤ r, (permRep F (injTuples j) (n' + p ^ a)).ρ.asAlgebraHom (z' * b * z') =
      (permRep F (injTuples j) (n' + p ^ a)).ρ.asAlgebraHom z' := by
    intro j hj
    have h1 := hw' j hj
    rw [map_sub, sub_eq_zero] at h1
    have h2 := adjusted_preserves_representation
      (permRep F (injTuples j) (n' + p ^ a)).ρ.asAlgebraHom.toRingHom z' w'
      (by simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul] using h1) k
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul] using h2
  -- the residual lies in the support-r relations
  set y := SelfContainedCycle017.residual z' b with hy_def
  have hy : y ∈ TupleRelations F r (n' + p ^ a) := by
    intro j hj
    simp only [y, SelfContainedCycle017.residual, map_sub, hsmall j hj, sub_self]
  -- the top-power auxiliary inverse on P_{r+1}(n' + p^a)
  obtain ⟨d, hdpos, hd⟩ := top_inverse (K := F) (n := n') c hc hr
  have hyQ : (permRep F (injTuples (r + 1)) (n' + p ^ a)).ρ.asAlgebraHom y * d *
      (permRep F (injTuples (r + 1)) (n' + p ^ a)).ρ.asAlgebraHom y =
      (permRep F (injTuples (r + 1)) (n' + p ^ a)).ρ.asAlgebraHom y := by
    have e : (permRep F (injTuples (r + 1)) (n' + p ^ a)).ρ.asAlgebraHom y =
        SelfContainedCycle017.residual
          ((permRep F (injTuples (r + 1)) (n' + p ^ a)).ρ.asAlgebraHom z')
          ((permRep F (injTuples (r + 1)) (n' + p ^ a)).ρ.asAlgebraHom b) := by
      simp only [y, SelfContainedCycle017.residual, map_sub, map_mul]
    rw [e]
    apply residual_inner
    · simpa only [map_mul] using
        congrArg (permRep F (injTuples (r + 1)) (n' + p ^ a)).ρ.asAlgebraHom hb
    · rw [hz', map_pow, zEltP_action]; exact hd
  -- compression onto r+1 fresh labels
  obtain ⟨cc, hcc⟩ := compression hM h d hdpos
  set ι := MonoidAlgebra.mapDomainAlgHom F F (rankIncl h) with hι
  set Z := ι z' with hZ
  set B := ι b with hB
  set A := B + (1 - B * Z) * cc * (1 - Z * B) with hA_def
  have hYres : ι y = SelfContainedCycle017.residual Z B := by
    simp only [y, SelfContainedCycle017.residual, map_sub, map_mul, Z, B]
  have hA : Z * A * Z - Z ∈ TupleRelations F (r + 1) (n' + (r + 1) + p ^ a) := by
    intro j hj
    rw [map_sub, sub_eq_zero]
    have key : ∀ φ : MonoidAlgebra F (Sfin (n' + (r + 1) + p ^ a)) →ₐ[F] Module.End F
        ((permRep F (injTuples j) (n' + (r + 1) + p ^ a)).V),
        φ (ι y) * φ cc * φ (ι y) = φ (ι y) → φ (Z * A * Z) = φ Z := by
      intro φ hφ
      rw [hYres, show φ (SelfContainedCycle017.residual Z B) =
          SelfContainedCycle017.residual (φ Z) (φ B) by
        simp only [SelfContainedCycle017.residual, map_sub, map_mul]] at hφ
      have := residual_lift (φ Z) (φ B) (φ cc) hφ
      simpa only [A, map_mul, map_add, map_sub, map_one] using this
    apply key
    rcases Nat.lt_or_ge j (r + 1) with hj' | hj'
    · have hz0 : (permRep F (injTuples j) (n' + (r + 1) + p ^ a)).ρ.asAlgebraHom (ι y) = 0 :=
        lift_relations h r y hy j (by omega)
      rw [hz0, mul_zero]
    · obtain rfl : j = r + 1 := by omega
      exact compression_inner (iMap F (r + 1) h) (pMap F (r + 1) h) _ _ _ d
        (lift_eq_localised h y rfl hy) hcc hyQ
  -- relabel the block into place
  let u : Sfin (n' + (r + 1) + p ^ a) :=
    ⟨movePerm n' (r + 1) (p ^ a), movePerm_mem n' (r + 1) (p ^ a) (by omega)⟩
  refine ⟨conjugateAlgebra u A, ?_⟩
  have hmove : conjugateAlgebra u Z = zEltP p a (n' + (r + 1)) c ^ (p - 1) := by
    rw [hZ, hz', map_pow, map_pow, move_zEltP p a n' (r + 1) h c]
  unfold IsTopWitness
  rw [← hmove, ← map_mul, ← map_mul, ← map_sub]
  exact conjugate_relation u _ hA

/-- **Top-power witnesses over a finite field of characteristic `p`.** -/
theorem top_witness_exists (a : ℕ) (c : Fin a → F) (hc : Generic p c) :
    ∀ r, r < p ^ a → ∀ n, r * (r + 1) / 2 ≤ n → ∃ w, IsTopWitness p r a n c w := by
  intro r
  induction r with
  | zero => intro _ n _; exact ⟨0, base_top_witness a n c⟩
  | succ r ih =>
    intro hr n hn
    rw [budget] at hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + (r + 1) := ⟨n - (r + 1), by omega⟩
    obtain ⟨w', hw'⟩ := ih (by omega) n' (by omega)
    exact stepP a c hc r n' hr w' hw'

end Step
end ClaudeCP
