/-
Claude, 25 Sep 2026.  Formalisation of Cycle 017, part C: the position-equivariant auxiliary
inverse.

For `r < 2^a`, generic coefficients and characteristic two, there is a linear endomorphism `d`
of `P_r(n + 2^a)` that commutes with all permutations of tuple positions and satisfies
`z d z = z`.  The construction is Cycle 017's: `d = -(w⁻² · W · D)`, where `D` multiplies a
tuple by a function of its LABEL SET (which is what makes `d` position-equivariant).  The
algebra (`D z - z D = W`, `W z = z W`, `W^2 = w^2`) is Stage 5's `DegreeData` machinery, applied
to degree data pulled back from finite sets of labels to tuples.
-/
import C017Compression
import DegreeProfilesReview.ShiftedM5
import Mathlib.Algebra.Group.Action.Pointwise.Finset

set_option autoImplicit false
open CategoryTheory
open scoped Pointwise

namespace ClaudeC017
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open DegreeProfilesReview.ConcreteM5 DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.Del
open SelfContainedCycle003 SelfContainedCycle004

section SetData
variable {r t : ℕ}

/-- The label set of `g • τ` is the pointwise image of the label set. -/
theorem tset_smul' (g : Sfin t) (τ : (injTuples r).Rk t) : tset (g • τ) = g • tset τ := by
  rw [tset_smul, Finset.smul_finset_def]
  rfl

end SetData

section Degree
variable (K : Type) [Field K] [CharP K 2] (a n r : ℕ)

/-- Degree data on finite sets of labels (Stage 5's construction, for the pointwise action). -/
noncomputable def ddSet : DegreeData K (gen (blockφ 2 a n)) (Finset ℕ) :=
  degreeData (blockφ 2 a n) K

/-- The same degree data, pulled back to tuples through their label sets. -/
noncomputable def ddTup : DegreeData K (gen (blockφ 2 a n)) ((injTuples r).Rk (n + 2 ^ a)) where
  π τ := (ddSet K a n).π (tset τ)
  e i τ := (ddSet K a n).e i (tset τ)
  π_smul i τ := by
    rw [tset_smul']
    exact (ddSet K a n).π_smul i (tset τ)
  e_smul i k τ := by
    rw [tset_smul']
    exact (ddSet K a n).e_smul i k (tset τ)

end Degree

section Moves
variable {a n r : ℕ}

/-- A label of the block moves injectively under the block group. -/
theorem block_orbit_injective {l : ℕ} (hl : n ≤ l ∧ l < n + 2 ^ a) :
    Function.Injective (fun v : Fin a → ZMod 2 => (blockφ 2 a n (Multiplicative.ofAdd v)).1 l) := by
  intro v v' hvv
  simp only at hvv
  change blockHom 2 a n (Multiplicative.ofAdd v) l = blockHom 2 a n (Multiplicative.ofAdd v') l
    at hvv
  rw [blockHom_apply_block 2 a n _ hl, blockHom_apply_block 2 a n _ hl] at hvv
  have h1 := (blockEquiv 2 a n).injective (Subtype.ext hvv)
  exact Multiplicative.ofAdd.injective (mul_right_cancel h1)

/-- A tuple with a block label has a label set moved by the block group (`r < 2^a`). -/
theorem tset_moved (hr : r < 2 ^ a) (τ : (injTuples r).Rk (n + 2 ^ a))
    (hact : ∃ j, n ≤ tupleVal τ j) :
    ∃ v : Fin a → ZMod 2, blockφ 2 a n (Multiplicative.ofAdd v) • tset τ ≠ tset τ := by
  by_contra hno
  push_neg at hno
  obtain ⟨j, hj⟩ := hact
  set l := tupleVal τ j
  have hl : n ≤ l ∧ l < n + 2 ^ a := ⟨hj, tupleVal_lt τ j⟩
  have hlS : l ∈ tset τ := mem_tset.mpr ⟨j, rfl⟩
  have hmaps : ∀ v ∈ (Finset.univ : Finset (Fin a → ZMod 2)),
      (blockφ 2 a n (Multiplicative.ofAdd v)).1 l ∈ tset τ := by
    intro v _
    rw [← hno v]
    exact Finset.smul_mem_smul_finset hlS
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ) (t := tset τ)
    (fun v : Fin a → ZMod 2 => (blockφ 2 a n (Multiplicative.ofAdd v)).1 l)
    (fun v _ => Finset.mem_coe.mpr (hmaps v (Finset.mem_univ v))) ((block_orbit_injective hl).injOn)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, tset_card] at hcard
  omega

/-- A tuple of retained labels is fixed by the block generators. -/
theorem gen_fixes (τ : (injTuples r).Rk (n + 2 ^ a)) (hin : ∀ j, tupleVal τ j < n) (i : Fin a) :
    gen (blockφ 2 a n) i • τ = τ := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  change tupleVal (gen (blockφ 2 a n) i • τ) j = tupleVal τ j
  rw [tupleVal_smul]
  change blockHom 2 a n _ (tupleVal τ j) = tupleVal τ j
  exact blockHom_apply_not_block 2 a n _ (by have := hin j; omega)

end Moves

section Inverse
variable {K : Type} [Field K] [CharP K 2] {a n r : ℕ}

omit [CharP K 2] in
/-- The trivial twist is the permutation representation. -/
theorem twist_trivial (t : ℕ) :
    twist (X := (injTuples r).Rk t) (Representation.trivial K (Sfin t) K) =
      Representation.ofMulAction K (Sfin t) ((injTuples r).Rk t) := by
  ext γ : 1
  apply Finsupp.lhom_ext
  intro x c
  rw [twist_single, Representation.ofMulAction_single]
  rfl

omit [CharP K 2] in
/-- A diagonal operator given by a position-invariant function commutes with positions. -/
theorem scal_posLin {t : ℕ} (f : (injTuples r).Rk t → K) (hf : ∀ (π : Equiv.Perm (Fin r)) τ, f (π • τ) = f τ)
    (π : Equiv.Perm (Fin r)) :
    (scal f : Module.End K ((injTuples r).Rk t →₀ K)) ∘ₗ posLin K π = posLin K π ∘ₗ scal f := by
  apply Finsupp.lhom_ext
  intro τ c
  rw [LinearMap.comp_apply, LinearMap.comp_apply, posLin_single, scal_single, scal_single,
    posLin_single, hf]

omit [CharP K 2] in
theorem twist_posLin {t : ℕ} (γ : Sfin t) (π : Equiv.Perm (Fin r)) :
    (twist (X := (injTuples r).Rk t) (Representation.trivial K (Sfin t) K) γ) ∘ₗ posLin K π =
      posLin K π ∘ₗ twist (X := (injTuples r).Rk t) (Representation.trivial K (Sfin t) K) γ := by
  apply Finsupp.lhom_ext
  intro τ c
  rw [LinearMap.comp_apply, LinearMap.comp_apply, posLin_single, twist_single, twist_single,
    posLin_single, smul_pos_comm]

/-- **The auxiliary inverse.** -/
theorem aux_inverse (c : Fin a → K) (hc : Generic 2 c) (hr : r < 2 ^ a) :
    ∃ d : Module.End K ((injTuples r).Rk (n + 2 ^ a) →₀ K), PosEquivariant K d ∧
      (zOp (σgen 2 a n) c (permRep K (injTuples r) (n + 2 ^ a)).ρ : Module.End K _) * d *
        zOp (σgen 2 a n) c (permRep K (injTuples r) (n + 2 ^ a)).ρ =
      zOp (σgen 2 a n) c (permRep K (injTuples r) (n + 2 ^ a)).ρ := by
  set t := n + 2 ^ a
  set σtriv := Representation.trivial K (Sfin t) K
  set s := gen (blockφ 2 a n)
  have hρ : (permRep K (injTuples r) t).ρ = twist (X := (injTuples r).Rk t) σtriv :=
    (twist_trivial t).symm
  have hsig : σgen 2 a n = s := rfl
  rw [hρ, hsig]
  set dd := ddTup K a n r
  set z : Module.End K ((injTuples r).Rk t →₀ K) := zOp s c (twist (X := (injTuples r).Rk t) σtriv)
  set D : Module.End K ((injTuples r).Rk t →₀ K) := scal dd.π
  set W : Module.End K ((injTuples r).Rk t →₀ K) := dd.W c σtriv
  set g : (injTuples r).Rk t → K := fun τ => (dd.w c τ ^ 2)⁻¹
  have hs : ∀ i k, s i * s k = s k * s i := gen_comm (blockφ 2 a n)
  have hp : ∀ i, s i ^ 2 = 1 := gen_pow (blockφ 2 a n)
  have hz2 : z * z = 0 := by
    have := zOp_pow_char (p := 2) c (twist (X := (injTuples r).Rk t) σtriv) hs hp
    rwa [pow_two] at this
  -- `w = 0` forces a retained tuple
  have hw0 : ∀ τ, dd.w c τ = 0 → ∀ i, s i • τ = τ := by
    intro τ hτ i
    by_cases hact : ∃ j, n ≤ tupleVal τ j
    · exfalso
      change (ddSet K a n).w c (tset τ) = 0 at hτ
      exact degreeData_w_ne_zero (blockφ 2 a n) (K := K) hc (tset_moved hr τ hact) hτ
    · push_neg at hact
      exact gen_fixes τ hact i
  refine ⟨-(scal g * W * D), ?_, ?_⟩
  · -- position equivariance
    intro π
    have hD : Commute (scal dd.π : Module.End K ((injTuples r).Rk t →₀ K)) (posLin K π) :=
      scal_posLin (K := K) dd.π (fun π τ => by
        change (ddSet K a n).π (tset (π • τ)) = (ddSet K a n).π (tset τ); rw [tset_pos]) π
    have hg : Commute (scal g : Module.End K ((injTuples r).Rk t →₀ K)) (posLin K π) :=
      scal_posLin (K := K) g (fun π τ => by
        change ((ddSet K a n).w c (tset (π • τ)) ^ 2)⁻¹ = ((ddSet K a n).w c (tset τ) ^ 2)⁻¹
        rw [tset_pos]) π
    have hW : Commute W (posLin K π) := by
      change Commute (∑ i, c i • (twist (X := (injTuples r).Rk t) σtriv (s i) * scal (dd.e i)))
        (posLin K π)
      apply Commute.sum_left
      intro i _
      apply Commute.smul_left
      apply Commute.mul_left
      · exact twist_posLin (K := K) (s i) π
      · exact scal_posLin (K := K) (dd.e i) (fun π τ => by
          change (ddSet K a n).e i (tset (π • τ)) = (ddSet K a n).e i (tset τ); rw [tset_pos]) π
    exact ((hg.mul_left hW).mul_left hD).neg_left.eq
  · -- `z d z = z`
    have hDz : D * z - z * D = W := dd.commutator c σtriv
    have hzDz : z * D * z = -(W * z) := by
      have h1 : z * D = D * z - W := by rw [← hDz]; abel
      rw [h1, sub_mul, mul_assoc, hz2, mul_zero, zero_sub]
    have hWz : Commute W z := dd.W_commute_zOp c σtriv hs
    have hgz : Commute (scal g : Module.End K ((injTuples r).Rk t →₀ K)) z :=
      scal_commute_zOp c σtriv (fun k τ => by
        change ((dd.w c (s k • τ)) ^ 2)⁻¹ = ((dd.w c τ) ^ 2)⁻¹
        rw [dd.w_smul])
    have hW2 : W * W = scal (dd.w c ^ 2) := by
      rcases subsingleton_or_nontrivial ((injTuples r).Rk t →₀ K) with hsub | hnt
      · exact Subsingleton.elim _ _
      · rw [← pow_two]
        exact dd.W_pow c σtriv hs hp
    have hmain : z * (-(scal g * W * D)) * z = scal (g * dd.w c ^ 2) * z := by
      have e1 : z * (-(scal g * W * D)) * z = -(z * (scal g * (W * (D * z)))) := by
        apply LinearMap.ext; intro m
        simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
      have e2 : z * (scal g * (W * (D * z))) = scal g * (z * (W * (D * z))) := by
        rw [← mul_assoc z (scal g), ← hgz.eq, mul_assoc]
      have e3 : z * (W * (D * z)) = W * (z * (D * z)) := by
        rw [← mul_assoc z W, ← hWz.eq, mul_assoc]
      have e4 : z * (D * z) = -(W * z) := by rw [← mul_assoc, hzDz]
      rw [e1, e2, e3, e4, ← scal_mul, ← hW2]
      apply LinearMap.ext; intro m
      simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]
    rw [hmain]
    apply LinearMap.ext
    intro m
    rw [Module.End.mul_apply]
    apply scal_eq_self
    intro τ hτ
    have hwτ : dd.w c τ ≠ 0 := by
      intro h0
      apply hτ
      rw [zOp_apply, Finsupp.finset_sum_apply]
      apply Finset.sum_eq_zero
      intro i _
      rw [Finsupp.smul_apply, Finsupp.sub_apply]
      have hfix := hw0 τ h0 i
      have := twist_smul_apply σtriv (s i) m τ
      rw [hfix] at this
      rw [this]
      simp [σtriv]
    rw [Pi.mul_apply, Pi.pow_apply]
    exact inv_mul_cancel₀ (pow_ne_zero _ hwτ)

end Inverse
end ClaudeC017
