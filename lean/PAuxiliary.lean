/-
Claude, 25 Sep 2026.  Every prime characteristic, part A: the top-power auxiliary inverse and
purity on the tuple modules.

Fix a prime `p`, a field `K` of characteristic `p`, `q = p^a`, generic coefficients `c`, and
`z = Σ c_i (σ_i - 1)` for Stage 5's block generators.  On the tuple module `P_r(n + q)` with
`r < q` put `u = z^(p-1)`.

* `top_inverse`: there is a position-equivariant `d` with `u d u = u`.
* `tuple_pure`:  `ker z ∩ range z ⊆ range z^(p-1)` (Cycle 084's `PureTop z (p-1)`).

Both come from Stage 5's degree data, pulled back from label sets to tuples.  With
`D' = w^{-p} W^{p-1} D` one has `D' z - z D' = E`, where `E` is the identity on tuples that meet
the block and zero on the others, and `E` commutes with `D'`.  Hence
`z^k D'^k m = (-1)^k k! m` for `m ∈ ker z` supported on the moved tuples, and
`d = ((-1)^(p-1) (p-1)!)⁻¹ D'^(p-1)` works because every `z^(p-1) v` is such an `m`.
For `p = 2` this is Cycle 017's `d = -(w⁻² W D)`.
-/
import C017Auxiliary
import TopPowerProjection

set_option autoImplicit false
open CategoryTheory
open scoped Pointwise

namespace ClaudeCP
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open DegreeProfilesReview.ConcreteM5 DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.Del
open SelfContainedCycle003 SelfContainedCycle004
open ClaudeC017

/-! ### Degree data for the block of size `p^a` -/

section Degree
variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (a n r : ℕ)

noncomputable def ddSetP : DegreeData K (gen (blockφ p a n)) (Finset ℕ) :=
  degreeData (blockφ p a n) K

noncomputable def ddTupP : DegreeData K (gen (blockφ p a n)) ((injTuples r).Rk (n + p ^ a)) where
  π τ := (ddSetP p K a n).π (tset τ)
  e i τ := (ddSetP p K a n).e i (tset τ)
  π_smul i τ := by
    rw [tset_smul']
    exact (ddSetP p K a n).π_smul i (tset τ)
  e_smul i k τ := by
    rw [tset_smul']
    exact (ddSetP p K a n).e_smul i k (tset τ)

end Degree

/-! ### Moved and fixed tuples -/

section Moves
variable {p : ℕ} [Fact p.Prime] {a n r : ℕ}

theorem block_orbit_injectiveP {l : ℕ} (hl : n ≤ l ∧ l < n + p ^ a) :
    Function.Injective (fun v : Fin a → ZMod p => (blockφ p a n (Multiplicative.ofAdd v)).1 l) := by
  intro v v' hvv
  simp only at hvv
  change blockHom p a n (Multiplicative.ofAdd v) l = blockHom p a n (Multiplicative.ofAdd v') l
    at hvv
  rw [blockHom_apply_block p a n _ hl, blockHom_apply_block p a n _ hl] at hvv
  have h1 := (blockEquiv p a n).injective (Subtype.ext hvv)
  exact Multiplicative.ofAdd.injective (mul_right_cancel h1)

/-- A tuple with a block label has a label set moved by the block group (`r < p^a`). -/
theorem tset_movedP (hr : r < p ^ a) (τ : (injTuples r).Rk (n + p ^ a))
    (hact : ∃ j, n ≤ tupleVal τ j) :
    ∃ v : Fin a → ZMod p, blockφ p a n (Multiplicative.ofAdd v) • tset τ ≠ tset τ := by
  by_contra hno
  push_neg at hno
  obtain ⟨j, hj⟩ := hact
  set l := tupleVal τ j
  have hl : n ≤ l ∧ l < n + p ^ a := ⟨hj, tupleVal_lt τ j⟩
  have hlS : l ∈ tset τ := mem_tset.mpr ⟨j, rfl⟩
  have hmaps : ∀ v ∈ (Finset.univ : Finset (Fin a → ZMod p)),
      (blockφ p a n (Multiplicative.ofAdd v)).1 l ∈ tset τ := by
    intro v _
    rw [← hno v]
    exact Finset.smul_mem_smul_finset hlS
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ) (t := tset τ)
    (fun v : Fin a → ZMod p => (blockφ p a n (Multiplicative.ofAdd v)).1 l)
    (fun v _ => Finset.mem_coe.mpr (hmaps v (Finset.mem_univ v))) ((block_orbit_injectiveP hl).injOn)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, tset_card] at hcard
  omega

/-- A tuple of retained labels is fixed by the block generators. -/
theorem gen_fixesP (τ : (injTuples r).Rk (n + p ^ a)) (hin : ∀ j, tupleVal τ j < n) (i : Fin a) :
    gen (blockφ p a n) i • τ = τ := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  change tupleVal (gen (blockφ p a n) i • τ) j = tupleVal τ j
  rw [tupleVal_smul]
  change blockHom p a n _ (tupleVal τ j) = tupleVal τ j
  exact blockHom_apply_not_block p a n _ (by have := hin j; omega)

end Moves

/-! ### The top-power inverse and purity -/

section TopPower
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] {a n r : ℕ}

/-- The common algebra: `w = 0` only at fixed tuples, the range of `z` avoids them, and
`D' z - z D' = E` with `E` the indicator of the moved tuples. -/
theorem top_setup (c : Fin a → K) (hc : Generic p c) (hr : r < p ^ a) :
    let t := n + p ^ a
    let σtriv := Representation.trivial K (Sfin t) K
    let s := gen (blockφ p a n)
    let dd := ddTupP p K a n r
    let z : Module.End K ((injTuples r).Rk t →₀ K) :=
      zOp s c (twist (X := (injTuples r).Rk t) σtriv)
    let g : (injTuples r).Rk t → K := fun τ => (dd.w c τ ^ p)⁻¹
    let ind : (injTuples r).Rk t → K := g * dd.w c ^ p
    let D' : Module.End K ((injTuples r).Rk t →₀ K) :=
      scal g * dd.W c σtriv ^ (p - 1) * scal dd.π
    z ^ p = 0 ∧
    (∀ τ, dd.w c τ = 0 → ∀ i, s i • τ = τ) ∧
    (∀ v τ, dd.w c τ = 0 → (z v) τ = 0) ∧
    D' * z - z * D' = scal ind ∧
    Commute (scal ind : Module.End K ((injTuples r).Rk t →₀ K)) D' ∧
    (∀ τ, dd.w c τ ≠ 0 → ind τ = 1) := by
  intro t σtriv s dd z g ind D'
  have hs : ∀ i k, s i * s k = s k * s i := gen_comm (blockφ p a n)
  have hp : ∀ i, s i ^ p = 1 := gen_pow (blockφ p a n)
  have hw0 : ∀ τ, dd.w c τ = 0 → ∀ i, s i • τ = τ := by
    intro τ hτ i
    by_cases hact : ∃ j, n ≤ tupleVal τ j
    · exfalso
      change (ddSetP p K a n).w c (tset τ) = 0 at hτ
      exact degreeData_w_ne_zero (blockφ p a n) (K := K) hc (tset_movedP hr τ hact) hτ
    · push_neg at hact
      exact gen_fixesP τ hact i
  have hzero : ∀ v τ, dd.w c τ = 0 → (z v) τ = 0 := by
    intro v τ h0
    change (zOp s c (twist (X := (injTuples r).Rk t) σtriv) v) τ = 0
    rw [zOp_apply, Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.smul_apply, Finsupp.sub_apply]
    have hfix := hw0 τ h0 i
    have := twist_smul_apply σtriv (s i) v τ
    rw [hfix] at this
    rw [this]
    simp [σtriv]
  have hzp : z ^ p = 0 := zOp_pow_char c (twist (X := (injTuples r).Rk t) σtriv) hs hp
  have hginv : ∀ k x, g (s k • x) = g x := fun k x => by
    change (dd.w c (s k • x) ^ p)⁻¹ = (dd.w c x ^ p)⁻¹
    rw [dd.w_smul]
  have hindinv : ∀ k x, ind (s k • x) = ind x := fun k x => by
    change g (s k • x) * dd.w c (s k • x) ^ p = g x * dd.w c x ^ p
    rw [hginv, dd.w_smul]
  refine ⟨hzp, hw0, hzero, ?_, ?_, ?_⟩
  · rcases subsingleton_or_nontrivial ((injTuples r).Rk t →₀ K) with hsub | hnt
    · exact Subsingleton.elim _ _
    set V : Module.End K ((injTuples r).Rk t →₀ K) := scal g * dd.W c σtriv ^ (p - 1) with hV
    have hpp : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos
    have hVW : V * dd.W c σtriv = scal ind := by
      rw [hV, mul_assoc, ← pow_succ, hpp, dd.W_pow c σtriv hs hp, scal_mul]
    have hVz : Commute V z :=
      (scal_commute_zOp c σtriv hginv).mul_left ((dd.W_commute_zOp c σtriv hs).pow_left _)
    have h1 : z * (V * scal dd.π) = V * (z * scal dd.π) := by
      rw [← mul_assoc, ← hVz.eq, mul_assoc]
    change V * scal dd.π * z - z * (V * scal dd.π) = scal ind
    rw [h1, mul_assoc, ← mul_sub, dd.commutator c σtriv, hVW]
  · apply Commute.mul_right
    · exact (scal_commute _ _).mul_right ((dd.scal_commute_W c σtriv hs hindinv).pow_right _)
    · exact scal_commute _ _
  · intro τ hτ
    change (dd.w c τ ^ p)⁻¹ * dd.w c τ ^ p = 1
    exact inv_mul_cancel₀ (pow_ne_zero _ hτ)

/-- **Purity on the tuple modules** (`r < p^a`, generic `c`): `ker z ∩ range z ⊆ range z^(p-1)`. -/
theorem tuple_pure (c : Fin a → K) (hc : Generic p c) (hr : r < p ^ a) :
    SelfContainedCycle084.PureTop
      (zOp (σgen p a n) c (permRep K (injTuples r) (n + p ^ a)).ρ) (p - 1) := by
  obtain ⟨-, -, hzero, -, -, -⟩ := top_setup (n := n) c hc hr
  set t := n + p ^ a
  set σtriv := Representation.trivial K (Sfin t) K
  have hρ : (permRep K (injTuples r) t).ρ = twist (X := (injTuples r).Rk t) σtriv :=
    (twist_trivial t).symm
  have hsig : σgen p a n = gen (blockφ p a n) := rfl
  rw [hρ, hsig]
  intro v hv hrange
  obtain ⟨x, rfl⟩ := hrange
  apply mem_range_pow_of_degreeData c σtriv (ddTupP p K a n r) (gen_comm (blockφ p a n))
    (gen_pow (blockφ p a n)) hv
  intro τ hτ h0
  exact hτ (hzero x τ h0)

/-- **The top-power auxiliary inverse** (`r < p^a`, generic `c`). -/
theorem top_inverse (c : Fin a → K) (hc : Generic p c) (hr : r < p ^ a) :
    ∃ d : Module.End K ((injTuples r).Rk (n + p ^ a) →₀ K), PosEquivariant K d ∧
      (zOp (σgen p a n) c (permRep K (injTuples r) (n + p ^ a)).ρ : Module.End K _) ^ (p - 1) * d *
        zOp (σgen p a n) c (permRep K (injTuples r) (n + p ^ a)).ρ ^ (p - 1) =
      zOp (σgen p a n) c (permRep K (injTuples r) (n + p ^ a)).ρ ^ (p - 1) := by
  obtain ⟨hzp, -, hzero, hcomm, hED, hind⟩ := top_setup (n := n) c hc hr
  set t := n + p ^ a
  set σtriv := Representation.trivial K (Sfin t) K
  set s := gen (blockφ p a n)
  set dd := ddTupP p K a n r
  have hρ : (permRep K (injTuples r) t).ρ = twist (X := (injTuples r).Rk t) σtriv :=
    (twist_trivial t).symm
  have hsig : σgen p a n = s := rfl
  rw [hρ, hsig]
  set z : Module.End K ((injTuples r).Rk t →₀ K) := zOp s c (twist (X := (injTuples r).Rk t) σtriv)
  set g : (injTuples r).Rk t → K := fun τ => (dd.w c τ ^ p)⁻¹
  set D' : Module.End K ((injTuples r).Rk t →₀ K) :=
    scal g * dd.W c σtriv ^ (p - 1) * scal dd.π
  set κ : K := (-1 : K) ^ (p - 1) * ((p - 1).factorial : K)
  have hκ : κ ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    have hpr : p.Prime := Fact.out
    rw [Ne, CharP.cast_eq_zero_iff K p, hpr.dvd_factorial]
    have := hpr.pos
    omega
  refine ⟨κ⁻¹ • D' ^ (p - 1), ?_, ?_⟩
  · -- position equivariance
    intro π
    have hD : Commute (scal dd.π : Module.End K ((injTuples r).Rk t →₀ K)) (posLin K π) :=
      scal_posLin (K := K) dd.π (fun π τ => by
        change (ddSetP p K a n).π (tset (π • τ)) = (ddSetP p K a n).π (tset τ); rw [tset_pos]) π
    have hg : Commute (scal g : Module.End K ((injTuples r).Rk t →₀ K)) (posLin K π) :=
      scal_posLin (K := K) g (fun π τ => by
        change ((ddSetP p K a n).w c (tset (π • τ)) ^ p)⁻¹ = ((ddSetP p K a n).w c (tset τ) ^ p)⁻¹
        rw [tset_pos]) π
    have hW : Commute (dd.W c σtriv) (posLin K π) := by
      change Commute (∑ i, c i • (twist (X := (injTuples r).Rk t) σtriv (s i) * scal (dd.e i)))
        (posLin K π)
      apply Commute.sum_left
      intro i _
      apply Commute.smul_left
      apply Commute.mul_left
      · exact twist_posLin (K := K) (s i) π
      · exact scal_posLin (K := K) (dd.e i) (fun π τ => by
          change (ddSetP p K a n).e i (tset (π • τ)) = (ddSetP p K a n).e i (tset τ)
          rw [tset_pos]) π
    have hD' : Commute D' (posLin K π) := ((hg.mul_left (hW.pow_left _)).mul_left hD)
    exact ((hD'.pow_left _).smul_left κ⁻¹).eq
  · -- `u d u = u`
    apply LinearMap.ext
    intro v
    set m := (z ^ (p - 1)) v with hm
    have hzm : z m = 0 := by
      rw [hm, ← Module.End.mul_apply, ← pow_succ',
        Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le, hzp, LinearMap.zero_apply]
    have hEm : scal (g * dd.w c ^ p) m = m := by
      apply scal_eq_self
      intro τ hτ
      apply hind
      intro h0
      apply hτ
      have hp1 : p - 1 = (p - 1 - 1) + 1 := by
        have := (Fact.out : p.Prime).two_le; omega
      rw [hm, hp1, pow_succ', Module.End.mul_apply]
      exact hzero _ τ h0
    have key := DegreeProfilesReview.Shifted.pow_pow_apply_of_commutator hcomm hED hzm hEm (p - 1)
    rw [Module.End.mul_apply, Module.End.mul_apply, ← hm, LinearMap.smul_apply, map_smul, key,
      smul_smul, inv_mul_cancel₀ hκ, one_smul]

end TopPower
end ClaudeCP
