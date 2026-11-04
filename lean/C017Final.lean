/-
Claude, 25 Sep 2026.  Formalisation of Cycle 017, part E: base change and the unconditional
characteristic-two classification.

The finite-field witnesses of `C017Induction` are carried along an embedding
`GaloisField 2 a → L` into any algebraically closed field `L` of characteristic two.  This
discharges `WitnessHypothesis L (fun r => r(r+1)/2)` with no hypotheses, and hence the Stage 5
T1–T4 classification (for both PC and NS) holds for every template over every field of
characteristic two, with the T2 profiles bounded below by `(⌊√n⌋ - s - 1)/k`.
-/
import C017Induction

set_option autoImplicit false
open CategoryTheory

namespace ClaudeC017
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open DegreeProfilesReview.ConcreteM5 DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.Profiles
open SelfContainedCycle003 SelfContainedCycle004
open ClaudeWitnessTransfer

/-! ### Changing the coefficient field -/

section BaseChange
variable {F L : Type} [Field F] [Field L] (φ : F →+* L)

theorem mapRange_smul_alg {N : ℕ} (k : F) (x : MonoidAlgebra F (Sfin N)) :
    MonoidAlgebra.mapRangeRingHom (Sfin N) φ (k • x) =
      φ k • MonoidAlgebra.mapRangeRingHom (Sfin N) φ x := by
  ext m
  simp [MonoidAlgebra.mapRangeRingHom_apply]

theorem rho_mapRange {b N : ℕ} (x : MonoidAlgebra F (Sfin N)) (τ : (injTuples b).Rk N) :
    (permRep L (injTuples b) N).ρ.asAlgebraHom (MonoidAlgebra.mapRangeRingHom (Sfin N) φ x)
        (Finsupp.single τ 1) =
      Finsupp.mapRange φ φ.map_zero
        ((permRep F (injTuples b) N).ρ.asAlgebraHom x (Finsupp.single τ 1)) := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRangeRingHom_single, map_one,
      Representation.asAlgebraHom_single, one_smul]
    change Representation.ofMulAction L (Sfin N) _ g (Finsupp.single τ 1) =
      Finsupp.mapRange φ φ.map_zero (Representation.ofMulAction F (Sfin N) _ g (Finsupp.single τ 1))
    rw [Representation.ofMulAction_single, Representation.ofMulAction_single,
      Finsupp.mapRange_single, map_one]
  | hadd x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]
    ext m
    simp
  | hsmul k x hx =>
    rw [mapRange_smul_alg, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hx]
    ext m
    simp

theorem tupleRelations_map {r N : ℕ} {x : MonoidAlgebra F (Sfin N)}
    (hx : x ∈ TupleRelations F r N) :
    MonoidAlgebra.mapRangeRingHom (Sfin N) φ x ∈ TupleRelations L r N := by
  intro b hb
  apply Finsupp.lhom_ext
  intro τ c
  have hc : Finsupp.single τ c = c • Finsupp.single τ (1 : L) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hc, LinearMap.map_smul, rho_mapRange, hx b hb]
  simp

theorem zElt_map (a n : ℕ) (c : Fin a → F) :
    MonoidAlgebra.mapRangeRingHom (Sfin (n + 2 ^ a)) φ (zElt a n c) = zElt a n (φ ∘ c) := by
  simp only [zElt, map_sum, mapRange_smul_alg, map_sub, map_one,
    MonoidAlgebra.mapRangeRingHom_single, Function.comp_apply]

theorem innerInverse_map {r a n : ℕ} {c : Fin a → F} {w : MonoidAlgebra F (Sfin (n + 2 ^ a))}
    (hw : IsTupleInnerInverse r a n c w) :
    IsTupleInnerInverse r a n (φ ∘ c) (MonoidAlgebra.mapRangeRingHom (Sfin (n + 2 ^ a)) φ w) := by
  have h := tupleRelations_map φ hw
  rw [map_sub, map_mul, map_mul, zElt_map] at h
  exact h

variable [CharP F 2] [CharP L 2]

theorem generic_map {a : ℕ} {c : Fin a → F} (hc : Generic 2 c) : Generic 2 (φ ∘ c) := by
  intro g hg
  apply hc g
  apply φ.injective
  rw [map_sum, map_zero, ← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Function.comp_apply]
  congr 1
  exact congrFun (congrArg DFunLike.coe
    (Subsingleton.elim (φ.comp (ZMod.castHom (dvd_refl 2) F)) (ZMod.castHom (dvd_refl 2) L))) (g i)

end BaseChange

/-! ### Generic coefficients in `GaloisField 2 a` -/

theorem exists_generic_galois (a : ℕ) (ha : a ≠ 0) : ∃ c : Fin a → GaloisField 2 a, Generic 2 c := by
  have hfr := GaloisField.finrank 2 ha
  let bF := Module.finBasisOfFinrankEq (ZMod 2) (GaloisField 2 a) hfr
  refine ⟨fun i => bF i, ?_⟩
  intro g hg
  have hli := bF.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  apply hli g _ i
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, mul_comm]
  congr 1
  exact congrFun (congrArg DFunLike.coe (Subsingleton.elim (algebraMap (ZMod 2) (GaloisField 2 a))
    (ZMod.castHom (dvd_refl 2) (GaloisField 2 a)))) (g i)

/-! ### The witness hypothesis, unconditionally -/

theorem witnessHypothesis_of_isAlgClosed (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    WitnessHypothesis L (fun r => r * (r + 1) / 2) := by
  intro r a n hr hn
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain rfl : r = 0 := by simpa using hr
    refine ⟨Fin.elim0, ?_, 0, base_witness 0 n _⟩
    intro g _
    funext i
    exact i.elim0
  · letI : Algebra (ZMod 2) L := ZMod.algebra L 2
    obtain ⟨c, hc⟩ := exists_generic_galois a (by omega)
    obtain ⟨w, hw⟩ := witness_exists a c hc r hr n hn
    let φ : GaloisField 2 a →+* L :=
      (IsAlgClosed.lift : GaloisField 2 a →ₐ[ZMod 2] L).toRingHom
    exact ⟨φ ∘ c, generic_map φ hc, _, innerInverse_map φ hw⟩

theorem triangular_monotone : Monotone (fun r : ℕ => r * (r + 1) / 2) := by
  intro x y hxy
  exact Nat.div_le_div_right (Nat.mul_le_mul hxy (by omega))

/-! ### The unconditional characteristic-two theorems -/

section Final
variable {R : Type} [Field R] [CharP R 2] (T : Template R)

/-- **Theorem B (characteristic two).**  Every template over a field of characteristic two
satisfies (P) for both profiles, with onset `max(n₀, 2(kd+s)+1, (kd+s)(kd+s+1)/2)` and period
the least power of two above `kd+s`. -/
theorem charTwo_periodic :
    PeriodicProfile T.pcProfile (wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2))
        (period 2 T.k T.s) ∧
      PeriodicProfile T.nsProfile (wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2))
        (period 2 T.k T.s) :=
  periodic_of_hypothesis T (AlgebraicClosure R) triangular_monotone
    (witnessHypothesis_of_isAlgClosed _)

/-- **The T1–T4 classification (characteristic two).**  Exactly one of the four classes holds
for the PC profile, and exactly one for the NS profile. -/
theorem charTwo_classification :
    let N := wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2)
    ((IsT1 T.pcProfile ∧ ¬ IsT2 T.pcProfile N ∧ ¬ IsT3 T.pcProfile N ∧ ¬ IsT4 T.pcProfile N) ∨
     (¬ IsT1 T.pcProfile ∧ IsT2 T.pcProfile N ∧ ¬ IsT3 T.pcProfile N ∧ ¬ IsT4 T.pcProfile N) ∨
     (¬ IsT1 T.pcProfile ∧ ¬ IsT2 T.pcProfile N ∧ IsT3 T.pcProfile N ∧ ¬ IsT4 T.pcProfile N) ∨
     (¬ IsT1 T.pcProfile ∧ ¬ IsT2 T.pcProfile N ∧ ¬ IsT3 T.pcProfile N ∧ IsT4 T.pcProfile N)) ∧
    ((IsT1 T.nsProfile ∧ ¬ IsT2 T.nsProfile N ∧ ¬ IsT3 T.nsProfile N ∧ ¬ IsT4 T.nsProfile N) ∨
     (¬ IsT1 T.nsProfile ∧ IsT2 T.nsProfile N ∧ ¬ IsT3 T.nsProfile N ∧ ¬ IsT4 T.nsProfile N) ∨
     (¬ IsT1 T.nsProfile ∧ ¬ IsT2 T.nsProfile N ∧ IsT3 T.nsProfile N ∧ ¬ IsT4 T.nsProfile N) ∨
     (¬ IsT1 T.nsProfile ∧ ¬ IsT2 T.nsProfile N ∧ ¬ IsT3 T.nsProfile N ∧ IsT4 T.nsProfile N)) :=
  classification_of_hypothesis T (AlgebraicClosure R) triangular_monotone
    (witnessHypothesis_of_isAlgClosed _)

omit [CharP R 2] in
/-- The square-root window: if `n₀ ≤ n`, the triangular onset at `d = (⌊√n⌋ - s - 1)/k`
is at most `n`. -/
theorem wOnset_sqrt_le {n : ℕ} (hn : T.n0 ≤ n) :
    wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2) ((Nat.sqrt n - T.s - 1) / T.k) ≤ n := by
  set d := (Nat.sqrt n - T.s - 1) / T.k with hd
  unfold wOnset
  split
  · exact hn
  · rename_i hd0
    have hk : 0 < T.k := by
      rcases Nat.eq_zero_or_pos T.k with h | h
      · exfalso; apply hd0; rw [hd, h, Nat.div_zero]
      · exact h
    have hkd : T.k * d ≤ Nat.sqrt n - T.s - 1 := Nat.mul_div_le _ _
    have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have hx : T.k * d + T.s + 1 ≤ Nat.sqrt n := by
      have : 1 ≤ T.k * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hd0)
      omega
    set x := T.k * d + T.s with hxdef
    have hx2 : (x + 1) * (x + 1) ≤ n := le_trans (Nat.mul_le_mul hx hx) hsq
    refine max_le ?_ ?_
    · unfold onset
      rw [if_neg hd0]
      refine max_le hn ?_
      nlinarith
    · change x * (x + 1) / 2 ≤ n
      calc x * (x + 1) / 2 ≤ x * (x + 1) := Nat.div_le_self _ _
        _ ≤ n := by nlinarith

/-- **The Ω(√n) lower bound for T2 (PC).** -/
theorem charTwo_T2_pc_sqrt (h2 : IsT2 T.pcProfile (wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2)))
    {n : ℕ} (hn : T.n0 ≤ n) : (((Nat.sqrt n - T.s - 1) / T.k : ℕ) : ℕ∞) < T.pcProfile n :=
  (charTwo_periodic T).1.T2_gt h2 (wOnset_sqrt_le T hn)

/-- **The Ω(√n) lower bound for T2 (NS).** -/
theorem charTwo_T2_ns_sqrt (h2 : IsT2 T.nsProfile (wOnset T.k T.s T.n0 (fun r => r * (r + 1) / 2)))
    {n : ℕ} (hn : T.n0 ≤ n) : (((Nat.sqrt n - T.s - 1) / T.k : ℕ) : ℕ∞) < T.nsProfile n :=
  (charTwo_periodic T).2.T2_gt h2 (wOnset_sqrt_le T hn)

end Final
end ClaudeC017
