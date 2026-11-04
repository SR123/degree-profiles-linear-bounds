/-
Claude audit, 25 September 2026.  NOT a project file: an independent generalisation.

Cycles 011–013 prove the characteristic-two template transfer only for support r ≤ 3,
because the shared group-algebra inner inverse was supplied for that range alone.  This
file removes that restriction: ANY shared group-algebra element w with

      z w z - z ∈ TupleRelations K r (n + 2^a),     z = Σ_i c_i (σ_i - 1),

gives exactness of the actual canonical shifted functor for every support r' ≤ r, hence
the actual NS and ordinary-PC transfer n + 2^a ↔ n at every degree d with kd+s ≤ r.
Iterating, a family of such witnesses with onset W(r) gives hypothesis (P) with onset
max(n₀, 2(kd+s)+1, W(kd+s)) and period the least 2-power above kd+s, and therefore the
Stage 5 T1–T4 classification.  The existence of witnesses is kept as an explicit named
hypothesis; nothing is assumed about exactness, equivalence or transfer.
-/
import TemplateExactTransfer
import ShiftedAdditive
import ProjectorExactness
import ShiftedProjection
import ShiftedPreservation
import RankThreeTransport
import DegreeProfilesReview.TemplatePeriodicity
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace ClaudeWitnessTransfer
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.PC DegreeProfilesReview.NS
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle012 SelfContainedCycle013

section Algebra
variable {K : Type} [Field K]

/-- The actual group-algebra element z = Σ c_i (σ_i − 1) for the Stage 5 block generators. -/
noncomputable def zElt (a n : ℕ) (c : Fin a → K) : MonoidAlgebra K (Sfin (n + 2 ^ a)) :=
  ∑ i, c i • (MonoidAlgebra.single (σgen 2 a n i) (1 : K) - 1)

/-- Its action on every representation is Stage 5's operator `zOp`. -/
theorem zElt_action (a n : ℕ) (c : Fin a → K) (M : Rep K (Sfin (n + 2 ^ a))) :
    M.ρ.asAlgebraHom (zElt a n c) = zOp (σgen 2 a n) c M.ρ := by
  simp only [zElt, zOp, map_sum, map_smul, map_sub, map_one,
    Representation.asAlgebraHom_single_one]
  rfl

/-- The algebraic input: a shared inner inverse modulo the actual tuple relations. -/
def IsTupleInnerInverse (r a n : ℕ) (c : Fin a → K) (w : MonoidAlgebra K (Sfin (n + 2 ^ a))) :
    Prop :=
  zElt a n c * w * zElt a n c - zElt a n c ∈ TupleRelations K r (n + 2 ^ a)

theorem innerInverse_of_class {r a n : ℕ} {c : Fin a → K} {w : MonoidAlgebra K (Sfin (n + 2 ^ a))}
    (hw : IsTupleInnerInverse r a n c w) {M : Rep K (Sfin (n + 2 ^ a))}
    (hM : CanonicalClass K r (n + 2 ^ a) M) :
    zOp (σgen 2 a n) c M.ρ * M.ρ.asAlgebraHom w * zOp (σgen 2 a n) c M.ρ =
      zOp (σgen 2 a n) c M.ρ := by
  have hh := hM.2 _ hw
  rw [← zElt_action]
  simpa only [map_sub, map_mul, sub_eq_zero] using hh

/-- Smaller support classes lie in larger ones (same statement as Cycle 013's lemma). -/
theorem canonical_mono {r s N : ℕ} (hrs : r ≤ s) {M : Rep K (Sfin N)}
    (hM : CanonicalClass K r N M) : CanonicalClass K s N M :=
  ⟨hM.1, fun a ha => hM.2 a (fun b hb => ha b (hb.trans hrs))⟩

variable [CharP K 2]

theorem z_sq (a n : ℕ) (c : Fin a → K) (M : Rep K (Sfin (n + 2 ^ a))) :
    zOp (σgen 2 a n) c M.ρ * zOp (σgen 2 a n) c M.ρ = 0 := by
  simpa only [pow_two] using
    zOp_pow_char c M.ρ (gen_comm (blockφ 2 a n)) (gen_pow (blockφ 2 a n))

noncomputable def wProjector {a n : ℕ} (c : Fin a → K) (w : MonoidAlgebra K (Sfin (n + 2 ^ a)))
    (M : Rep K (Sfin (n + 2 ^ a))) : Module.End K M.V :=
  homologyProjector (zOp (σgen 2 a n) c M.ρ) (M.ρ.asAlgebraHom w)

noncomputable def wProjectionEquiv {r a n : ℕ} {c : Fin a → K}
    {w : MonoidAlgebra K (Sfin (n + 2 ^ a))} (hw : IsTupleInnerInverse r a n c w)
    (M : Rep K (Sfin (n + 2 ^ a))) (hM : CanonicalClass K r (n + 2 ^ a) M) :
    ((Ψhat 2 a n c).obj M).V ≃ₗ[K] LinearMap.range (wProjector c w M) :=
  scProjectionEquiv (σgen 2 a n) c M.ρ (M.ρ.asAlgebraHom w) (z_sq a n c M)
    (innerInverse_of_class hw hM)

theorem wProjection_natural {r a n : ℕ} {c : Fin a → K}
    {w : MonoidAlgebra K (Sfin (n + 2 ^ a))} (hw : IsTupleInnerInverse r a n c w)
    {M N : Rep K (Sfin (n + 2 ^ a))} (hM : CanonicalClass K r (n + 2 ^ a) M)
    (hN : CanonicalClass K r (n + 2 ^ a) N) (f : M ⟶ N) (d : ((Ψhat 2 a n c).obj M).V) :
    (wProjectionEquiv hw N hN (((Ψhat 2 a n c).map f).hom.hom d) : N.V) =
      f.hom.hom (wProjectionEquiv hw M hM d) :=
  scProjection_natural (σgen 2 a n) c M.ρ (M.ρ.asAlgebraHom w) (z_sq a n c M)
    (innerInverse_of_class hw hM) N.ρ (N.ρ.asAlgebraHom w) (z_sq a n c N)
    (innerInverse_of_class hw hN) f.hom.hom (hom_sequivariant _ f)
    (fun v => algebra_action_comm f _ v) d

/-- Every exact complex in the support-r class is preserved by the actual Ψhat. -/
theorem witness_map_exact {r a n : ℕ} {c : Fin a → K} {w : MonoidAlgebra K (Sfin (n + 2 ^ a))}
    (hw : IsTupleInnerInverse r a n c w) {X Y Z : Rep K (Sfin (n + 2 ^ a))}
    (hX : CanonicalClass K r (n + 2 ^ a) X) (hY : CanonicalClass K r (n + 2 ^ a) Y)
    (hZ : CanonicalClass K r (n + 2 ^ a) Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hex : Function.Exact f.hom.hom g.hom.hom) :
    Function.Exact (((Ψhat 2 a n c).map f).hom.hom) (((Ψhat 2 a n c).map g).hom.hom) := by
  apply exact_of_projector_models f.hom.hom g.hom.hom _ _
    (wProjector c w X) (wProjector c w Y) (wProjector c w Z)
    (wProjectionEquiv hw X hX) (wProjectionEquiv hw Y hY) (wProjectionEquiv hw Z hZ)
  · exact projector_idempotent _ _ (z_sq a n c Y) (innerInverse_of_class hw hY)
  · exact projector_natural _ _ _ _ f.hom.hom
      ((hom_sequivariant (σgen 2 a n) f).zOp_comm c) (fun v => algebra_action_comm f _ v)
  · exact wProjection_natural hw hX hY f
  · exact wProjection_natural hw hY hZ g
  · exact hex

theorem witness_canonical_map_exact {r r' a n : ℕ} {c : Fin a → K}
    {w : MonoidAlgebra K (Sfin (n + 2 ^ a))} (hw : IsTupleInnerInverse r a n c w) (hr : r' ≤ r)
    (S : ShortComplex (canonicalSchurClass K r' (n + 2 ^ a)).B) (hS : S.Exact) :
    (S.map (canonicalΨ 2 a n r' c)).Exact := by
  let ωN := (canonicalSchurClass K r' (n + 2 ^ a)).toM4.ω
  let ωn := (canonicalSchurClass K r' n).toM4.ω
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map ωN)).mp
    (hS.map ωN)
  apply Functor.reflects_exact_of_faithful ωn
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact witness_map_exact hw (canonical_mono hr S.X₁.property)
    (canonical_mono hr S.X₂.property) (canonical_mono hr S.X₃.property) S.f S.g hex

theorem witness_preserves_homology {r r' a n : ℕ} {c : Fin a → K}
    {w : MonoidAlgebra K (Sfin (n + 2 ^ a))} (hw : IsTupleInnerInverse r a n c w) (hr : r' ≤ r) :
    (canonicalΨ 2 a n r' c).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (witness_canonical_map_exact hw hr)

theorem witness_preserves_finiteLimits {r r' a n : ℕ} {c : Fin a → K}
    {w : MonoidAlgebra K (Sfin (n + 2 ^ a))} (hw : IsTupleInnerInverse r a n c w) (hr : r' ≤ r) :
    PreservesFiniteLimits (canonicalΨ 2 a n r' c) := by
  let F := canonicalΨ 2 a n r' c
  haveI : F.PreservesHomology := witness_preserves_homology hw hr
  letI : ∀ {X Y : (canonicalSchurClass K r' (n + 2 ^ a)).B} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) F := fun f => Functor.PreservesHomology.preservesKernel F f
  exact Functor.preservesFiniteLimits_of_preservesKernels F

theorem witness_preserves_finiteColimits {r r' a n : ℕ} {c : Fin a → K}
    {w : MonoidAlgebra K (Sfin (n + 2 ^ a))} (hw : IsTupleInnerInverse r a n c w) (hr : r' ≤ r) :
    PreservesFiniteColimits (canonicalΨ 2 a n r' c) := by
  let F := canonicalΨ 2 a n r' c
  haveI : F.PreservesHomology := witness_preserves_homology hw hr
  letI : ∀ {X Y : (canonicalSchurClass K r' (n + 2 ^ a)).B} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) F :=
    fun f => Functor.PreservesHomology.preservesCokernel F f
  exact Functor.preservesFiniteColimits_of_preservesCokernels F

/-- **Actual-template transfer from any shared witness**, at every support, every
characteristic-two field carrying generic coefficients. -/
theorem template_step_of_witness (T : Template K) {d a n r : ℕ} (hd : 1 ≤ d)
    (hn0 : T.n0 ≤ n) (hrq : T.k * d + T.s < 2 ^ a) (hr : T.k * d + T.s ≤ r)
    {c : Fin a → K} (hc : Generic 2 c) {w : MonoidAlgebra K (Sfin (n + 2 ^ a))}
    (hw : IsTupleInnerInverse r a n c w) :
    (Refutes (T.inst (n + 2 ^ a)) d ↔ Refutes (T.inst n) d) ∧
    (NSRefutes (T.inst (n + 2 ^ a)) d ↔ NSRefutes (T.inst n) d) := by
  letI := witness_preserves_finiteLimits hw hr
  letI := witness_preserves_finiteColimits hw hr
  letI : (canonicalΨ 2 a n (T.k * d + T.s) c).PreservesZeroMorphisms := inferInstance
  let m5 := canonicalM5w (n := n) (r := T.k * d + T.s) hc hrq
  exact ⟨template_pc_step_exact T (F := canonicalΨ 2 a n (T.k * d + T.s) c)
      hd (by omega) hn0 m5,
    template_ns_step_exact T (F := canonicalΨ 2 a n (T.k * d + T.s) c) (by omega) hn0 m5⟩

end Algebra

/-! ### From a witness family to hypothesis (P) and the four types -/

/-- Witnesses exist for every support r, every 2-power above r, and every retained rank
n ≥ W r, over the field L. -/
def WitnessHypothesis (L : Type) [Field L] [CharP L 2] (W : ℕ → ℕ) : Prop :=
  ∀ r a n : ℕ, r < 2 ^ a → W r ≤ n →
    ∃ c : Fin a → L, Generic 2 c ∧ ∃ w : MonoidAlgebra L (Sfin (n + 2 ^ a)),
      IsTupleInnerInverse r a n c w

/-- Onset `N(0)=n₀`, `N(d)=max(n₀, 2(kd+s)+1, W(kd+s))`. -/
def wOnset (k s n0 : ℕ) (W : ℕ → ℕ) (d : ℕ) : ℕ :=
  if d = 0 then n0 else max (onset k s n0 d) (W (k * d + s))

section Profiles
variable {R : Type} [Field R] (T : Template R) (L : Type) [Field L] [CharP L 2] [Algebra R L]

theorem step_of_hypothesis {W : ℕ → ℕ} (H : WitnessHypothesis L W) {d a n : ℕ} (hd : 1 ≤ d)
    (hn0 : T.n0 ≤ n) (hW : W (T.k * d + T.s) ≤ n) (hrq : T.k * d + T.s < 2 ^ a) :
    (T.pcProfile (n + 2 ^ a) ≤ (d : ℕ∞) ↔ T.pcProfile n ≤ (d : ℕ∞)) ∧
    (T.nsProfile (n + 2 ^ a) ≤ (d : ℕ∞) ↔ T.nsProfile n ≤ (d : ℕ∞)) := by
  obtain ⟨c, hc, w, hw⟩ := H (T.k * d + T.s) a n hrq hW
  have hh := template_step_of_witness (T.map (algebraMap R L)) hd hn0 hrq le_rfl hc hw
  rw [← pcDegree_le_iff, ← pcDegree_le_iff, ← nsDegree_le_iff, ← nsDegree_le_iff] at hh
  change ((T.map (algebraMap R L)).pcProfile (n + 2 ^ a) ≤ d ↔
    (T.map (algebraMap R L)).pcProfile n ≤ d) ∧
    ((T.map (algebraMap R L)).nsProfile (n + 2 ^ a) ≤ d ↔
    (T.map (algebraMap R L)).nsProfile n ≤ d) at hh
  rw [T.pcProfile_map, T.pcProfile_map, T.nsProfile_map, T.nsProfile_map] at hh
  exact hh

theorem wOnset_mono {W : ℕ → ℕ} (hWm : Monotone W) : Monotone (wOnset T.k T.s T.n0 W) := by
  intro d d' hdd
  unfold wOnset
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl]
    split
    · exact le_refl _
    · exact le_trans (n0_le_onset _ _ _ d') (le_max_left _ _)
  · rw [if_neg hd, if_neg (by omega)]
    have h1 := onset_mono T.k T.s T.n0 hdd
    have h2 : W (T.k * d + T.s) ≤ W (T.k * d' + T.s) :=
      hWm (by have := Nat.mul_le_mul_left T.k hdd; omega)
    exact max_le_max h1 h2

theorem periodic_of_hypothesis {W : ℕ → ℕ} (hWm : Monotone W) (H : WitnessHypothesis L W) :
    PeriodicProfile T.pcProfile (wOnset T.k T.s T.n0 W) (period 2 T.k T.s) ∧
    PeriodicProfile T.nsProfile (wOnset T.k T.s T.n0 W) (period 2 T.k T.s) := by
  have hp : (2 : ℕ) ≤ 2 := le_rfl
  have hge : ∀ d, d + 1 ≤ wOnset T.k T.s T.n0 W d := by
    intro d
    unfold wOnset
    split
    · have := T.hn0; omega
    · exact le_trans (onset_ge T.s T.hk T.hn0 d) (le_max_left _ _)
  -- the common periodicity argument, for either profile
  have key : ∀ (h : ℕ → ℕ∞), ZeroStable T.n0 h →
      (∀ d a n, 1 ≤ d → T.n0 ≤ n → W (T.k * d + T.s) ≤ n → T.k * d + T.s < 2 ^ a →
        (h (n + 2 ^ a) ≤ (d : ℕ∞) ↔ h n ≤ (d : ℕ∞))) →
      PeriodicProfile h (wOnset T.k T.s T.n0 W) (period 2 T.k T.s) := by
    intro h h0 hstep
    refine ⟨wOnset_mono T hWm, hge, period_pos hp T.k T.s, ?_⟩
    intro d t htd n m hn hm hc
    by_cases ht : t = 0
    · subst ht
      have hN0 : T.n0 ≤ wOnset T.k T.s T.n0 W d := by
        unfold wOnset; split
        · exact le_refl _
        · exact le_trans (n0_le_onset _ _ _ d) (le_max_left _ _)
      exact h0 n m (le_trans hN0 hn) (le_trans hN0 hm)
    · have hd : 1 ≤ d := by omega
      have hon : wOnset T.k T.s T.n0 W d = max (onset T.k T.s T.n0 d) (W (T.k * d + T.s)) := by
        unfold wOnset; rw [if_neg (by omega)]
      rw [hon] at hn hm
      have hper : period 2 T.k T.s d = leastPowGt 2 (T.k * d + T.s) := by
        unfold period; rw [if_neg (by omega)]
      rw [hper] at hc
      obtain ⟨a, ha⟩ := leastPowGt_isPow hp (T.k * d + T.s)
      have hgt := leastPowGt_gt hp (T.k * d + T.s)
      rw [ha] at hc hgt
      have hkt : T.k * t ≤ T.k * d := Nat.mul_le_mul_left T.k htd
      have hWt : W (T.k * t + T.s) ≤ W (T.k * d + T.s) := hWm (by omega)
      have hn0d : T.n0 ≤ onset T.k T.s T.n0 d := n0_le_onset _ _ _ d
      refine congr_of_step (Pr := fun x => h x ≤ (t : ℕ∞)) (q := 2 ^ a)
        (B := max T.n0 (W (T.k * t + T.s))) ?_ ?_ ?_ hc
      · intro x hx
        exact hstep t a x (by omega) (le_trans (le_max_left _ _) hx)
          (le_trans (le_max_right _ _) hx) (by omega)
      · exact max_le (le_trans hn0d (le_trans (le_max_left _ _) hn))
          (le_trans hWt (le_trans (le_max_right _ _) hn))
      · exact max_le (le_trans hn0d (le_trans (le_max_left _ _) hm))
          (le_trans hWt (le_trans (le_max_right _ _) hm))
  exact ⟨key _ T.zeroStable_pc
      (fun d a n hd hn0 hW hrq => (step_of_hypothesis T L H hd hn0 hW hrq).1),
    key _ T.zeroStable_ns
      (fun d a n hd hn0 hW hrq => (step_of_hypothesis T L H hd hn0 hW hrq).2)⟩

/-- **The four types from witnesses.**  Each actual profile is exactly one of T1–T4, with
the inverse-threshold function of the witness onset. -/
theorem classification_of_hypothesis {W : ℕ → ℕ} (hWm : Monotone W) (H : WitnessHypothesis L W) :
    let N := wOnset T.k T.s T.n0 W
    ((IsT1 T.pcProfile ∧ ¬ IsT2 T.pcProfile N ∧ ¬ IsT3 T.pcProfile N ∧ ¬ IsT4 T.pcProfile N) ∨
     (¬ IsT1 T.pcProfile ∧ IsT2 T.pcProfile N ∧ ¬ IsT3 T.pcProfile N ∧ ¬ IsT4 T.pcProfile N) ∨
     (¬ IsT1 T.pcProfile ∧ ¬ IsT2 T.pcProfile N ∧ IsT3 T.pcProfile N ∧ ¬ IsT4 T.pcProfile N) ∨
     (¬ IsT1 T.pcProfile ∧ ¬ IsT2 T.pcProfile N ∧ ¬ IsT3 T.pcProfile N ∧ IsT4 T.pcProfile N)) ∧
    ((IsT1 T.nsProfile ∧ ¬ IsT2 T.nsProfile N ∧ ¬ IsT3 T.nsProfile N ∧ ¬ IsT4 T.nsProfile N) ∨
     (¬ IsT1 T.nsProfile ∧ IsT2 T.nsProfile N ∧ ¬ IsT3 T.nsProfile N ∧ ¬ IsT4 T.nsProfile N) ∨
     (¬ IsT1 T.nsProfile ∧ ¬ IsT2 T.nsProfile N ∧ IsT3 T.nsProfile N ∧ ¬ IsT4 T.nsProfile N) ∨
     (¬ IsT1 T.nsProfile ∧ ¬ IsT2 T.nsProfile N ∧ ¬ IsT3 T.nsProfile N ∧ IsT4 T.nsProfile N)) := by
  obtain ⟨Ppc, Pns⟩ := periodic_of_hypothesis T L hWm H
  exact ⟨Ppc.exactly_one, Pns.exactly_one⟩

/-- The T2 bound in the witness scale: no recurring level means `d < h(n)` whenever the
witness onset at level `d` is at most `n`. -/
theorem T2_bound_of_hypothesis {W : ℕ → ℕ} (hWm : Monotone W) (H : WitnessHypothesis L W)
    (h2 : IsT2 T.pcProfile (wOnset T.k T.s T.n0 W)) {n d : ℕ}
    (hd : wOnset T.k T.s T.n0 W d ≤ n) : (d : ℕ∞) < T.pcProfile n :=
  (periodic_of_hypothesis T L hWm H).1.T2_gt h2 hd

end Profiles

/-! ### Non-vacuity: the hypothesis format is met by the checked support-three witness -/

section NonVacuity
open SelfContainedCycle006 (rootCoefficients)
open SelfContainedCycle011
variable {K : Type} [Field K] [CharP K 2]

theorem transported_z_eq (n : ℕ) (hn : 7 ≤ n) (t : K) :
    transportAlgebra (by omega : 11 ≤ n + 4) (blockRelabel n hn) (SelfContainedCycle010.prototypeZ t) =
      zElt 2 n (rootCoefficients t) := by
  rw [prototypeZ_formula]
  simp only [map_add, map_smul, map_sub, map_one, transport_generator, zElt, Fin.sum_univ_two,
    rootCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]

/-- The Cycle 011 witness satisfies `IsTupleInnerInverse` at r = 3, a = 2, n ≥ 7. -/
theorem cycle011_witness_is_tuple_inverse (n : ℕ) (hn : 7 ≤ n) (t : K) (ht : t^2+t+1=0) :
    IsTupleInnerInverse 3 2 n (rootCoefficients t) (actualWitness n hn t ht) := by
  unfold IsTupleInnerInverse actualWitness
  rw [← transported_z_eq n hn t]
  have h := transport_relation (by omega : 11 ≤ n + 4) (blockRelabel n hn) _
    (prototypeWitness_relation t ht)
  simpa only [map_sub, map_mul] using h

end NonVacuity
end ClaudeWitnessTransfer
