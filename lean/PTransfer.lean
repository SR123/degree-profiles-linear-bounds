/-
Claude, 25 Sep 2026.  Every prime characteristic, part B: from a shared top-power witness to
exactness, template transfer, (P) and T1–T4.

For a prime `p`, `q = p^a`, generic `c` and `z = Σ c_i (σ_i - 1)`, a TOP-POWER WITNESS of support
`r` is an actual group-algebra element `w` with

      z^(p-1) w z^(p-1) - z^(p-1) ∈ TupleRelations K r (n + q).

For `p = 2` this is `IsTupleInnerInverse`.  With purity on the tuple modules (`tuple_pure`),
Cycle 084's explicit projector `P = topProjector z w (p-1)` satisfies `zP = Pz = 0` and `P² = P`
modulo the tuple relations, so on every object of the canonical class Stage 5's actual shifted
quotient `ker z / (ker z ∩ range z)` is naturally the image of `P`.  Hence the actual functor
`Ψhat` is exact on the canonical class, and Cycle 013's template reduction gives the NS and PC
transfer `n + p^a ↔ n`; iterating gives (P) and the four types.
-/
import ClaudeWitnessTransfer
import TopPowerExactness
import PAuxiliary

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace ClaudeCP
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.Profiles
open DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 SelfContainedCycle004 SelfContainedCycle012 SelfContainedCycle013
open SelfContainedCycle084 ClaudeWitnessTransfer

section Algebra
variable {K : Type} [Field K] (p : ℕ) [Fact p.Prime]

/-- `z = Σ c_i (σ_i - 1)` in the group algebra of `S_{n+p^a}`. -/
noncomputable def zEltP (a n : ℕ) (c : Fin a → K) : MonoidAlgebra K (Sfin (n + p ^ a)) :=
  ∑ i, c i • (MonoidAlgebra.single (σgen p a n i) (1 : K) - 1)

theorem zEltP_action (a n : ℕ) (c : Fin a → K) (M : Rep K (Sfin (n + p ^ a))) :
    M.ρ.asAlgebraHom (zEltP p a n c) = zOp (σgen p a n) c M.ρ := by
  simp only [zEltP, zOp, map_sum, map_smul, map_sub, map_one,
    Representation.asAlgebraHom_single_one]
  rfl

/-- **Shared top-power witness of support `r`.** -/
def IsTopWitness (r a n : ℕ) (c : Fin a → K) (w : MonoidAlgebra K (Sfin (n + p ^ a))) : Prop :=
  zEltP p a n c ^ (p - 1) * w * zEltP p a n c ^ (p - 1) - zEltP p a n c ^ (p - 1) ∈
    TupleRelations K r (n + p ^ a)

/-- Cycle 084's projector, as an actual group-algebra element. -/
noncomputable def topElt (a n : ℕ) (c : Fin a → K) (w : MonoidAlgebra K (Sfin (n + p ^ a))) :
    MonoidAlgebra K (Sfin (n + p ^ a)) :=
  topProjector (zEltP p a n c) w (p - 1)

variable {p}
variable [CharP K p]

theorem one_le_pred : 1 ≤ p - 1 := by
  have := (Fact.out : p.Prime).two_le; omega

theorem zOp_pow_p (a n : ℕ) (c : Fin a → K) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K (Sfin (n + p ^ a)) V) :
    (zOp (σgen p a n) c ρ) ^ (p - 1 + 1) = 0 := by
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le]
  exact zOp_pow_char c ρ (gen_comm (blockφ p a n)) (gen_pow (blockφ p a n))

/-- The projector identities hold modulo the tuple relations. -/
theorem topElt_relations {r a n : ℕ} {c : Fin a → K} (hc : Generic p c) (hr : r < p ^ a)
    {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w) :
    zEltP p a n c * topElt p a n c w ∈ TupleRelations K r (n + p ^ a) ∧
    topElt p a n c w * zEltP p a n c ∈ TupleRelations K r (n + p ^ a) ∧
    topElt p a n c w * topElt p a n c w - topElt p a n c w ∈ TupleRelations K r (n + p ^ a) := by
  have key : ∀ b, b ≤ r →
      let φ := ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom).toRingHom
      let Z := zOp (σgen p a n) c (permRep K (injTuples b) (n + p ^ a)).ρ
      φ (zEltP p a n c) = Z ∧ φ (topElt p a n c w) = topProjector Z (φ w) (p - 1) ∧
      Z * topProjector Z (φ w) (p - 1) = 0 ∧ topProjector Z (φ w) (p - 1) * Z = 0 ∧
      topProjector Z (φ w) (p - 1) * topProjector Z (φ w) (p - 1) =
        topProjector Z (φ w) (p - 1) := by
    intro b hb φ Z
    have hφz : φ (zEltP p a n c) = Z := zEltP_action p a n c _
    have hi : Z ^ (p - 1) * φ w * Z ^ (p - 1) = Z ^ (p - 1) := by
      have h := hw b hb
      rw [map_sub, sub_eq_zero] at h
      have h' : φ (zEltP p a n c ^ (p - 1) * w * zEltP p a n c ^ (p - 1)) =
          φ (zEltP p a n c ^ (p - 1)) := h
      simpa only [map_mul, map_pow, hφz] using h'
    have hz := zOp_pow_p a n c (permRep K (injTuples b) (n + p ^ a)).ρ
    have hpur := tuple_pure (n := n) c hc (lt_of_le_of_lt hb hr)
    obtain ⟨h1, h2⟩ := topProjector_annihilates Z (φ w) one_le_pred hpur hi hz
    have h3 := topProjector_idempotent Z (φ w) one_le_pred hpur hi hz
    refine ⟨hφz, ?_, h1, h2, h3⟩
    rw [topElt, map_topProjector, hφz]
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨hz, hP, h1, -, -⟩ := key b hb
    have : ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom).toRingHom
        (zEltP p a n c * topElt p a n c w) = 0 := by rw [map_mul, hz, hP, h1]
    exact this
  · obtain ⟨hz, hP, -, h2, -⟩ := key b hb
    have : ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom).toRingHom
        (topElt p a n c w * zEltP p a n c) = 0 := by rw [map_mul, hz, hP, h2]
    exact this
  · obtain ⟨-, hP, -, -, h3⟩ := key b hb
    have : ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom).toRingHom
        (topElt p a n c w * topElt p a n c w - topElt p a n c w) = 0 := by
      rw [map_sub, map_mul, hP, h3, sub_self]
    exact this

/-- The projector on an object of the canonical class. -/
noncomputable def topProj {a n : ℕ} (c : Fin a → K) (w : MonoidAlgebra K (Sfin (n + p ^ a)))
    (M : Rep K (Sfin (n + p ^ a))) : Module.End K M.V :=
  M.ρ.asAlgebraHom (topElt p a n c w)

theorem topProj_props {r a n : ℕ} {c : Fin a → K} (hc : Generic p c) (hr : r < p ^ a)
    {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    {M : Rep K (Sfin (n + p ^ a))} (hM : CanonicalClass K r (n + p ^ a) M) :
    topProj c w M * zOp (σgen p a n) c M.ρ = 0 ∧ zOp (σgen p a n) c M.ρ * topProj c w M = 0 ∧
    topProj c w M * topProj c w M = topProj c w M ∧
    ∀ v, zOp (σgen p a n) c M.ρ v = 0 →
      v - topProj c w M v ∈ LinearMap.range (zOp (σgen p a n) c M.ρ) := by
  obtain ⟨h1, h2, h3⟩ := topElt_relations hc hr hw
  have e1 := hM.2 _ h1
  have e2 := hM.2 _ h2
  have e3 := hM.2 _ h3
  rw [map_mul, zEltP_action] at e1 e2
  rw [map_sub, map_mul, sub_eq_zero] at e3
  refine ⟨e2, e1, e3, fun v hv => ?_⟩
  have hP : topProj c w M = topProjector (zOp (σgen p a n) c M.ρ) (M.ρ.asAlgebraHom w) (p - 1) := by
    have := map_topProjector (M.ρ.asAlgebraHom).toRingHom (zEltP p a n c) w (p - 1)
    rw [show ((M.ρ.asAlgebraHom).toRingHom) (zEltP p a n c) = zOp (σgen p a n) c M.ρ from
      zEltP_action p a n c M] at this
    exact this
  rw [hP]
  exact kernel_residual_in_range _ _ one_le_pred hv

/-- The actual shifted quotient is naturally the image of the projector. -/
noncomputable def topProjectionEquiv {r a n : ℕ} {c : Fin a → K} (hc : Generic p c)
    (hr : r < p ^ a) {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    (M : Rep K (Sfin (n + p ^ a))) (hM : CanonicalClass K r (n + p ^ a) M) :
    ((Ψhat p a n c).obj M).V ≃ₗ[K] LinearMap.range (topProj c w M) :=
  qEquiv (zOp (σgen p a n) c M.ρ) (topProj c w M) (topProj_props hc hr hw hM).1
    (topProj_props hc hr hw hM).2.1 (topProj_props hc hr hw hM).2.2.1
    (topProj_props hc hr hw hM).2.2.2

theorem topProjection_natural {r a n : ℕ} {c : Fin a → K} (hc : Generic p c) (hr : r < p ^ a)
    {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    {M N : Rep K (Sfin (n + p ^ a))} (hM : CanonicalClass K r (n + p ^ a) M)
    (hN : CanonicalClass K r (n + p ^ a) N) (f : M ⟶ N) (d : ((Ψhat p a n c).obj M).V) :
    (topProjectionEquiv hc hr hw N hN (((Ψhat p a n c).map f).hom.hom d) : N.V) =
      f.hom.hom (topProjectionEquiv hc hr hw M hM d) := by
  obtain ⟨v, hv, rfl⟩ := sc_induction (σgen p a n) c M.ρ d
  change (topProjectionEquiv hc hr hw N hN
    (scMap c f.hom.hom (hom_sequivariant _ f) (scMk (σgen p a n) c M.ρ v hv)) : N.V) = _
  rw [scMap_scMk]
  change topProj c w N (f.hom.hom v) = f.hom.hom (topProj c w M v)
  exact (algebra_action_comm f _ v).symm

/-- Every exact complex in the support-r class is preserved by the actual `Ψhat`. -/
theorem top_map_exact {r a n : ℕ} {c : Fin a → K} (hc : Generic p c) (hr : r < p ^ a)
    {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    {X Y Z : Rep K (Sfin (n + p ^ a))}
    (hX : CanonicalClass K r (n + p ^ a) X) (hY : CanonicalClass K r (n + p ^ a) Y)
    (hZ : CanonicalClass K r (n + p ^ a) Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hex : Function.Exact f.hom.hom g.hom.hom) :
    Function.Exact (((Ψhat p a n c).map f).hom.hom) (((Ψhat p a n c).map g).hom.hom) := by
  apply exact_of_projector_models f.hom.hom g.hom.hom _ _
    (topProj c w X) (topProj c w Y) (topProj c w Z)
    (topProjectionEquiv hc hr hw X hX) (topProjectionEquiv hc hr hw Y hY)
    (topProjectionEquiv hc hr hw Z hZ)
  · exact (topProj_props hc hr hw hY).2.2.1
  · exact fun x => algebra_action_comm f _ x
  · exact topProjection_natural hc hr hw hX hY f
  · exact topProjection_natural hc hr hw hY hZ g
  · exact hex

theorem top_canonical_map_exact {r r' a n : ℕ} {c : Fin a → K} (hc : Generic p c)
    (hr : r < p ^ a) {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    (hr' : r' ≤ r) (S : ShortComplex (canonicalSchurClass K r' (n + p ^ a)).B) (hS : S.Exact) :
    (S.map (canonicalΨ p a n r' c)).Exact := by
  let ωN := (canonicalSchurClass K r' (n + p ^ a)).toM4.ω
  let ωn := (canonicalSchurClass K r' n).toM4.ω
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map ωN)).mp
    (hS.map ωN)
  apply Functor.reflects_exact_of_faithful ωn
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact top_map_exact hc hr hw (canonical_mono hr' S.X₁.property)
    (canonical_mono hr' S.X₂.property) (canonical_mono hr' S.X₃.property) S.f S.g hex

theorem top_preserves_homology {r r' a n : ℕ} {c : Fin a → K} (hc : Generic p c)
    (hr : r < p ^ a) {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    (hr' : r' ≤ r) : (canonicalΨ p a n r' c).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (top_canonical_map_exact hc hr hw hr')

theorem top_preserves_finiteLimits {r r' a n : ℕ} {c : Fin a → K} (hc : Generic p c)
    (hr : r < p ^ a) {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    (hr' : r' ≤ r) : PreservesFiniteLimits (canonicalΨ p a n r' c) := by
  let F := canonicalΨ p a n r' c
  haveI : F.PreservesHomology := top_preserves_homology hc hr hw hr'
  letI : ∀ {X Y : (canonicalSchurClass K r' (n + p ^ a)).B} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) F := fun f => Functor.PreservesHomology.preservesKernel F f
  exact Functor.preservesFiniteLimits_of_preservesKernels F

theorem top_preserves_finiteColimits {r r' a n : ℕ} {c : Fin a → K} (hc : Generic p c)
    (hr : r < p ^ a) {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p r a n c w)
    (hr' : r' ≤ r) : PreservesFiniteColimits (canonicalΨ p a n r' c) := by
  let F := canonicalΨ p a n r' c
  haveI : F.PreservesHomology := top_preserves_homology hc hr hw hr'
  letI : ∀ {X Y : (canonicalSchurClass K r' (n + p ^ a)).B} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) F :=
    fun f => Functor.PreservesHomology.preservesCokernel F f
  exact Functor.preservesFiniteColimits_of_preservesCokernels F

/-- **Actual-template transfer from a shared top-power witness**, in characteristic `p`. -/
theorem template_step_of_top_witness (T : Template K) {d a n r : ℕ} (hd : 1 ≤ d)
    (hn0 : T.n0 ≤ n) (hrq : T.k * d + T.s < p ^ a) (hr : T.k * d + T.s ≤ r) (hrp : r < p ^ a)
    {c : Fin a → K} (hc : Generic p c) {w : MonoidAlgebra K (Sfin (n + p ^ a))}
    (hw : IsTopWitness p r a n c w) :
    (Refutes (T.inst (n + p ^ a)) d ↔ Refutes (T.inst n) d) ∧
    (NSRefutes (T.inst (n + p ^ a)) d ↔ NSRefutes (T.inst n) d) := by
  letI := top_preserves_finiteLimits hc hrp hw hr
  letI := top_preserves_finiteColimits hc hrp hw hr
  letI : (canonicalΨ p a n (T.k * d + T.s) c).PreservesZeroMorphisms := inferInstance
  let m5 := canonicalM5w (n := n) (r := T.k * d + T.s) hc hrq
  exact ⟨template_pc_step_exact T (F := canonicalΨ p a n (T.k * d + T.s) c)
      hd (by omega) hn0 m5,
    template_ns_step_exact T (F := canonicalΨ p a n (T.k * d + T.s) c) (by omega) hn0 m5⟩

end Algebra

/-! ### From a witness family to (P) and the four types -/

/-- Top-power witnesses exist for every support `r`, every `p`-power above `r`, and every
retained rank `n ≥ W r`, over the field `L`. -/
def TopWitnessHypothesis (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharP L p] (W : ℕ → ℕ) :
    Prop :=
  ∀ r a n : ℕ, r < p ^ a → W r ≤ n →
    ∃ c : Fin a → L, Generic p c ∧ ∃ w : MonoidAlgebra L (Sfin (n + p ^ a)),
      IsTopWitness p r a n c w

section Profiles
variable {R : Type} [Field R] (T : Template R) (p : ℕ) [Fact p.Prime] (L : Type) [Field L]
  [CharP L p] [Algebra R L]

theorem step_of_top_hypothesis {W : ℕ → ℕ} (H : TopWitnessHypothesis p L W) {d a n : ℕ}
    (hd : 1 ≤ d) (hn0 : T.n0 ≤ n) (hW : W (T.k * d + T.s) ≤ n) (hrq : T.k * d + T.s < p ^ a) :
    (T.pcProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ T.pcProfile n ≤ (d : ℕ∞)) ∧
    (T.nsProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ T.nsProfile n ≤ (d : ℕ∞)) := by
  obtain ⟨c, hc, w, hw⟩ := H (T.k * d + T.s) a n hrq hW
  have hh := template_step_of_top_witness (T.map (algebraMap R L)) hd hn0 hrq le_rfl hrq hc hw
  rw [← pcDegree_le_iff, ← pcDegree_le_iff, ← nsDegree_le_iff, ← nsDegree_le_iff] at hh
  change ((T.map (algebraMap R L)).pcProfile (n + p ^ a) ≤ d ↔
    (T.map (algebraMap R L)).pcProfile n ≤ d) ∧
    ((T.map (algebraMap R L)).nsProfile (n + p ^ a) ≤ d ↔
    (T.map (algebraMap R L)).nsProfile n ≤ d) at hh
  rw [T.pcProfile_map, T.pcProfile_map, T.nsProfile_map, T.nsProfile_map] at hh
  exact hh

theorem periodic_of_top_hypothesis {W : ℕ → ℕ} (hWm : Monotone W)
    (H : TopWitnessHypothesis p L W) :
    PeriodicProfile T.pcProfile (wOnset T.k T.s T.n0 W) (period p T.k T.s) ∧
    PeriodicProfile T.nsProfile (wOnset T.k T.s T.n0 W) (period p T.k T.s) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hge : ∀ d, d + 1 ≤ wOnset T.k T.s T.n0 W d := by
    intro d
    unfold wOnset
    split
    · have := T.hn0; omega
    · exact le_trans (onset_ge T.s T.hk T.hn0 d) (le_max_left _ _)
  have key : ∀ (h : ℕ → ℕ∞), ZeroStable T.n0 h →
      (∀ d a n, 1 ≤ d → T.n0 ≤ n → W (T.k * d + T.s) ≤ n → T.k * d + T.s < p ^ a →
        (h (n + p ^ a) ≤ (d : ℕ∞) ↔ h n ≤ (d : ℕ∞))) →
      PeriodicProfile h (wOnset T.k T.s T.n0 W) (period p T.k T.s) := by
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
      have hper : period p T.k T.s d = leastPowGt p (T.k * d + T.s) := by
        unfold period; rw [if_neg (by omega)]
      rw [hper] at hc
      obtain ⟨a, ha⟩ := leastPowGt_isPow hp (T.k * d + T.s)
      have hgt := leastPowGt_gt hp (T.k * d + T.s)
      rw [ha] at hc hgt
      have hkt : T.k * t ≤ T.k * d := Nat.mul_le_mul_left T.k htd
      have hWt : W (T.k * t + T.s) ≤ W (T.k * d + T.s) := hWm (by omega)
      have hn0d : T.n0 ≤ onset T.k T.s T.n0 d := n0_le_onset _ _ _ d
      refine congr_of_step (Pr := fun x => h x ≤ (t : ℕ∞)) (q := p ^ a)
        (B := max T.n0 (W (T.k * t + T.s))) ?_ ?_ ?_ hc
      · intro x hx
        exact hstep t a x (by omega) (le_trans (le_max_left _ _) hx)
          (le_trans (le_max_right _ _) hx) (by omega)
      · exact max_le (le_trans hn0d (le_trans (le_max_left _ _) hn))
          (le_trans hWt (le_trans (le_max_right _ _) hn))
      · exact max_le (le_trans hn0d (le_trans (le_max_left _ _) hm))
          (le_trans hWt (le_trans (le_max_right _ _) hm))
  exact ⟨key _ T.zeroStable_pc
      (fun d a n hd hn0 hW hrq => (step_of_top_hypothesis T p L H hd hn0 hW hrq).1),
    key _ T.zeroStable_ns
      (fun d a n hd hn0 hW hrq => (step_of_top_hypothesis T p L H hd hn0 hW hrq).2)⟩

end Profiles
end ClaudeCP
