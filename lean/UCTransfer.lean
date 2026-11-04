/-
Uniform consequences, Claude return 001 (5 October 2026).  Part 2: the concrete transfer of a
fully invariant target through the ACTUAL exact deletion functor.

The distinguished map of the existing PC datum is replaced by the target matrix `targetM d`
(singleton empty-support source, entry `γ(y)`):

* `concDatumG`, `concDatumG_stage`: the concrete datum of actual polynomial spaces with
  `c = (a ↦ a • G_t)`; its closure stages are literally those of the existing datum (the stages
  never use `c`);
* `targetMem_iff`: categorical membership of the target in stage `j` is membership of the actual
  polynomial in the `j`-th stage of the actual PC closure;
* `catDatumG`, `ωCompatG`, `pc_target_stage_iff`, `ns_target_iff`: the categorical datum inside an
  `M4` realisation, and the bridge to actual polynomial spaces (all comparison data constructed);
* `ΦCompatGW`: for an `M5w` structure, the compatibility of the deletion functor with the new
  datum; its new field is the EXISTING `M5w.δ_mat` applied to `targetM`, not a new hypothesis;
* `target_pc_step_exact`, `target_ns_step_exact`: target membership transfers along any exact
  functor carrying `M5w` data, using that the trivial source is simple and survives;
* `target_step_of_exact`: the same for the actual shifted functor `canonicalΨ` with the actual
  `canonicalM5w`;
* **`target_transfer`**: the unconditional two-way transfer over every field of characteristic
  `p`, for every degree `d` (including `d = 0` and `d` below the target degree), with `q = p^a`
  above the unchanged support budget `kd + s` and retained rank `n ≥ max(n₀, nG, 2(kd+s) - 1)`.
  The exactness input is `LinearFinal.exactness_linear`, which is unconditional.
-/
import UCTarget
import LinearFinal

set_option autoImplicit false

universe v₂ v₃ v₄ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace UniformConsequence

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.Concrete
open DegreeProfilesReview.Deletion DegreeProfilesReview.Transport

variable {K : Type} [Field K] {T : Template K}

namespace Target

variable (G : Target T) {d : ℕ} (hd : 1 ≤ d)

/-! ### The concrete datum with the target as distinguished map -/

/-- The PC datum of actual polynomial spaces at size `t`, with distinguished map
`a ↦ a • G_t` instead of the constant. -/
noncomputable def concDatumG (t : ℕ) : PCDatum (ModuleCat.{0} K) :=
  { T.concDatum hd t with c := ModuleCat.ofHom (G.targetMap t d) }

/-- The distinguished map of the concrete target datum is `a ↦ a • G_t` (definitional check). -/
theorem concDatumG_c (t : ℕ) : (G.concDatumG hd t).c = ModuleCat.ofHom (G.targetMap t d) := rfl

/-- The closure stages do not depend on the distinguished map. -/
theorem concDatumG_stage (t j : ℕ) :
    (G.concDatumG hd t).stage j = (T.concDatum hd t).stage j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show (G.concDatumG hd t).next ((G.concDatumG hd t).stage j) =
      (T.concDatum hd t).next ((T.concDatum hd t).stage j)
    rw [ih]
    rfl

/-- **Concrete bridge, PC.**  Beyond `n₀`, categorical membership of the target in the `j`-th
stage is membership of the actual realised target in the `j`-th stage of the actual closure. -/
theorem targetMem_iff {t : ℕ} (ht : T.n0 ≤ t) (j : ℕ) :
    (G.concDatumG hd t).ConstMem j ↔
      ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) ∈
        V (T.inst t) d j := by
  unfold PCDatum.ConstMem PCDatum.quot
  rw [comp_cokernel_π_eq_zero_iff, G.concDatumG_stage hd t j,
    ← rng_stage hd (T.axMap d t) (T.inst t) (T.range_axMap d ht) j]
  unfold rng
  rw [G.Gtr_mem_map_iff]
  exact G.range_targetMap_le_iff t d _

/-! ### The categorical datum inside an `M4` realisation -/

section Rank

variable {t : ℕ} {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (P : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) t B)

/-- The PC datum inside `B` with distinguished map the target matrix. -/
noncomputable def catDatumG : PCDatum B :=
  { T.catDatum hd P with
    c := P.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (G.targetM d) }

/-- The distinguished map of the target datum is the target matrix (definitional check). -/
theorem catDatumG_c :
    (G.catDatumG hd P).c = P.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (G.targetM d) :=
  rfl

/-- The underlying-space functor carries the categorical target datum to the actual one.
Every comparison isomorphism and square is constructed; the new square comes from the actual
realisation of the target matrix. -/
noncomputable def ωCompatG : PCCompat P.ω (G.catDatumG hd P) (G.concDatumG hd t) :=
  { T.ωCompat hd P with
    hc := P.sq_of_realise _ _ (G.targetM d) _ _ _ (G.targetM_realise t d) }

/-- **Bridge, PC.**  Beyond `n₀`, the target lies in the `j`-th categorical stage iff the actual
realised target lies in the `j`-th stage of the actual closure of the instance at size `t`. -/
theorem pc_target_stage_iff (ht : T.n0 ≤ t) (j : ℕ) :
    (G.catDatumG hd P).ConstMem j ↔
      ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) ∈
        V (T.inst t) d j :=
  (const_mem_iff P.ω (G.ωCompatG hd P) j).trans (G.targetMem_iff hd ht j)

/-- **Bridge, NS.**  Beyond `n₀`, the target maps to zero in the cokernel of the categorical
certificate map iff the actual realised target lies in the actual NS span. -/
theorem ns_target_iff (ht : T.n0 ≤ t) :
    P.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (G.targetM d) ≫
        cokernel.π (P.mat (T.cert_bounded d) (T.mon_bounded' d) (T.certM d)) = 0 ↔
      ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) ∈
        NSspan (T.inst t) d := by
  have hA := P.sq_of_realise (T.cert_bounded d) (T.mon_bounded' d) (T.certM d)
    (LinearEquiv.refl K _) (monBasis (T.Var.Rk t) K d) (T.certMap d t) (T.certM_realise d t)
  have hj := P.sq_of_realise (BasisSystem.unit_bounded _) (T.mon_bounded' d) (G.targetM d)
    (Template.unitEquiv (K := K) t) (monBasis (T.Var.Rk t) K d) (G.targetMap t d)
    (G.targetM_realise t d)
  have h1 := image_membership_iff P.ω
    (P.mat (T.cert_bounded d) (T.mon_bounded' d) (T.certM d))
    (P.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (G.targetM d))
    (ModuleCat.ofHom (T.certMap d t)) (ModuleCat.ofHom (G.targetMap t d))
    _ _ _ hA hj
  refine h1.trans ?_
  rw [comp_cokernel_π_eq_zero_iff, ← T.range_certMap d ht, G.Gtr_mem_map_iff]
  exact G.range_targetMap_le_iff t d _

end Rank

/-! ### Compatibility with the deletion functor, from the existing `δ_mat` -/

section Deletion

variable {N n : ℕ}
  {BN : Type u₂} [Category.{v₂} BN] [Abelian BN] {Bn : Type u₂} [Category.{v₂} Bn] [Abelian Bn]
  {PN : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) N BN}
  {Pn : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) n Bn} {Φ : BN ⥤ Bn}

/-- **Actual target-matrix transport.**  The deletion functor carries the rank-`N` realisation of
the target matrix to its rank-`n` realisation, through the comparison isomorphisms of the trivial
module and of `P_{≤ d}`.  This is the existing field `M5w.δ_mat`, instantiated at `targetM d`. -/
theorem targetM_transport (m5 : M5w.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ) :
    Φ.map (PN.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (G.targetM d)) ≫
        (m5.δ (T.Var.mon d) (T.mon_bounded' d)).hom =
      (m5.δ BasisSystem.unit (BasisSystem.unit_bounded _)).hom ≫
        Pn.mat (BasisSystem.unit_bounded _) (T.mon_bounded' d) (G.targetM d) :=
  m5.δ_mat _ _ (G.targetM d)

/-- **The deletion functor carries the rank-`N` target datum to the rank-`n` target datum.**
All fields are those of the existing `ΦCompatW`, except the distinguished square, which is the
existing `M5w.δ_mat` applied to the target matrix (`targetM_transport`). -/
noncomputable def ΦCompatGW (m5 : M5w.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ) :
    PCCompat Φ (G.catDatumG hd PN) (G.catDatumG hd Pn) :=
  { T.ΦCompatW hd m5 with hc := m5.δ_mat _ _ (G.targetM d) }

end Deletion

/-! ### One deletion step for the target, along any exact functor with `M5w` data -/

section Step

variable {N n : ℕ} {BN Bn : Type 1} [Category.{0} BN] [Abelian BN] [Category.{0} Bn]
  [Abelian Bn]
  {PN : M4.{0, 0, 1, 1} K (T.k * d + T.s) N BN} {Pn : M4.{0, 0, 1, 1} K (T.k * d + T.s) n Bn}
  {F : BN ⥤ Bn} [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

include hd in
/-- **Target transfer, ordinary PC, abstract form.** -/
theorem target_pc_step_exact (hN : T.n0 ≤ N) (hn : T.n0 ≤ n)
    (m5 : M5w.{0, 0, 0, 1, 1, 1} PN Pn F) :
    ((G.Gtr N d : Pd (T.Var.Rk N) K d) : MvPolynomial (T.Var.Rk N) K) ∈ Vinf (T.inst N) d ↔
      ((G.Gtr n d : Pd (T.Var.Rk n) K d) : MvPolynomial (T.Var.Rk n) K) ∈
        Vinf (T.inst n) d := by
  haveI : Simple (G.catDatumG hd PN).U := SelfContainedCycle013.unit_simple PN
  rw [mem_Vinf_iff, mem_Vinf_iff]
  apply exists_congr
  intro j
  rw [← G.pc_target_stage_iff hd PN hN j, ← G.pc_target_stage_iff hd Pn hn j]
  exact ExactnessHandoff.const_mem_iff_of_simple F
    (SelfContainedCycle013.shifted_unit_nonzero T m5) (G.ΦCompatGW hd m5) j

/-- **Target transfer, Nullstellensatz, abstract form** (every `d`, including `d = 0`). -/
theorem target_ns_step_exact (hN : T.n0 ≤ N) (hn : T.n0 ≤ n)
    (m5 : M5w.{0, 0, 0, 1, 1, 1} PN Pn F) :
    ((G.Gtr N d : Pd (T.Var.Rk N) K d) : MvPolynomial (T.Var.Rk N) K) ∈ NSspan (T.inst N) d ↔
      ((G.Gtr n d : Pd (T.Var.Rk n) K d) : MvPolynomial (T.Var.Rk n) K) ∈
        NSspan (T.inst n) d := by
  haveI := SelfContainedCycle013.unit_simple PN
  rw [← G.ns_target_iff PN hN, ← G.ns_target_iff Pn hn]
  exact ExactnessHandoff.image_membership_iff_of_simple F
    (SelfContainedCycle013.shifted_unit_nonzero T m5)
    _ _ _ _ (m5.δ _ _) (m5.δ _ _) (m5.δ _ _) (m5.δ_mat _ _ _) (m5.δ_mat _ _ _)

end Step

/-! ### The actual shifted functor -/

section Canonical

open DegreeProfilesReview.SymRep DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor
open DegreeProfilesReview.ShiftedM5 SelfContainedCycle003 SelfContainedCycle004 ClaudeLinear

include hd in
/-- **Target transfer through the actual shifted functor** `canonicalΨ = ker z/(ker z ∩ im z)`
with its actual `canonicalM5w` data, whenever it is exact. -/
theorem target_step_of_exact {p : ℕ} [Fact p.Prime] [CharP K p] {a n : ℕ} (hn0 : T.n0 ≤ n)
    (hrq : T.k * d + T.s < p ^ a) {c : Fin a → K} (hc : Generic p c)
    (hE : ShiftedExact p a n (T.k * d + T.s) c) :
    (((G.Gtr (n + p ^ a) d : Pd _ K d) : MvPolynomial _ K) ∈ Vinf (T.inst (n + p ^ a)) d ↔
      ((G.Gtr n d : Pd _ K d) : MvPolynomial _ K) ∈ Vinf (T.inst n) d) ∧
    (((G.Gtr (n + p ^ a) d : Pd _ K d) : MvPolynomial _ K) ∈ NSspan (T.inst (n + p ^ a)) d ↔
      ((G.Gtr n d : Pd _ K d) : MvPolynomial _ K) ∈ NSspan (T.inst n) d) := by
  haveI := hE.1
  haveI := hE.2
  letI : (canonicalΨ p a n (T.k * d + T.s) c).PreservesZeroMorphisms := inferInstance
  let m5 := canonicalM5w (n := n) (r := T.k * d + T.s) hc hrq
  exact ⟨G.target_pc_step_exact hd (F := canonicalΨ p a n (T.k * d + T.s) c) (by omega) hn0 m5,
    G.target_ns_step_exact (F := canonicalΨ p a n (T.k * d + T.s) c) (by omega) hn0 m5⟩

end Canonical

end Target

/-! ### Degree zero -/

namespace Target

variable (G : Target T)

/-- The rank-independent condition for derivability of the target in degree zero. -/
def ZeroDerivable : Prop := G.deg = 0 ∧ (G.γ 0 = 0 ∨ T.HasConstAxiom)

theorem V0_le_Pd {σ : Type*} (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    V0 Γ d ≤ restrictTotalDegree σ K d :=
  V_le_W Γ d 0

/-- **Degree-zero stabilisation for the target.**  Beyond `max(n₀, nG)`, the target is a
degree-zero consequence iff the rank-independent condition `ZeroDerivable` holds. -/
theorem mem_V0_zero_iff {t : ℕ} (hn0 : T.n0 ≤ t) (hnG : G.nG ≤ t) :
    G.poly t ∈ V0 (T.inst t) 0 ↔ G.ZeroDerivable := by
  constructor
  · intro h
    have hdeg0 : G.deg = 0 := by
      have := (mem_restrictTotalDegree _ _ _).mp (V0_le_Pd (T.inst t) 0 h)
      rw [G.totalDegree_poly hnG] at this
      omega
    refine ⟨hdeg0, ?_⟩
    by_cases hγ : G.γ 0 = 0
    · exact Or.inl hγ
    · right
      rw [G.poly_eq_C_of_deg_zero hdeg0] at h
      have := (V0 (T.inst t) 0).smul_mem (G.γ 0)⁻¹ h
      rw [smul_eq_C_mul, ← C_mul, inv_mul_cancel₀ hγ, C_1] at this
      exact (T.one_mem_V0_zero_iff hn0).mp this
  · rintro ⟨hdeg0, hγ | hc⟩
    · rw [G.poly_eq_C_of_deg_zero hdeg0, hγ, C_0]
      exact Submodule.zero_mem _
    · rw [G.poly_eq_C_of_deg_zero hdeg0]
      have h1 := (T.one_mem_V0_zero_iff hn0).mpr hc
      have := (V0 (T.inst t) 0).smul_mem (G.γ 0) h1
      rwa [smul_eq_C_mul, mul_one] at this

theorem pc_zero_iff {t : ℕ} (hn0 : T.n0 ≤ t) (hnG : G.nG ≤ t) :
    G.poly t ∈ Vinf (T.inst t) 0 ↔ G.ZeroDerivable := by
  rw [Vinf_zero]; exact G.mem_V0_zero_iff hn0 hnG

theorem ns_zero_iff {t : ℕ} (hn0 : T.n0 ≤ t) (hnG : G.nG ≤ t) :
    G.poly t ∈ NSspan (T.inst t) 0 ↔ G.ZeroDerivable := by
  rw [Template.NSspan_zero]; exact G.mem_V0_zero_iff hn0 hnG

end Target

/-! ### The unconditional transfer over every field of characteristic `p` -/

section Final

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] {T : Template R}

/-- **Concrete invariant-target transfer (unconditional).**  Let `T` be a uniform template over a
field `R` of prime characteristic `p` and `G` a fully invariant uniform target.  For every degree
`d`, every `q = p^a` above the support budget `kd + s` and every retained rank
`n ≥ max(n₀, nG)` with `n ≥ 2(kd+s) - 1`:

  `G_{n+q}` is a degree-`d` ordinary-PC consequence of `T_{n+q}` iff `G_n` is one of `T_n`, and
  `G_{n+q}` has a total-product degree-`d` NS identity from `T_{n+q}` iff `G_n` has one from `T_n`.

Membership is in the actual consequence spaces (`Vinf`, the closure of all degree-`≤ d` PC lines,
and `NSspan`, the image of the certificate map).  For `d ≥ deg G` the proof is the exact-deletion
transfer over the algebraic closure followed by field descent; for `1 ≤ d < deg G` both sides
are false; for `d = 0` both sides are the rank-independent condition `ZeroDerivable`. -/
theorem target_transfer (G : Target T) {d a n : ℕ} (hn0 : T.n0 ≤ n) (hnG : G.nG ≤ n)
    (hW : 2 * (T.k * d + T.s) - 1 ≤ n) (hrq : T.k * d + T.s < p ^ a) :
    (G.poly (n + p ^ a) ∈ Vinf (T.inst (n + p ^ a)) d ↔ G.poly n ∈ Vinf (T.inst n) d) ∧
    (G.poly (n + p ^ a) ∈ NSspan (T.inst (n + p ^ a)) d ↔ G.poly n ∈ NSspan (T.inst n) d) := by
  have hn0' : T.n0 ≤ n + p ^ a := le_trans hn0 (Nat.le_add_right _ _)
  have hnG' : G.nG ≤ n + p ^ a := le_trans hnG (Nat.le_add_right _ _)
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    rw [G.pc_zero_iff hn0' hnG', G.pc_zero_iff hn0 hnG, G.ns_zero_iff hn0' hnG',
      G.ns_zero_iff hn0 hnG]
    exact ⟨Iff.rfl, Iff.rfl⟩
  by_cases hdeg : d < G.deg
  · have h1 := G.not_mem_of_lt hnG' hdeg (T.inst (n + p ^ a))
    have h2 := G.not_mem_of_lt hnG hdeg (T.inst n)
    exact ⟨iff_of_false h1.1 h2.1, iff_of_false h1.2 h2.2⟩
  push_neg at hdeg
  -- the exact-deletion step over the algebraic closure
  set L := AlgebraicClosure R
  obtain ⟨c, hc, hE⟩ := LinearFinal.exactness_linear p L (T.k * d + T.s) a n hrq hW
  have hstep := (G.map (algebraMap R L)).target_step_of_exact hd hn0 hrq hc hE
  have hγ : ∀ m, (G.map (algebraMap R L)).γ m ≠ 0 → BasisSystem.mdeg m ≤ d :=
    fun m hm => le_trans (G.mdeg_le_deg (G.map_γ_ne _ hm)) hdeg
  rw [(G.map (algebraMap R L)).Gtr_coe_of hγ, (G.map (algebraMap R L)).Gtr_coe_of hγ,
    G.map_poly, G.map_poly, T.inst_map, T.inst_map] at hstep
  rw [mem_Vinf_map_iff, mem_Vinf_map_iff, mem_NSspan_map_iff, mem_NSspan_map_iff] at hstep
  exact hstep

/-- The same transfer in the paper's conservative retained range `n > 2(kd+s)`. -/
theorem target_transfer_paper_range (G : Target T) {d a n : ℕ} (hn0 : T.n0 ≤ n)
    (hnG : G.nG ≤ n) (hn : 2 * (T.k * d + T.s) < n) (hrq : T.k * d + T.s < p ^ a) :
    (G.poly (n + p ^ a) ∈ Vinf (T.inst (n + p ^ a)) d ↔ G.poly n ∈ Vinf (T.inst n) d) ∧
    (G.poly (n + p ^ a) ∈ NSspan (T.inst (n + p ^ a)) d ↔ G.poly n ∈ NSspan (T.inst n) d) :=
  target_transfer p G hn0 hnG (by omega) hrq

/-- The transfer stated for the actual proof systems: ordinary PC derivations ending in the
actual polynomial `G_n`, and total-product NS identities `G_n = ∑ a_f f`. -/
theorem target_transfer_derivations (G : Target T) {d a n : ℕ} (hn0 : T.n0 ≤ n)
    (hnG : G.nG ≤ n) (hW : 2 * (T.k * d + T.s) - 1 ≤ n) (hrq : T.k * d + T.s < p ^ a) :
    (Derives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a)) ↔ Derives (T.inst n) d (G.poly n)) ∧
    (NSDerives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a)) ↔
      NSDerives (T.inst n) d (G.poly n)) := by
  rw [derives_iff_mem_Vinf, derives_iff_mem_Vinf, nsDerives_iff_mem_NSspan,
    nsDerives_iff_mem_NSspan]
  exact target_transfer p G hn0 hnG hW hrq

end Final

end UniformConsequence
