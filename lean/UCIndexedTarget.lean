/-
Uniform consequences, Claude return 002 (5 October 2026).  Part 1: bounded-support indexed
targets.

An *indexed uniform target* for a template `T` consists of a basis system `B` of target indices
whose objects use at most `t` labels, a degree bound `DG`, and ONE rank-independent coefficient
rule `γ(b, μ)` on (global index, global monomial), invariant under simultaneous relabelling of
`b` and `μ`, vanishing when `deg μ > DG`.  At universe size `n` the target with index `b ∈ B_n` is
`G_{b,n} = ∑_{supp μ ⊆ [n]} γ(b, μ) μ`.

Proved here, with no hypotheses:
* `inflate`: the same template (same variables, axiom indices, coefficients, hence literally the
  same instances `inflate_inst`) with the bookkeeping parameters `k' = 2k`, `s' = s + t`; only the
  support bookkeeping changes;
* `aux`: the auxiliary template whose axiom indices are the TARGET indices and whose axioms are
  the targets.  It is used only to reuse the degree and matrix lemmas of `Templates.lean` and
  `TemplateMatrices.lean`; the targets are never added to the axioms of `T`;
* `totalDegree_poly`: beyond `max 1 (k·DG + t)` the degree of `G_{b,n}` is the rank-independent
  number `deg b`; `maxDeg` is the largest of these, attained at every rank `≥ t`;
* `AllPC`, `AllNS`: EVERY target indexed by `B_n` is a degree-`d` consequence;
* `not_all_of_lt`: below `maxDeg` both predicates fail; `allPC_zero_iff`, `allNS_zero_iff`:
  degree zero is the rank-independent condition `ZeroDerivable`;
* `rename_mem_Vinf`: the PC closure of an instance is invariant under `S_n` (the NS span is
  `ClaudeC017.rename_mem_NSspan`);
* `orbit`: the restriction to ONE fixed global orbit; `orbit_transitive`: at every rank the
  rank-`n` indices of one global orbit form one `S_n`-orbit; `rep_iff_orbit_pc/ns`: a
  representative is a consequence iff the whole orbit is.
-/
import UCClassification
import C017TypeAgreement

set_option autoImplicit false

open MvPolynomial

namespace UniformConsequence.Indexed

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.SymRep
open UniformConsequence

variable {K : Type} [Field K]

/-! ### Bookkeeping inflation of a template -/

/-- The same template with the support bookkeeping inflated to `k' = 2k`, `s' = s + t` (and a
starting rank compatible with these).  Variables, axiom indices and coefficients are unchanged. -/
@[reducible] def inflate (T : Template K) (t : ℕ) : Template K where
  Var := T.Var
  Ax := T.Ax
  k := 2 * T.k
  s := T.s + t
  D := T.D
  n0 := max T.n0 (2 * T.k * T.D + (T.s + t))
  hk := by have := T.hk; omega
  hn0 := le_trans T.hn0 (le_max_left _ _)
  hn0' := le_max_right _ _
  var_bounded := T.var_bounded.mono (by omega)
  ax_bounded := T.ax_bounded.mono (Nat.le_add_right _ _)
  coeff := T.coeff
  coeff_inv := T.coeff_inv
  coeff_deg := T.coeff_deg

/-- **The inflated template has literally the same instances.** -/
theorem inflate_inst (T : Template K) (t n : ℕ) : (inflate T t).inst n = T.inst n := rfl

/-- The axiom map of degree `≤ d` is literally unchanged by the inflation. -/
theorem inflate_axMap (T : Template K) (t d n : ℕ) :
    (inflate T t).axMap d n = T.axMap d n := rfl

/-- The NS certificate map is literally unchanged by the inflation. -/
theorem inflate_certMap (T : Template K) (t d n : ℕ) :
    (inflate T t).certMap d n = T.certMap d n := rfl

/-- The class support of the inflated template is `2kd + s + t`. -/
theorem inflate_support (T : Template K) (t d : ℕ) :
    (inflate T t).k * d + (inflate T t).s = 2 * T.k * d + T.s + t := by
  show 2 * T.k * d + (T.s + t) = _
  ring

/-! ### General invariance of the PC closure -/

section Rename

variable {σ τ : Type*}

/-- Renaming variables maps derivations to derivations, provided the axioms are carried into the
new axiom set.  Degrees cannot increase. -/
theorem derives_rename (e : σ → τ) {Γ : Set (MvPolynomial σ K)} {Γ' : Set (MvPolynomial τ K)}
    (hΓ : ∀ f ∈ Γ, rename e f ∈ Γ') {d : ℕ} {f : MvPolynomial σ K} (hf : Derives Γ d f) :
    Derives Γ' d (rename e f) := by
  obtain ⟨l, hl, hdeg, hfl⟩ := hf
  refine ⟨l.map (rename e), ?_, ?_, List.mem_map_of_mem hfl⟩
  · clear hdeg hfl
    induction hl with
    | nil => exact IsProof.nil
    | ax _ hf ih => exact IsProof.ax ih (hΓ _ hf)
    | @lin l f _ hf ih =>
      refine IsProof.lin ih ?_
      have h1 : rename e f ∈ (Submodule.span K {g | g ∈ l}).map (rename e).toLinearMap :=
        Submodule.mem_map_of_mem hf
      rw [Submodule.map_span] at h1
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨g, hg, rfl⟩
      exact List.mem_map_of_mem hg
    | @mulX l g i _ hg ih =>
      rw [List.map_cons, map_mul, rename_X]
      exact IsProof.mulX (e i) ih (List.mem_map_of_mem hg)
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact le_trans (totalDegree_rename_le e g0) (hdeg g0 hg0)

end Rename

/-- The ordinary-PC closure of an instance is invariant under `S_n`. -/
theorem rename_mem_Vinf (T : Template K) {n : ℕ} (g : Sfin n) {d : ℕ}
    {f : MvPolynomial (T.Var.Rk n) K} (hf : f ∈ Vinf (T.inst n) d) :
    rename (fun v => g • v) f ∈ Vinf (T.inst n) d := by
  rw [← derives_iff_mem_Vinf] at hf ⊢
  refine derives_rename _ ?_ hf
  rintro _ ⟨i, rfl⟩
  exact ⟨g • i, (ClaudeC017.rename_poly T g i).symm⟩

/-! ### Moving labels -/

/-- Every global object of support `≤ n` has a copy at rank `n`. -/
theorem exists_up (𝒰 : BasisSystem) {r n : ℕ} (hU : 𝒰.Bounded r) (hrn : r ≤ n) (o : 𝒰.Obj) :
    ∃ (g : Equiv.Perm ℕ) (b : 𝒰.Rk n), 𝒰.up n b = g • o := by
  have hcard : ((∅ : Finset ℕ) ∪ 𝒰.supp o).card ≤ n := by
    rw [Finset.empty_union]; exact le_trans (hU o) hrn
  obtain ⟨σ, -, hσ⟩ := exists_perm_fix_move' ∅ (𝒰.supp o) n (Finset.empty_subset _) hcard
  have hsupp : 𝒰.supp (σ • o) ⊆ Finset.range n := by
    rw [𝒰.supp_smul]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hσ y hy)
  obtain ⟨b, hb⟩ := (𝒰.range_up n _).mpr hsupp
  exact ⟨σ, b, hb⟩

/-- A permutation mapping `[n]` into `[n]` agrees on `[n]` with an element of `S_n`. -/
theorem exists_Sfin_of_maps (σ' : Equiv.Perm ℕ) (n : ℕ) (h : ∀ x, x < n → σ' x < n) :
    ∃ σ : Sfin n, ∀ x, x < n → σ.1 x = σ' x := by
  classical
  have himg : (Finset.range n).image σ' = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_range.mpr (h x (Finset.mem_range.mp hx))
    · rw [Finset.card_image_of_injective _ σ'.injective]
  have hiff : ∀ x, σ' x < n ↔ x < n := by
    intro x
    refine ⟨fun hx => ?_, h x⟩
    have : σ' x ∈ (Finset.range n).image σ' := by rw [himg]; exact Finset.mem_range.mpr hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp this
    rw [σ'.injective hyx] at hy
    exact Finset.mem_range.mp hy
  let τ : Equiv.Perm ℕ := Equiv.Perm.ofSubtype (σ'.subtypePerm (p := fun x => x < n) hiff)
  have hτ1 : ∀ x, x < n → τ x = σ' x := fun x hx =>
    Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun x => x < n) hiff hx
  have hτ2 : ∀ x, n ≤ x → τ x = x := fun x hx =>
    Equiv.Perm.ofSubtype_apply_of_not_mem (σ'.subtypePerm (p := fun x => x < n) hiff) (by simp only; omega)
  exact ⟨⟨τ, hτ2⟩, hτ1⟩

/-- **Transitivity at rank `n`.**  Two rank-`n` objects in the same global orbit are related by
an element of `S_n`. -/
theorem orbit_transitive (𝒰 : BasisSystem) {n : ℕ} {b b' : 𝒰.Rk n} {o : 𝒰.Obj}
    {g g' : Equiv.Perm ℕ} (hb : 𝒰.up n b = g • o) (hb' : 𝒰.up n b' = g' • o) :
    ∃ σ : Sfin n, σ • b = b' := by
  classical
  set h : Equiv.Perm ℕ := g' * g⁻¹ with hh
  have hhu : h • 𝒰.up n b = 𝒰.up n b' := by
    rw [hb, hb', hh, mul_smul, inv_smul_smul]
  set A := 𝒰.supp (𝒰.up n b) with hA
  have hAn : A ⊆ Finset.range n := 𝒰.supp_up n b
  have hA1 : A.image h ⊆ Finset.range n := by
    rw [← 𝒰.supp_smul, hhu]; exact 𝒰.supp_up n b'
  have hcard : (A.image h ∪ (Finset.range n).image h).card ≤ n := by
    rw [← Finset.image_union, Finset.union_eq_right.mpr hAn,
      Finset.card_image_of_injective _ h.injective, Finset.card_range]
  obtain ⟨ρ, hρA, hρB⟩ := exists_perm_fix_move' _ _ n hA1 hcard
  have hmaps : ∀ x, x < n → (ρ * h) x < n := by
    intro x hx
    exact hρB _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hx))
  obtain ⟨σ, hσ⟩ := exists_Sfin_of_maps (ρ * h) n hmaps
  refine ⟨σ, 𝒰.up_inj n ?_⟩
  rw [up_smul, ← hhu]
  -- `σ` agrees with `h` on the support of `up b`
  have hagree : ∀ x ∈ A, σ.1 x = h x := by
    intro x hx
    rw [hσ x (Finset.mem_range.mp (hAn hx)), Equiv.Perm.mul_apply]
    exact hρA _ (Finset.mem_image_of_mem _ hx)
  have hfix := 𝒰.fixed (h⁻¹ * σ.1) (𝒰.up n b) (fun x hx => by
    rw [Equiv.Perm.mul_apply, hagree x hx]
    exact h.symm_apply_apply x)
  calc σ.1 • 𝒰.up n b = h • ((h⁻¹ * σ.1) • 𝒰.up n b) := by
        rw [← mul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = h • 𝒰.up n b := by rw [hfix]

/-! ### Indexed targets -/

/-- **A bounded-support indexed uniform target** for the template `T`. -/
structure ITarget (T : Template K) where
  /-- The target indices. -/
  B : BasisSystem
  /-- A bound on the number of labels of an index. -/
  t : ℕ
  hB : B.Bounded t
  /-- A fixed bound on the degree of every target. -/
  DG : ℕ
  /-- The rank-independent coefficient rule on (global index, global monomial). -/
  γ : B.Obj → (T.Var.Obj →₀ ℕ) → K
  γ_inv : ∀ (g : Equiv.Perm ℕ) (b : B.Obj) (m : T.Var.Obj →₀ ℕ),
    γ (g • b) (T.Var.monSMul g m) = γ b m
  γ_deg : ∀ b m, γ b m ≠ 0 → BasisSystem.mdeg m ≤ DG

namespace ITarget

variable {T : Template K} (G : ITarget T)

/-- The auxiliary template whose axioms are the targets (bookkeeping only: it is used to reuse
the degree and matrix lemmas; it is never combined with the axioms of `T`). -/
noncomputable def aux : Template K where
  Var := T.Var
  Ax := G.B
  k := T.k
  s := G.t
  D := G.DG
  n0 := max 1 (T.k * G.DG + G.t)
  hk := T.hk
  hn0 := le_max_left _ _
  hn0' := le_max_right _ _
  var_bounded := T.var_bounded
  ax_bounded := G.hB
  coeff := G.γ
  coeff_inv := G.γ_inv
  coeff_deg := G.γ_deg

/-- **The target polynomial** `G_{b,n}`. -/
noncomputable def poly (n : ℕ) (b : G.B.Rk n) : MvPolynomial (T.Var.Rk n) K := G.aux.poly n b

theorem coeff_poly (n : ℕ) (b : G.B.Rk n) (m : T.Var.Rk n →₀ ℕ) :
    MvPolynomial.coeff m (G.poly n b) = G.γ (G.B.up n b) (T.Var.monUp n m) := rfl

/-- The rank-independent degree of the target with global index `b`. -/
noncomputable def deg (b : G.B.Obj) : ℕ := G.aux.axDeg b

theorem deg_smul (g : Equiv.Perm ℕ) (b : G.B.Obj) : G.deg (g • b) = G.deg b :=
  G.aux.axDeg_smul g b

theorem deg_le_DG (b : G.B.Obj) : G.deg b ≤ G.DG := G.aux.axDeg_le_D b

theorem mdeg_le_deg {b : G.B.Obj} {m : T.Var.Obj →₀ ℕ} (h : G.γ b m ≠ 0) :
    BasisSystem.mdeg m ≤ G.deg b :=
  G.aux.le_axDeg (i := b) h

/-- The fixed starting rank of target-degree stabilisation, `max 1 (k·DG + t)`. -/
theorem aux_n0 : G.aux.n0 = max 1 (T.k * G.DG + G.t) := rfl

theorem t_le_aux_n0 : G.t ≤ G.aux.n0 := le_trans (Nat.le_add_left _ _) (le_max_right _ _)

theorem totalDegree_poly_le (n : ℕ) (b : G.B.Rk n) :
    (G.poly n b).totalDegree ≤ G.deg (G.B.up n b) :=
  G.aux.totalDegree_poly_le n b

/-- **Target-degree stabilisation.** -/
theorem totalDegree_poly {n : ℕ} (hn : G.aux.n0 ≤ n) (b : G.B.Rk n) :
    (G.poly n b).totalDegree = G.deg (G.B.up n b) :=
  G.aux.totalDegree_poly hn b

open Classical in
/-- The largest target degree (over all global indices; it is attained at every rank `≥ t`). -/
noncomputable def maxDeg : ℕ := Nat.find (⟨G.DG, G.deg_le_DG⟩ : ∃ e, ∀ b, G.deg b ≤ e)

theorem deg_le_maxDeg (b : G.B.Obj) : G.deg b ≤ G.maxDeg := by
  classical
  exact Nat.find_spec (⟨G.DG, G.deg_le_DG⟩ : ∃ e, ∀ b, G.deg b ≤ e) b

theorem maxDeg_le_DG : G.maxDeg ≤ G.DG := by
  classical
  exact Nat.find_min' _ G.deg_le_DG

theorem exists_deg_eq_maxDeg (h : 0 < G.maxDeg) : ∃ b, G.deg b = G.maxDeg := by
  classical
  have hmin : ¬ ∀ b, G.deg b ≤ G.maxDeg - 1 :=
    Nat.find_min (⟨G.DG, G.deg_le_DG⟩ : ∃ e, ∀ b, G.deg b ≤ e) (by unfold maxDeg at h ⊢; omega)
  push_neg at hmin
  obtain ⟨b, hb⟩ := hmin
  exact ⟨b, le_antisymm (G.deg_le_maxDeg b) (by omega)⟩

/-- Every target at rank `n ≥ aux.n0` has degree at most `maxDeg`, and some has exactly `maxDeg`
when `maxDeg > 0`. -/
theorem exists_poly_maxDeg {n : ℕ} (hn : G.aux.n0 ≤ n) (h : 0 < G.maxDeg) :
    ∃ b : G.B.Rk n, (G.poly n b).totalDegree = G.maxDeg := by
  obtain ⟨o, ho⟩ := G.exists_deg_eq_maxDeg h
  obtain ⟨g, b, hb⟩ := exists_up G.B G.hB (le_trans G.t_le_aux_n0 hn) o
  refine ⟨b, ?_⟩
  rw [G.totalDegree_poly hn, hb, G.deg_smul, ho]

/-! #### The membership predicates -/

/-- **Every target indexed by `B_n` has a degree-`d` ordinary PC derivation.** -/
def AllPC (n d : ℕ) : Prop := ∀ b : G.B.Rk n, G.poly n b ∈ Vinf (T.inst n) d

/-- **Every target indexed by `B_n` has a total-product degree-`d` NS identity.** -/
def AllNS (n d : ℕ) : Prop := ∀ b : G.B.Rk n, G.poly n b ∈ NSspan (T.inst n) d

theorem allPC_iff_derives (n d : ℕ) :
    G.AllPC n d ↔ ∀ b : G.B.Rk n, Derives (T.inst n) d (G.poly n b) :=
  forall_congr' fun _ => derives_iff_mem_Vinf.symm

theorem allNS_iff_nsDerives (n d : ℕ) :
    G.AllNS n d ↔ ∀ b : G.B.Rk n, NSDerives (T.inst n) d (G.poly n b) :=
  forall_congr' fun _ => nsDerives_iff_mem_NSspan.symm

theorem AllPC.mono {n d d' : ℕ} (h : d ≤ d') (hG : G.AllPC n d) : G.AllPC n d' := by
  intro b
  have := hG b
  rw [← derives_iff_mem_Vinf] at this ⊢
  exact this.mono h

theorem AllNS.mono {n d d' : ℕ} (h : d ≤ d') (hG : G.AllNS n d) : G.AllNS n d' := by
  intro b
  have := hG b
  rw [← nsDerives_iff_mem_NSspan] at this ⊢
  exact this.mono h

theorem allNS_le_allPC {n d : ℕ} (h : G.AllNS n d) : G.AllPC n d :=
  fun b => NSspan_le_Vinf _ d (h b)

/-! #### Below the largest target degree -/

/-- **Floor.**  Below `maxDeg` not every target is a consequence, in either system. -/
theorem not_all_of_lt {n d : ℕ} (hn : G.aux.n0 ≤ n) (hd : d < G.maxDeg) :
    ¬ G.AllPC n d ∧ ¬ G.AllNS n d := by
  obtain ⟨b, hb⟩ := G.exists_poly_maxDeg hn (by omega)
  constructor
  · intro h
    have := (mem_restrictTotalDegree _ _ _).mp (Vinf_le_Pd _ d (h b))
    omega
  · intro h
    have := (mem_restrictTotalDegree _ _ _).mp (NSspan_le_Pd _ d (h b))
    omega

/-! #### Degree zero -/

/-- The rank-independent condition for derivability of every target in degree zero: all targets
are constants, and each constant is zero or the template has a nonzero constant axiom. -/
def ZeroDerivable : Prop := G.maxDeg = 0 ∧ ∀ o : G.B.Obj, G.γ o 0 = 0 ∨ T.HasConstAxiom

theorem poly_eq_C {n : ℕ} (b : G.B.Rk n) (h0 : G.deg (G.B.up n b) = 0) :
    G.poly n b = C (G.γ (G.B.up n b) 0) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_poly, coeff_C]
  by_cases hm : 0 = m
  · subst hm
    rw [if_pos rfl]
    unfold BasisSystem.monUp
    rw [Finsupp.mapDomain_zero]
  · rw [if_neg hm]
    by_contra hne
    have h1 := G.mdeg_le_deg hne
    rw [h0, mdeg_monUp] at h1
    exact hm (Target.mdeg_eq_zero' (by omega)).symm

theorem γ_up_zero {n : ℕ} {b : G.B.Rk n} {o : G.B.Obj} {g : Equiv.Perm ℕ}
    (hb : G.B.up n b = g • o) : G.γ (G.B.up n b) 0 = G.γ o 0 := by
  have h := G.γ_inv g o 0
  have h0 : T.Var.monSMul g 0 = 0 := by unfold BasisSystem.monSMul; rw [Finsupp.mapDomain_zero]
  rw [h0] at h
  rw [hb, h]

theorem C_mem_V0_iff {n : ℕ} (hT : T.n0 ≤ n) (c : K) :
    C c ∈ V0 (T.inst n) 0 ↔ c = 0 ∨ T.HasConstAxiom := by
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have := (V0 (T.inst n) 0).smul_mem c⁻¹ h
      rw [smul_eq_C_mul, ← C_mul, inv_mul_cancel₀ hc, C_1] at this
      exact (T.one_mem_V0_zero_iff hT).mp this
  · rintro (rfl | hc)
    · rw [C_0]; exact Submodule.zero_mem _
    · have h1 := (T.one_mem_V0_zero_iff hT).mpr hc
      have := (V0 (T.inst n) 0).smul_mem c h1
      rwa [smul_eq_C_mul, mul_one] at this

/-- **Degree-zero stabilisation**, in the closure form. -/
theorem all_V0_zero_iff {n : ℕ} (hT : T.n0 ≤ n) (ha : G.aux.n0 ≤ n) :
    (∀ b : G.B.Rk n, G.poly n b ∈ V0 (T.inst n) 0) ↔ G.ZeroDerivable := by
  constructor
  · intro h
    have hmax : G.maxDeg = 0 := by
      by_contra hne
      exact (G.not_all_of_lt ha (Nat.pos_of_ne_zero hne)).1
        (fun b => by rw [Vinf_zero]; exact h b)
    refine ⟨hmax, fun o => ?_⟩
    obtain ⟨g, b, hb⟩ := exists_up G.B G.hB (le_trans G.t_le_aux_n0 ha) o
    have hdeg : G.deg (G.B.up n b) = 0 := by
      have := G.deg_le_maxDeg (G.B.up n b); omega
    have hmem := h b
    rw [G.poly_eq_C b hdeg, C_mem_V0_iff hT, G.γ_up_zero hb] at hmem
    exact hmem
  · rintro ⟨hmax, hall⟩ b
    have hdeg : G.deg (G.B.up n b) = 0 := by
      have := G.deg_le_maxDeg (G.B.up n b); omega
    rw [G.poly_eq_C b hdeg, C_mem_V0_iff hT]
    exact hall _

theorem allPC_zero_iff {n : ℕ} (hT : T.n0 ≤ n) (ha : G.aux.n0 ≤ n) :
    G.AllPC n 0 ↔ G.ZeroDerivable := by
  unfold AllPC
  simp only [Vinf_zero]
  exact G.all_V0_zero_iff hT ha

theorem allNS_zero_iff {n : ℕ} (hT : T.n0 ≤ n) (ha : G.aux.n0 ≤ n) :
    G.AllNS n 0 ↔ G.ZeroDerivable := by
  unfold AllNS
  simp only [Template.NSspan_zero]
  exact G.all_V0_zero_iff hT ha

/-! #### Field maps -/

/-- The same indexed target with coefficients mapped along a field homomorphism. -/
@[reducible] def map {S : Type} [Field S] (φ : K →+* S) : ITarget (T.map φ) where
  B := G.B
  t := G.t
  hB := G.hB
  DG := G.DG
  γ := fun b m => φ (G.γ b m)
  γ_inv := fun g b m => by rw [G.γ_inv]
  γ_deg := fun b m h => G.γ_deg b m fun h0 => h (by rw [h0, map_zero])

theorem map_poly {S : Type} [Field S] (φ : K →+* S) (n : ℕ) (b : G.B.Rk n) :
    (G.map φ).poly n b = MvPolynomial.map φ (G.poly n b) := by
  apply MvPolynomial.ext
  intro m
  exact (MvPolynomial.coeff_map φ (G.poly n b) m).symm

theorem map_deg_le {S : Type} [Field S] (φ : K →+* S) (b : G.B.Obj) :
    (G.map φ).deg b ≤ G.deg b := by
  classical
  apply Nat.find_min'
  intro m hm
  exact G.mdeg_le_deg fun h0 => hm (by show φ _ = 0; rw [h0, map_zero])

theorem map_aux_n0 {S : Type} [Field S] (φ : K →+* S) : (G.map φ).aux.n0 = G.aux.n0 := rfl

/-! #### One fixed global orbit -/

/-- The rank-`n` index `b` lies in the global orbit of `o`. -/
def InOrbit (o : G.B.Obj) {n : ℕ} (b : G.B.Rk n) : Prop :=
  ∃ g : Equiv.Perm ℕ, G.B.up n b = g • o

/-- The targets with indices in ONE fixed global orbit. -/
noncomputable def orbit (o : G.B.Obj) : ITarget T where
  B := G.B.sub (fun u => ∃ g : Equiv.Perm ℕ, u = g • o) (fun g u => by
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨g⁻¹ * h, by rw [mul_smul, ← hh, inv_smul_smul]⟩
    · rintro ⟨h, rfl⟩
      exact ⟨g * h, (mul_smul g h o).symm⟩)
  t := G.t
  hB := sub_bounded G.hB _ _
  DG := G.DG
  γ := fun u m => G.γ u.1 m
  γ_inv := fun g u m => G.γ_inv g u.1 m
  γ_deg := fun u m h => G.γ_deg u.1 m h

theorem orbit_poly (o : G.B.Obj) {n : ℕ} (b : (G.orbit o).B.Rk n) :
    (G.orbit o).poly n b = G.poly n b.1 := rfl

/-- The whole-orbit predicates of the orbit target are the predicates for the indices of `B_n`
lying in the orbit. -/
theorem orbit_allPC_iff (o : G.B.Obj) (n d : ℕ) :
    (G.orbit o).AllPC n d ↔ ∀ b : G.B.Rk n, G.InOrbit o b → G.poly n b ∈ Vinf (T.inst n) d := by
  constructor
  · rintro h b ⟨g, hg⟩
    exact h ⟨b, ⟨g, hg⟩⟩
  · rintro h ⟨b, hb⟩
    exact h b hb

theorem orbit_allNS_iff (o : G.B.Obj) (n d : ℕ) :
    (G.orbit o).AllNS n d ↔
      ∀ b : G.B.Rk n, G.InOrbit o b → G.poly n b ∈ NSspan (T.inst n) d := by
  constructor
  · rintro h b ⟨g, hg⟩
    exact h ⟨b, ⟨g, hg⟩⟩
  · rintro h ⟨b, hb⟩
    exact h b hb

/-- **All targets = every orbit.**  The aggregate predicate is the conjunction of the whole-orbit
predicates over the (finitely many) global orbits; it is NOT a rank-dependent choice among them. -/
theorem allPC_iff_forall_orbit (n d : ℕ) :
    G.AllPC n d ↔ ∀ o : G.B.Obj, (G.orbit o).AllPC n d := by
  constructor
  · intro h o
    rw [orbit_allPC_iff]
    exact fun b _ => h b
  · intro h b
    exact (G.orbit_allPC_iff (G.B.up n b) n d).mp (h _) b ⟨1, (one_smul _ _).symm⟩

theorem allNS_iff_forall_orbit (n d : ℕ) :
    G.AllNS n d ↔ ∀ o : G.B.Obj, (G.orbit o).AllNS n d := by
  constructor
  · intro h o
    rw [orbit_allNS_iff]
    exact fun b _ => h b
  · intro h b
    exact (G.orbit_allNS_iff (G.B.up n b) n d).mp (h _) b ⟨1, (one_smul _ _).symm⟩

/-- At every rank `n ≥ t` the orbit of `o` has a rank-`n` representative. -/
theorem exists_rep (o : G.B.Obj) {n : ℕ} (hn : G.t ≤ n) : ∃ b : G.B.Rk n, G.InOrbit o b := by
  obtain ⟨g, b, hb⟩ := exists_up G.B G.hB hn o
  exact ⟨b, g, hb⟩

theorem rename_poly (n : ℕ) (σ : Sfin n) (b : G.B.Rk n) :
    rename (fun v => σ • v) (G.poly n b) = G.poly n (σ • b) :=
  ClaudeC017.rename_poly G.aux σ b

/-- **Representative versus whole orbit**, for any `S_n`-invariant subspace. -/
theorem rep_iff_orbit (o : G.B.Obj) {n : ℕ} (H : Submodule K (MvPolynomial (T.Var.Rk n) K))
    (hH : ∀ (σ : Sfin n) f, f ∈ H → rename (fun v => σ • v) f ∈ H)
    {b0 : G.B.Rk n} (hb0 : G.InOrbit o b0) :
    G.poly n b0 ∈ H ↔ ∀ b : G.B.Rk n, G.InOrbit o b → G.poly n b ∈ H := by
  refine ⟨fun h b hb => ?_, fun h => h b0 hb0⟩
  obtain ⟨g0, hg0⟩ := hb0
  obtain ⟨g, hg⟩ := hb
  obtain ⟨σ, rfl⟩ := orbit_transitive G.B hg0 hg
  rw [← G.rename_poly]
  exact hH σ _ h

/-- **Representative = whole orbit, ordinary PC.** -/
theorem rep_iff_orbit_pc (o : G.B.Obj) {n d : ℕ} {b0 : G.B.Rk n} (hb0 : G.InOrbit o b0) :
    G.poly n b0 ∈ Vinf (T.inst n) d ↔ (G.orbit o).AllPC n d := by
  rw [orbit_allPC_iff]
  exact G.rep_iff_orbit o _ (fun σ f hf => rename_mem_Vinf T σ hf) hb0

/-- **Representative = whole orbit, NS.** -/
theorem rep_iff_orbit_ns (o : G.B.Obj) {n d : ℕ} {b0 : G.B.Rk n} (hb0 : G.InOrbit o b0) :
    G.poly n b0 ∈ NSspan (T.inst n) d ↔ (G.orbit o).AllNS n d := by
  rw [orbit_allNS_iff]
  exact G.rep_iff_orbit o _ (fun σ f hf => ClaudeC017.rename_mem_NSspan T σ hf) hb0

end ITarget

end UniformConsequence.Indexed
