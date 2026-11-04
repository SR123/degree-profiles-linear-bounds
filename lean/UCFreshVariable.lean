/-
Uniform consequences, Claude return 002 (5 October 2026).  Part 4 (Milestone 3): a fresh nullary
variable turns finite hard refutations into finite hard NONCONSTANT targets.

Polynomial level (any field `K`, any variable type `σ`, any axiom set `Γ ⊆ K[σ]`).  Put
`y = X none` in `K[Option σ]` and embed `Γ` by `rename some` (`lift Γ`); NO axiom involving `y`
is added.  Then, in the extended order (`⊤ + 1 = ⊤`):

* `tpcDegree_y`:  `d_PC(lift Γ ⊢ y) = max 1 (d_PC(Γ ⊢ 1))`;
* `tnsDegree_y`:  `d_NS(lift Γ ⊢ y) = d_NS(Γ ⊢ 1) + 1`.

PC lower bound: substitute `y = 1` in every line (`ysubst`, `derives_ysubst`); multiplication by
`y` becomes a repeated line, admitted as a linear combination; degrees do not increase.  PC upper
bound: the embedded refutation followed by one multiplication by `y`.  NS upper bound: multiply
the certificate by `y`.  NS lower bound: extract the coefficient of `y¹` through
`optionEquivLeft` (`extract_mem`); every surviving product loses exactly one degree.

Template level: `optionSys` adds one singleton object of empty support to a basis system;
`freshVar T` is `T` with this variable and the SAME axioms (coefficients vanish on monomials
involving `y`), parameters `k, s, D, n₀` unchanged; `freshVar_inst`: its instance is literally
`lift (T.inst n)`.  `freshTarget T` is the fully invariant uniform target `y` (Return 001's
`Target`), `freshTarget_poly`: it is `X none` at every rank.  `fresh_profiles`: its PC and NS
target profiles are `max 1 (T.pcProfile n)` and `T.nsProfile n + 1` at EVERY rank.

Types (`fresh_types`): over a field of prime characteristic, the fresh target profile has the
same T1–T4 type as the refutation profile, for PC and for NS (each with its own linear onset):
the recurring sets agree from `2` on for PC and are shifted by one for NS.

Instance: the preserved fluctuating witness `B̂` (`ClaudeUndec.bhat`), over any field of
characteristic `p` (`PaperAudit.bhat_window`: `n = p^a u`, `p ∤ u`, `n ≥ 2p^a`):
`p^a ≤ h_PC(n) ≤ p^a + 4` and `p^a + 1 ≤ h_NS(n) ≤ p^a + 5` for the nonconstant target `y`;
`bhat_fresh_T4`: both target profiles are of type T4 (from the preserved `bhat_pc_type`).
-/
import UCIndexedTarget
import PaperAudit

set_option autoImplicit false

open MvPolynomial

namespace UniformConsequence.Fresh

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.PC
open DegreeProfilesReview.NS UniformConsequence

/-! ### Polynomial level -/

section Poly

variable {K : Type} [Field K] {σ : Type}

/-- The old axioms in `K[Option σ]` (`y = X none` is new; no axiom involves it). -/
def lift (Γ : Set (MvPolynomial σ K)) : Set (MvPolynomial (Option σ) K) :=
  (rename (some : σ → Option σ)) '' Γ

/-- The substitution `y ↦ 1`, `x_i ↦ x_i`. -/
noncomputable def ysubst : MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  aeval fun o => o.elim (1 : MvPolynomial σ K) X

theorem ysubst_X_none : ysubst (X (none : Option σ) : MvPolynomial (Option σ) K) = 1 := by
  simp [ysubst]

theorem ysubst_X_some (i : σ) : ysubst (X (some i) : MvPolynomial (Option σ) K) = X i := by
  simp [ysubst]

theorem ysubst_rename (f : MvPolynomial σ K) : ysubst (rename some f) = f := by
  unfold ysubst
  rw [aeval_rename]
  have : ((fun o : Option σ => o.elim (1 : MvPolynomial σ K) X) ∘ some) = X := rfl
  rw [this, aeval_X_left_apply]

theorem ysubst_degree (f : MvPolynomial (Option σ) K) :
    (ysubst f).totalDegree ≤ f.totalDegree := by
  apply SelfContainedCycle072.degree_substitution
  intro o
  cases o with
  | none => rw [ysubst_X_none, totalDegree_one]; omega
  | some i => rw [ysubst_X_some, totalDegree_X]

/-- **Substituting `y = 1` in an ordinary PC derivation.**  Multiplication by `y` becomes a
repeated line (a linear combination); every other rule is preserved. -/
theorem derives_ysubst {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial (Option σ) K}
    (h : Derives (lift Γ) d f) : Derives Γ d (ysubst f) := by
  obtain ⟨l, hl, hdeg, hfl⟩ := h
  refine ⟨l.map ysubst, ?_, ?_, List.mem_map_of_mem hfl⟩
  · clear hdeg hfl
    induction hl with
    | nil => exact IsProof.nil
    | ax _ hf ih =>
      obtain ⟨g, hg, rfl⟩ := hf
      rw [List.map_cons, ysubst_rename]
      exact IsProof.ax ih hg
    | @lin l f _ hf ih =>
      refine IsProof.lin ih ?_
      have h1 : ysubst f ∈ (Submodule.span K {g | g ∈ l}).map ysubst.toLinearMap :=
        Submodule.mem_map_of_mem hf
      rw [Submodule.map_span] at h1
      refine Submodule.span_mono ?_ h1
      rintro _ ⟨g, hg, rfl⟩
      exact List.mem_map_of_mem hg
    | @mulX l g i _ hg ih =>
      rw [List.map_cons, map_mul]
      cases i with
      | none =>
        rw [ysubst_X_none, one_mul]
        exact IsProof.lin ih (Submodule.subset_span (List.mem_map_of_mem hg))
      | some j =>
        rw [ysubst_X_some]
        exact IsProof.mulX j ih (List.mem_map_of_mem hg)
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact le_trans (ysubst_degree g0) (hdeg g0 hg0)

/-- **Embedded refutation followed by one multiplication by `y`.** -/
theorem derives_y_of_refutes {Γ : Set (MvPolynomial σ K)} {d : ℕ} (h : Refutes Γ d)
    (hd : 1 ≤ d) : Derives (lift Γ) d (X none) := by
  have h1 : Derives (lift Γ) d (rename some (1 : MvPolynomial σ K)) :=
    Indexed.derives_rename some (fun f hf => Set.mem_image_of_mem _ hf) h
  rw [map_one] at h1
  obtain ⟨l, hl, hdeg, h1l⟩ := h1
  refine ⟨X none * 1 :: l, IsProof.mulX none hl h1l, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [mul_one, totalDegree_X]; exact hd
    · exact hdeg g hg
  · rw [mul_one]; exact List.mem_cons_self

theorem one_le_of_derives_y {Γ : Set (MvPolynomial σ K)} {d : ℕ}
    (h : Derives (lift Γ) d (X none)) : 1 ≤ d := by
  have hmem := derives_iff_mem_Vinf.mp h
  have := (mem_restrictTotalDegree _ _ _).mp (Vinf_le_Pd _ d hmem)
  rwa [totalDegree_X] at this

/-- **Exact PC identity**: `d_PC(lift Γ ⊢ y) = max 1 (d_PC(Γ ⊢ 1))`, `⊤` included. -/
theorem tpcDegree_y (Γ : Set (MvPolynomial σ K)) :
    tpcDegree (lift Γ) (X none) = max 1 (pcDegree Γ) := by
  apply enat_eq_of_forall_le_iff
  intro d
  rw [tpcDegree_le_iff, max_le_iff, pcDegree_le_iff]
  constructor
  · intro h
    refine ⟨by exact_mod_cast one_le_of_derives_y h, ?_⟩
    have := derives_ysubst h
    rwa [ysubst_X_none] at this
  · rintro ⟨h1, h2⟩
    exact derives_y_of_refutes h2 (by exact_mod_cast h1)

/-! #### Nullstellensatz -/

theorem ns_mdeg_add {τ : Type} (a b : τ →₀ ℕ) : NS.mdeg (a + b) = NS.mdeg a + NS.mdeg b := by
  unfold NS.mdeg
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem ns_mdeg_single {τ : Type} (i : τ) : NS.mdeg (Finsupp.single i 1) = 1 := by
  unfold NS.mdeg
  exact Finsupp.sum_single_index rfl

theorem ns_mdeg_mapDomain_some (m : σ →₀ ℕ) :
    NS.mdeg (Finsupp.mapDomain (some : σ → Option σ) m) = NS.mdeg m := by
  unfold NS.mdeg
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem ns_mdeg_option (m : Option σ →₀ ℕ) : NS.mdeg m = m none + NS.mdeg m.some := by
  unfold NS.mdeg
  exact Finsupp.sum_option_index m (fun _ e => e) (fun _ => rfl) (fun _ _ _ => rfl)

/-- **Multiplying a certificate by `y`.** -/
theorem y_mem_of_one_mem {Γ : Set (MvPolynomial σ K)} {e : ℕ}
    (h : (1 : MvPolynomial σ K) ∈ NSspan Γ e) : (X none : MvPolynomial (Option σ) K) ∈
      NSspan (lift Γ) (e + 1) := by
  let ψ : MvPolynomial σ K →ₗ[K] MvPolynomial (Option σ) K :=
    (LinearMap.mulLeft K (X none : MvPolynomial (Option σ) K)).comp (rename some).toLinearMap
  have hψ : (NSspan Γ e).map ψ ≤ NSspan (lift Γ) (e + 1) := by
    unfold NSspan
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨m, f, hf, hdeg, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨Finsupp.single none 1 + Finsupp.mapDomain some m, rename some f, ⟨f, hf, rfl⟩, ?_, ?_⟩
    · rw [ns_mdeg_add, ns_mdeg_single, ns_mdeg_mapDomain_some]
      have := totalDegree_rename_le (some : σ → Option σ) f
      omega
    · show X none * rename some (monomial m 1 * f) = _
      rw [map_mul, rename_monomial, ← mul_assoc, X, monomial_mul, one_mul]
  have := hψ (Submodule.mem_map_of_mem h)
  simpa [ψ] using this

theorem optionEquivLeft_rename_some (f : MvPolynomial σ K) :
    optionEquivLeft K σ (rename some f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [rename_C, optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, optionEquivLeft_X_some, Polynomial.C_mul]

/-- **Extracting the coefficient of `y¹`** maps the degree-`e` certificate image of `lift Γ` into
the degree-`(e - 1)` certificate image of `Γ`. -/
theorem extract_mem {Γ : Set (MvPolynomial σ K)} {e : ℕ} {g : MvPolynomial (Option σ) K}
    (hg : g ∈ NSspan (lift Γ) e) : (optionEquivLeft K σ g).coeff 1 ∈ NSspan Γ (e - 1) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f, ⟨f0, hf0, rfl⟩, hdeg, rfl⟩ := hx
    rw [map_mul, optionEquivLeft_monomial, optionEquivLeft_rename_some,
      Polynomial.monomial_mul_C, Polynomial.coeff_monomial]
    split_ifs with h1
    · apply Submodule.subset_span
      refine ⟨m.some, f0, hf0, ?_, rfl⟩
      rw [ns_mdeg_option, h1] at hdeg
      have e1 := totalDegree_rename_le (some : σ → Option σ) f0
      have e2 := ysubst_degree (K := K) (rename some f0)
      rw [ysubst_rename] at e2
      omega
    · exact Submodule.zero_mem _
  | zero => rw [map_zero, Polynomial.coeff_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, Polynomial.coeff_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, Polynomial.coeff_smul]
    exact Submodule.smul_mem _ c hx

theorem one_le_of_y_mem {Γ : Set (MvPolynomial σ K)} {e : ℕ}
    (h : (X none : MvPolynomial (Option σ) K) ∈ NSspan (lift Γ) e) : 1 ≤ e := by
  have := (mem_restrictTotalDegree _ _ _).mp (NSspan_le_Pd _ e h)
  rwa [totalDegree_X] at this

/-- **Exact NS identity**: `d_NS(lift Γ ⊢ y) = d_NS(Γ ⊢ 1) + 1`, `⊤ + 1 = ⊤` included. -/
theorem tnsDegree_y (Γ : Set (MvPolynomial σ K)) :
    tnsDegree (lift Γ) (X none) = nsDegree Γ + 1 := by
  apply enat_eq_of_forall_le_iff
  intro d
  rw [tnsDegree_le_iff_mem]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · constructor
    · intro h; exact absurd (one_le_of_y_mem h) (by omega)
    · intro h
      exfalso
      have : (1 : ℕ∞) ≤ 0 := le_trans (le_add_self) h
      exact absurd this (by norm_num)
  · obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [show ((e + 1 : ℕ) : ℕ∞) = (e : ℕ∞) + 1 by push_cast; rfl,
      ENat.add_le_add_iff_right ENat.one_ne_top, nsDegree_le_iff, nsRefutes_iff_one_mem_NSspan]
    constructor
    · intro h
      have := extract_mem h
      rwa [optionEquivLeft_X_none, Polynomial.coeff_X_one, Nat.add_sub_cancel] at this
    · exact y_mem_of_one_mem

end Poly

/-! ### Template level: one fresh nullary variable -/

section Template

/-- The basis system with one extra object `none` of empty support. -/
def optionSys (𝒰 : BasisSystem) : BasisSystem where
  Obj := Option 𝒰.Obj
  act :=
    { smul := fun g o => o.map (fun u => g • u)
      one_smul := fun o => by
        cases o with
        | none => rfl
        | some u => exact congrArg some (one_smul _ u)
      mul_smul := fun g h o => by
        cases o with
        | none => rfl
        | some u => exact congrArg some (mul_smul g h u) }
  supp := fun o => o.elim ∅ 𝒰.supp
  supp_smul := fun g o => by
    cases o with
    | none => exact (Finset.image_empty g).symm
    | some u => exact 𝒰.supp_smul g u
  fixed := fun g o h => by
    cases o with
    | none => rfl
    | some u => exact congrArg some (𝒰.fixed g u h)
  Rk := fun t => Option (𝒰.Rk t)
  fin := fun _ => inferInstance
  up := fun t => Option.map (𝒰.up t)
  up_inj := fun t => Option.map_injective (𝒰.up_inj t)
  range_up := fun t o => by
    cases o with
    | none => exact ⟨fun _ => Finset.empty_subset _, fun _ => ⟨none, rfl⟩⟩
    | some u =>
      show (∃ x, Option.map (𝒰.up t) x = some u) ↔ 𝒰.supp u ⊆ Finset.range t
      rw [← 𝒰.range_up]
      constructor
      · rintro ⟨x, hx⟩
        cases x with
        | none => exact absurd hx (by simp)
        | some y => exact ⟨y, Option.some_injective _ hx⟩
      · rintro ⟨y, hy⟩
        exact ⟨some y, by rw [Option.map_some, hy]⟩

theorem optionSys_bounded {𝒰 : BasisSystem} {r : ℕ} (h : 𝒰.Bounded r) :
    (optionSys 𝒰).Bounded r := fun o => by
  cases o with
  | none => exact Nat.zero_le _
  | some u => exact h u

/-- The exponent of the fresh variable in a monomial. -/
def yExp {α : Type} (m : Option α →₀ ℕ) : ℕ := m none

variable {K : Type} [Field K]

/-- The values of a relabelled monomial at `none` and on the old objects. -/
theorem monSMul_none (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) (m : (optionSys 𝒰).Obj →₀ ℕ) :
    yExp ((optionSys 𝒰).monSMul g m) = yExp m := by
  have hinj : Function.Injective (fun u : (optionSys 𝒰).Obj => g • u) := MulAction.injective g
  exact Finsupp.mapDomain_apply hinj m none

theorem monSMul_some (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) (m : (optionSys 𝒰).Obj →₀ ℕ) :
    ((optionSys 𝒰).monSMul g m).some = 𝒰.monSMul g m.some := by
  have hinj : Function.Injective (fun u : (optionSys 𝒰).Obj => g • u) := MulAction.injective g
  have hinj' : Function.Injective (fun u : 𝒰.Obj => g • u) := MulAction.injective g
  have hF : ∀ v : 𝒰.Obj, (fun u : (optionSys 𝒰).Obj => g • u) (some v) = some (g • v) :=
    fun _ => rfl
  ext u
  obtain ⟨v, rfl⟩ : ∃ v, g • v = u := ⟨g⁻¹ • u, smul_inv_smul g u⟩
  rw [Finsupp.some_apply]
  show (Finsupp.mapDomain (fun u : (optionSys 𝒰).Obj => g • u) m) (some (g • v)) =
    (Finsupp.mapDomain (fun u : 𝒰.Obj => g • u) m.some) (g • v)
  rw [← hF v, Finsupp.mapDomain_apply hinj, Finsupp.mapDomain_apply hinj', Finsupp.some_apply]
  rfl

theorem mdeg_option {α : Type} (m : Option α →₀ ℕ) :
    BasisSystem.mdeg m = yExp m + BasisSystem.mdeg m.some := by
  unfold BasisSystem.mdeg
  exact Finsupp.sum_option_index m (fun _ e => e) (fun _ => rfl) (fun _ _ _ => rfl)

open Classical in
/-- **The template with one fresh nullary variable `y`** and the SAME axioms: an axiom's
coefficient on a monomial involving `y` is zero, on a `y`-free monomial it is the old one.  The
parameters `k, s, D, n₀` are unchanged. -/
noncomputable def freshVar (T : Template K) : Template K where
  Var := optionSys T.Var
  Ax := T.Ax
  k := T.k
  s := T.s
  D := T.D
  n0 := T.n0
  hk := T.hk
  hn0 := T.hn0
  hn0' := T.hn0'
  var_bounded := optionSys_bounded T.var_bounded
  ax_bounded := T.ax_bounded
  coeff := fun i m => if yExp m = 0 then T.coeff i m.some else 0
  coeff_inv := fun g i m => by
    show (if yExp ((optionSys T.Var).monSMul g m) = 0 then
      T.coeff (g • i) ((optionSys T.Var).monSMul g m).some else 0) = _
    rw [monSMul_none, monSMul_some, T.coeff_inv]
  coeff_deg := fun i m h => by
    by_cases h0 : yExp m = 0
    · rw [if_pos h0] at h
      rw [mdeg_option, h0, zero_add]
      exact T.coeff_deg i _ h
    · rw [if_neg h0] at h; exact absurd rfl h

theorem monUp_none (T : Template K) (n : ℕ) (m : Option (T.Var.Rk n) →₀ ℕ) :
    yExp ((freshVar T).Var.monUp n m) = yExp m := by
  have hinj : Function.Injective ((freshVar T).Var.up n) := (freshVar T).Var.up_inj n
  exact Finsupp.mapDomain_apply hinj m none

theorem monUp_some (T : Template K) (n : ℕ) (m : Option (T.Var.Rk n) →₀ ℕ) :
    ((freshVar T).Var.monUp n m).some = T.Var.monUp n m.some := by
  have hinj : Function.Injective ((freshVar T).Var.up n) := (freshVar T).Var.up_inj n
  have hinj' : Function.Injective (T.Var.up n) := T.Var.up_inj n
  ext u
  rw [Finsupp.some_apply]
  by_cases hu : ∃ v, T.Var.up n v = u
  · obtain ⟨v, rfl⟩ := hu
    show (Finsupp.mapDomain ((freshVar T).Var.up n) m) ((freshVar T).Var.up n (some v)) =
      (Finsupp.mapDomain (T.Var.up n) m.some) (T.Var.up n v)
    rw [Finsupp.mapDomain_apply hinj, Finsupp.mapDomain_apply hinj', Finsupp.some_apply]
    rfl
  · push_neg at hu
    unfold BasisSystem.monUp
    rw [Finsupp.mapDomain_notin_range, Finsupp.mapDomain_notin_range]
    · rintro ⟨v, rfl⟩; exact hu v rfl
    · rintro ⟨o, ho⟩
      cases o with
      | none => exact absurd ho (by simp [freshVar, optionSys])
      | some v => exact hu v (Option.some_injective _ ho)

/-- **The instance of the fresh-variable template is literally the old instance, embedded.** -/
theorem freshVar_poly (T : Template K) (n : ℕ) (i : T.Ax.Rk n) :
    (freshVar T).poly n i = rename some (T.poly n i) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [Template.coeff_poly]
  show (if yExp ((freshVar T).Var.monUp n m) = 0 then
      T.coeff (T.Ax.up n i) ((freshVar T).Var.monUp n m).some else 0) = _
  rw [monUp_none, monUp_some]
  by_cases h0 : yExp m = 0
  · rw [if_pos h0]
    have hm : m = Finsupp.mapDomain some m.some := by
      ext o
      cases o with
      | none =>
        rw [show m none = yExp m from rfl, h0, Finsupp.mapDomain_notin_range]
        rintro ⟨v, hv⟩; exact absurd hv (by simp)
      | some v =>
        erw [Finsupp.mapDomain_apply (Option.some_injective _)]
        rfl
    rw [hm, coeff_rename_mapDomain _ (Option.some_injective _), Template.coeff_poly]
    congr 2
    rw [← hm]
  · rw [if_neg h0]
    symm
    apply coeff_rename_eq_zero
    intro u hu
    exfalso
    apply h0
    show m none = 0
    rw [← hu, Finsupp.mapDomain_notin_range]
    rintro ⟨v, hv⟩; exact absurd hv (by simp)

theorem freshVar_inst (T : Template K) (n : ℕ) : (freshVar T).inst n = lift (T.inst n) := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨T.poly n i, ⟨i, rfl⟩, (freshVar_poly T n i).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, freshVar_poly T n i⟩

open Classical in
/-- **The target `y`**: a fully invariant uniform target (Return 001's `Target`) of degree one. -/
noncomputable def freshTarget (T : Template K) : Target (freshVar T) where
  DG := 1
  γ := fun m => if m = Finsupp.single none 1 then 1 else 0
  γ_inv := fun g m => by
    have hs : (freshVar T).Var.monSMul g (Finsupp.single none 1) = Finsupp.single none 1 := by
      unfold BasisSystem.monSMul
      rw [Finsupp.mapDomain_single]
      rfl
    show (if (freshVar T).Var.monSMul g m = Finsupp.single none 1 then (1 : K) else 0) = _
    have key : (freshVar T).Var.monSMul g m = Finsupp.single none 1 ↔
        m = Finsupp.single none 1 := by
      conv_lhs => rw [← hs]
      exact ((freshVar T).Var.monSMul_injective g).eq_iff
    exact if_congr key rfl rfl
  γ_deg := fun m h => by
    by_cases hm : m = Finsupp.single none 1
    · subst hm; rw [mdeg_single]
    · rw [if_neg hm] at h; exact absurd rfl h

/-- At every rank the target is the actual polynomial `y = X none`. -/
theorem freshTarget_poly (T : Template K) (n : ℕ) :
    (freshTarget T).poly n = X none := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [Target.coeff_poly, coeff_X']
  show (if (freshVar T).Var.monUp n m = Finsupp.single none 1 then (1 : K) else 0) = _
  refine if_congr ?_ rfl rfl
  have hs : (freshVar T).Var.monUp n (Finsupp.single none 1) = Finsupp.single none 1 := by
    unfold BasisSystem.monUp
    rw [Finsupp.mapDomain_single]
    rfl
  rw [← hs, ((freshVar T).Var.monUp_injective n).eq_iff, eq_comm]

/-- **Exact profile identities for the fresh target**, at every rank:
`h_PC(n) = max 1 (d_PC(T_n))`, `h_NS(n) = d_NS(T_n) + 1`. -/
theorem fresh_profiles (T : Template K) (n : ℕ) :
    (freshTarget T).pcProfile n = max 1 (T.pcProfile n) ∧
    (freshTarget T).nsProfile n = T.nsProfile n + 1 := by
  unfold Target.pcProfile Target.nsProfile Template.pcProfile Template.nsProfile
  rw [freshTarget_poly, freshVar_inst]
  exact ⟨tpcDegree_y _, tnsDegree_y _⟩

end Template

/-! ### A preserved finite hard witness: `B̂` -/

section Instance

open ClaudeUndec

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p]

/-- **Finite hard NONCONSTANT targets from `B̂`.**  Over any field of characteristic `p`, for
`n = p^a u` with `p ∤ u` and `n ≥ 2p^a`, the degree-one target `y` (no axiom involves `y`) has
`p^a ≤ h_PC(n) ≤ h_NS(n)`, `h_PC(n) ≤ p^a + 4`, `p^a + 1 ≤ h_NS(n) ≤ p^a + 5`: finite, and
unbounded along `n = (p+1)p^a`. -/
theorem bhat_fresh_window {n a u : ℕ} (hu : ¬ p ∣ u) (hnu : n = p ^ a * u)
    (h2 : 2 * p ^ a ≤ n) :
    ((p ^ a : ℕ) : ℕ∞) ≤ (freshTarget (template bhat K)).pcProfile n ∧
      (freshTarget (template bhat K)).pcProfile n ≤ ((p ^ a + 4 : ℕ) : ℕ∞) ∧
      (freshTarget (template bhat K)).pcProfile n ≤ (freshTarget (template bhat K)).nsProfile n ∧
      ((p ^ a + 1 : ℕ) : ℕ∞) ≤ (freshTarget (template bhat K)).nsProfile n ∧
      (freshTarget (template bhat K)).nsProfile n ≤ ((p ^ a + 5 : ℕ) : ℕ∞) := by
  obtain ⟨hlo, hpcns, hhi⟩ := PaperAudit.bhat_window p K hu hnu h2
  obtain ⟨epc, ens⟩ := fresh_profiles (template bhat K) n
  have hq : 1 ≤ p ^ a := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have h1 : (1 : ℕ∞) ≤ (template bhat K).pcProfile n :=
    le_trans (by exact_mod_cast hq) hlo
  rw [epc, ens, max_eq_right h1]
  refine ⟨hlo, le_trans hpcns hhi, le_trans hpcns le_self_add, ?_, ?_⟩
  · have := add_le_add (le_trans hlo hpcns) (le_refl (1 : ℕ∞))
    push_cast
    exact this
  · have := add_le_add hhi (le_refl (1 : ℕ∞))
    calc (template bhat K).nsProfile n + 1 ≤ ((p ^ a + 4 : ℕ) : ℕ∞) + 1 := this
      _ = ((p ^ a + 5 : ℕ) : ℕ∞) := by push_cast; ring

/-- The explicit peaks `n_a = (p+1)p^a`: `n_a/(p+1) ≤ h_PC(n_a) ≤ h_NS(n_a) ≤ n_a/(p+1) + 5`. -/
theorem bhat_fresh_peaks (a : ℕ) :
    (((p + 1) * p ^ a / (p + 1) : ℕ) : ℕ∞) ≤
        (freshTarget (template bhat K)).pcProfile ((p + 1) * p ^ a) ∧
      (freshTarget (template bhat K)).pcProfile ((p + 1) * p ^ a) ≤
        (freshTarget (template bhat K)).nsProfile ((p + 1) * p ^ a) ∧
      (freshTarget (template bhat K)).nsProfile ((p + 1) * p ^ a) ≤
        (((p + 1) * p ^ a / (p + 1) + 5 : ℕ) : ℕ∞) := by
  have hp2 := (Fact.out : p.Prime).two_le
  have hdiv : (p + 1) * p ^ a / (p + 1) = p ^ a := Nat.mul_div_cancel_left _ (by omega)
  have hu : ¬ p ∣ p + 1 := by
    intro h
    have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
  have hw := bhat_fresh_window p K (a := a) (u := p + 1) hu (by ring)
    (Nat.mul_le_mul_right (p ^ a) (by omega : 2 ≤ p + 1))
  rw [hdiv]
  exact ⟨hw.1, hw.2.2.1, hw.2.2.2.2⟩

/-- The target `y` is not constant and has degree one at every rank. -/
theorem fresh_target_degree (T : Template K) (n : ℕ) :
    ((freshTarget T).poly n).totalDegree = 1 := by
  rw [freshTarget_poly, totalDegree_X]

end Instance

/-! ### The fresh target has the type of the refutation profile -/

section Types

open DegreeProfilesReview.Profiles

/-- `d` is taken at arbitrarily large sizes. -/
def Recur (h : ℕ → ℕ∞) (d : ℕ) : Prop := ∀ M, ∃ n, M ≤ n ∧ h n = (d : ℕ∞)

theorem E_eq_recur {h : ℕ → ℕ∞} {N Q : ℕ → ℕ} (P : PeriodicProfile h N Q) :
    E h N = {d | Recur h d} := by
  ext d
  exact P.mem_E_iff d

variable {g : ℕ → ℕ∞}

theorem enat_succ_eq_coe_succ {x : ℕ∞} {d : ℕ} : x + 1 = ((d + 1 : ℕ) : ℕ∞) ↔ x = (d : ℕ∞) := by
  rw [show ((d + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + 1 by push_cast; rfl]
  exact WithTop.add_right_inj ENat.one_ne_top

theorem recur_succ_iff (d : ℕ) : Recur (fun n => g n + 1) (d + 1) ↔ Recur g d := by
  unfold Recur
  simp only [enat_succ_eq_coe_succ]

theorem not_recur_succ_zero : ¬ Recur (fun n => g n + 1) 0 := by
  intro h
  obtain ⟨n, -, hn⟩ := h 0
  have hn' : g n + 1 = 0 := hn
  have : (1 : ℕ∞) ≤ 0 := by rw [← hn']; exact le_add_self
  exact absurd this (by norm_num)

theorem max_one_eq_coe_iff {x : ℕ∞} {d : ℕ} (hd : 2 ≤ d) : max 1 x = (d : ℕ∞) ↔ x = (d : ℕ∞) := by
  constructor
  · intro h
    rcases le_total 1 x with h1 | h1
    · rwa [max_eq_right h1] at h
    · rw [max_eq_left h1] at h
      have : ((1 : ℕ) : ℕ∞) = (d : ℕ∞) := by exact_mod_cast h
      have := Nat.cast_injective this
      omega
  · intro h
    rw [h, max_eq_right]
    exact_mod_cast (show 1 ≤ d by omega)

theorem recur_max_iff {d : ℕ} (hd : 2 ≤ d) : Recur (fun n => max 1 (g n)) d ↔ Recur g d := by
  unfold Recur
  simp only [max_one_eq_coe_iff hd]

theorem not_recur_max_zero : ¬ Recur (fun n => max 1 (g n)) 0 := by
  intro h
  obtain ⟨n, -, hn⟩ := h 0
  have hn' : max 1 (g n) = 0 := by simpa using hn
  have : (1 : ℕ∞) ≤ 0 := by rw [← hn']; exact le_max_left _ _
  exact absurd this (by norm_num)

theorem recur_max_one_iff : Recur (fun n => max 1 (g n)) 1 ↔ Recur g 0 ∨ Recur g 1 := by
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    obtain ⟨⟨M0, hM0⟩, ⟨M1, hM1⟩⟩ :
        (∃ M, ∀ n, M ≤ n → g n ≠ ((0 : ℕ) : ℕ∞)) ∧ (∃ M, ∀ n, M ≤ n → g n ≠ ((1 : ℕ) : ℕ∞)) := by
      obtain ⟨h0, h1⟩ := hno
      unfold Recur at h0 h1
      push_neg at h0 h1
      exact ⟨h0, h1⟩
    obtain ⟨n, hn, hval⟩ := h (max M0 M1)
    have hval' : max 1 (g n) = 1 := by simpa using hval
    have hle : g n ≤ 1 := by
      have : g n ≤ max 1 (g n) := le_max_right _ _
      rw [hval'] at this; exact this
    have h0 := hM0 n (le_trans (le_max_left _ _) hn)
    have h1 := hM1 n (le_trans (le_max_right _ _) hn)
    obtain ⟨x, hx, hx1⟩ := enat_exists_of_le_coe (show g n ≤ ((1 : ℕ) : ℕ∞) by exact_mod_cast hle)
    interval_cases x
    · exact h0 hx
    · exact h1 hx
  · intro h
    have key : ∀ e : ℕ, e ≤ 1 → Recur g e → Recur (fun n => max 1 (g n)) 1 := by
      intro e he hr M
      obtain ⟨n, hn, hval⟩ := hr M
      refine ⟨n, hn, ?_⟩
      show max 1 (g n) = ((1 : ℕ) : ℕ∞)
      rw [hval, max_eq_left (by exact_mod_cast he)]
      rfl
    rcases h with h | h
    · exact key 0 (by omega) h
    · exact key 1 le_rfl h

theorem bounded_succ_iff : EventuallyBounded (fun n => g n + 1) ↔ EventuallyBounded g := by
  constructor
  · rintro ⟨B, M, h⟩
    exact ⟨B, M, fun n hn => le_trans le_self_add (h n hn)⟩
  · rintro ⟨B, M, h⟩
    refine ⟨B + 1, M, fun n hn => ?_⟩
    push_cast
    exact add_le_add (h n hn) le_rfl

theorem bounded_max_iff : EventuallyBounded (fun n => max 1 (g n)) ↔ EventuallyBounded g := by
  constructor
  · rintro ⟨B, M, h⟩
    exact ⟨B, M, fun n hn => le_trans (le_max_right _ _) (h n hn)⟩
  · rintro ⟨B, M, h⟩
    refine ⟨max 1 B, M, fun n hn => ?_⟩
    push_cast
    exact max_le_max le_rfl (h n hn)

/-- Two sets of naturals that agree from `2` on are finite, empty and nonempty together, when
membership of `1` in the second matches membership of `0` or `1` in the first. -/
theorem sets_of_agree {A B : Set ℕ} (h0 : 0 ∉ B) (h1 : 1 ∈ B ↔ 0 ∈ A ∨ 1 ∈ A)
    (h2 : ∀ d, 2 ≤ d → (d ∈ B ↔ d ∈ A)) :
    (A.Finite ↔ B.Finite) ∧ (A = ∅ ↔ B = ∅) ∧ (A.Nonempty ↔ B.Nonempty) := by
  have hsub1 : A ⊆ B ∪ {0, 1} := by
    intro d hd
    rcases Nat.lt_or_ge d 2 with h | h
    · right; interval_cases d <;> simp
    · left; exact (h2 d h).mpr hd
  have hsub2 : B ⊆ A ∪ {0, 1} := by
    intro d hd
    rcases Nat.lt_or_ge d 2 with h | h
    · right; interval_cases d <;> simp
    · left; exact (h2 d h).mp hd
  have hne : A.Nonempty ↔ B.Nonempty := by
    constructor
    · rintro ⟨d, hd⟩
      rcases Nat.lt_or_ge d 2 with h | h
      · exact ⟨1, h1.mpr (by interval_cases d <;> simp_all)⟩
      · exact ⟨d, (h2 d h).mpr hd⟩
    · rintro ⟨d, hd⟩
      rcases Nat.lt_or_ge d 2 with h | h
      · interval_cases d
        · exact absurd hd h0
        · rcases h1.mp hd with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
      · exact ⟨d, (h2 d h).mp hd⟩
  refine ⟨⟨fun hA => (hA.union (Set.toFinite {0, 1})).subset hsub2,
    fun hB => (hB.union (Set.toFinite {0, 1})).subset hsub1⟩, ?_, hne⟩
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, hne]

theorem types_of_sets {g h : ℕ → ℕ∞} {Ng Nh : ℕ → ℕ}
    (hB : EventuallyBounded g ↔ EventuallyBounded h)
    (hfin : (E g Ng).Finite ↔ (E h Nh).Finite) (hemp : E g Ng = ∅ ↔ E h Nh = ∅)
    (hne : (E g Ng).Nonempty ↔ (E h Nh).Nonempty) :
    (IsT1 g ↔ IsT1 h) ∧ (IsT2 g Ng ↔ IsT2 h Nh) ∧ (IsT3 g Ng ↔ IsT3 h Nh) ∧
      (IsT4 g Ng ↔ IsT4 h Nh) := by
  unfold IsT1 IsT2 IsT3 IsT4
  refine ⟨hB, hemp, ?_, ?_⟩
  · rw [hfin, hne, hB]
  · rw [Set.Infinite, Set.Infinite, hfin]

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p]

include p in
/-- **The fresh target has the same type as the refutation profile**, for ordinary PC and for
NS (the written corollary of `FRESH_VARIABLE_FINITE_HARD_TARGETS_003.md`).  Each type is taken
with the profile's own linear onset. -/
theorem fresh_types (T : Template R) :
    ((IsT1 T.pcProfile ↔ IsT1 (freshTarget T).pcProfile) ∧
      (IsT2 T.pcProfile (onset T.k T.s T.n0) ↔
        IsT2 (freshTarget T).pcProfile (onset T.k T.s (freshTarget T).nstar)) ∧
      (IsT3 T.pcProfile (onset T.k T.s T.n0) ↔
        IsT3 (freshTarget T).pcProfile (onset T.k T.s (freshTarget T).nstar)) ∧
      (IsT4 T.pcProfile (onset T.k T.s T.n0) ↔
        IsT4 (freshTarget T).pcProfile (onset T.k T.s (freshTarget T).nstar))) ∧
    ((IsT1 T.nsProfile ↔ IsT1 (freshTarget T).nsProfile) ∧
      (IsT2 T.nsProfile (onset T.k T.s T.n0) ↔
        IsT2 (freshTarget T).nsProfile (onset T.k T.s (freshTarget T).nstar)) ∧
      (IsT3 T.nsProfile (onset T.k T.s T.n0) ↔
        IsT3 (freshTarget T).nsProfile (onset T.k T.s (freshTarget T).nstar)) ∧
      (IsT4 T.nsProfile (onset T.k T.s T.n0) ↔
        IsT4 (freshTarget T).nsProfile (onset T.k T.s (freshTarget T).nstar))) := by
  have PTpc := (LinearFinal.linear_classification p T T.pcProfile (by simp)).1
  have PTns := (LinearFinal.linear_classification p T T.nsProfile (by simp)).1
  have PGpc := (freshTarget T).periodic_pc p
  have PGns := (freshTarget T).periodic_ns p
  have epc : (freshTarget T).pcProfile = fun n => max 1 (T.pcProfile n) :=
    funext fun n => (fresh_profiles T n).1
  have ens : (freshTarget T).nsProfile = fun n => T.nsProfile n + 1 :=
    funext fun n => (fresh_profiles T n).2
  have eTpc : E T.pcProfile (onset T.k T.s T.n0) = {d | Recur T.pcProfile d} := E_eq_recur PTpc
  have eTns : E T.nsProfile (onset T.k T.s T.n0) = {d | Recur T.nsProfile d} := E_eq_recur PTns
  have eGpc : E (freshTarget T).pcProfile (onset T.k T.s (freshTarget T).nstar) =
      {d | Recur (freshTarget T).pcProfile d} := E_eq_recur PGpc
  have eGns : E (freshTarget T).nsProfile (onset T.k T.s (freshTarget T).nstar) =
      {d | Recur (freshTarget T).nsProfile d} := E_eq_recur PGns
  constructor
  · have hsets := sets_of_agree (A := {d | Recur T.pcProfile d})
      (B := {d | Recur (freshTarget T).pcProfile d})
      (by show ¬ Recur (freshTarget T).pcProfile 0; rw [epc]; exact not_recur_max_zero)
      (by show Recur (freshTarget T).pcProfile 1 ↔ _; rw [epc]; exact recur_max_one_iff)
      (fun d hd => by show Recur (freshTarget T).pcProfile d ↔ _; rw [epc]; exact recur_max_iff hd)
    refine types_of_sets (by rw [epc]; exact bounded_max_iff.symm) ?_ ?_ ?_
    · rw [eTpc, eGpc]; exact hsets.1
    · rw [eTpc, eGpc]; exact hsets.2.1
    · rw [eTpc, eGpc]; exact hsets.2.2
  · have himg : {d | Recur (freshTarget T).nsProfile d} = Nat.succ '' {d | Recur T.nsProfile d} := by
      ext d
      show Recur (freshTarget T).nsProfile d ↔ _
      rw [ens]
      constructor
      · intro hd
        cases d with
        | zero => exact absurd hd not_recur_succ_zero
        | succ e => exact ⟨e, (recur_succ_iff e).mp hd, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact (recur_succ_iff e).mpr he
    have hinj : Set.InjOn Nat.succ {d | Recur T.nsProfile d} := fun _ _ _ _ h => Nat.succ_injective h
    refine types_of_sets (by rw [ens]; exact bounded_succ_iff.symm) ?_ ?_ ?_
    · rw [eTns, eGns, himg]
      exact (Set.finite_image_iff hinj).symm
    · rw [eTns, eGns, himg, Set.image_eq_empty]
    · rw [eTns, eGns, himg, Set.image_nonempty]

/-- **The fresh `B̂` target is of type T4 in both systems**: its finite target degrees recur at
arbitrarily large values (the preserved `ClaudeUndec.bhat_pc_type` plus `fresh_types`), over any
field of characteristic `p`. -/
theorem bhat_fresh_T4 (K : Type) [Field K] [CharP K p] :
    IsT4 (freshTarget (ClaudeUndec.template ClaudeUndec.bhat K)).pcProfile
        (onset (ClaudeUndec.template ClaudeUndec.bhat K).k (ClaudeUndec.template ClaudeUndec.bhat K).s
          (freshTarget (ClaudeUndec.template ClaudeUndec.bhat K)).nstar) ∧
      IsT4 (freshTarget (ClaudeUndec.template ClaudeUndec.bhat K)).nsProfile
        (onset (ClaudeUndec.template ClaudeUndec.bhat K).k (ClaudeUndec.template ClaudeUndec.bhat K).s
          (freshTarget (ClaudeUndec.template ClaudeUndec.bhat K)).nstar) := by
  have PT := (LinearFinal.linear_classification p (ClaudeUndec.template ClaudeUndec.bhat K)
    (ClaudeUndec.template ClaudeUndec.bhat K).pcProfile (by simp)).1
  have h4 : IsT4 (ClaudeUndec.template ClaudeUndec.bhat K).pcProfile
      (onset (ClaudeUndec.template ClaudeUndec.bhat K).k (ClaudeUndec.template ClaudeUndec.bhat K).s
        (ClaudeUndec.template ClaudeUndec.bhat K).n0) := by
    show (E _ _).Infinite
    rw [E_eq_recur PT]
    exact ClaudeUndec.bhat_pc_type p K
  have hG := ((fresh_types p (ClaudeUndec.template ClaudeUndec.bhat K)).1.2.2.2).mp h4
  exact ⟨hG, (((freshTarget (ClaudeUndec.template ClaudeUndec.bhat K)).types_agree p).2.2.2).mp hG⟩

end Types

end UniformConsequence.Fresh
