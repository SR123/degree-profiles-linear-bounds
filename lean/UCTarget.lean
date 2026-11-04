/-
Uniform consequences, Claude return 001 (5 October 2026).  Part 1: fully invariant targets.

A *fully invariant uniform target* for a template `T` is ONE rank-independent coefficient rule
`γ` on global monomials in the variables of `T`, invariant under every finite relabelling, with
`γ m = 0` whenever `deg m > DG`.  At universe size `t` the target is
`G_t = ∑_{m supported in [t]} γ(m) m`.

Proved here, with no hypotheses:
* `poly`, `coeff_poly`: the actual target polynomial at size `t`;
* `auxT`: an auxiliary template with the single empty-support axiom index whose unique axiom is
  `G_t`.  It is used ONLY to reuse the degree-stabilisation theorem of `Templates.lean`; the target
  is never added to the axioms of `T`;
* `deg`, `totalDegree_poly`: beyond `nG = max 1 (k·DG)` the degree of `G_t` is the rank-independent
  number `deg`;
* `targetM`: the invariant matrix from the one-point system (empty support) into the monomials of
  degree `≤ d`, with entry `γ(y)` in row `y`;
* `Gtr`, `Gtr_coe`, `targetM_realise`: its realisation at rank `t` is `a ↦ a • G_t` read in the
  monomial basis (for `d ≥ deg`; in general it is the degree-`≤ d` truncation);
* `NSDerives`: total-product NS identities `G = ∑ a_f f` for an arbitrary target polynomial, and
  `nsDerives_iff_mem_NSspan`; `NSDerivesAdd` (additive degree form) is equivalent;
* field maps of targets and membership descent for arbitrary `K`-rational targets.
-/
import TemplateExactTransfer
import DegreeProfilesReview.FieldDescent

set_option autoImplicit false

open MvPolynomial

namespace UniformConsequence

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.Concrete

/-! ### Total-product NS identities for an arbitrary polynomial -/

section NSTargets

variable {σ : Type*} {K : Type*} [Field K]

/-- A total-product-degree `≤ d` Nullstellensatz identity `g = ∑_{f ∈ s} a_f f` with every
`f ∈ Γ`.  For `g = 1` this is `NS.NSRefutes`. -/
def NSDerives (Γ : Set (MvPolynomial σ K)) (d : ℕ) (g : MvPolynomial σ K) : Prop :=
  ∃ (s : Finset (MvPolynomial σ K)) (a : MvPolynomial σ K → MvPolynomial σ K),
    (∀ f ∈ s, f ∈ Γ) ∧ (∀ f ∈ s, (a f * f).totalDegree ≤ d) ∧ ∑ f ∈ s, a f * f = g

/-- The same identity with the degree bound in the additive form `deg a_f + deg f ≤ d` for every
nonzero multiplier (the form used in the target specification). -/
def NSDerivesAdd (Γ : Set (MvPolynomial σ K)) (d : ℕ) (g : MvPolynomial σ K) : Prop :=
  ∃ (s : Finset (MvPolynomial σ K)) (a : MvPolynomial σ K → MvPolynomial σ K),
    (∀ f ∈ s, f ∈ Γ) ∧ (∀ f ∈ s, a f = 0 ∨ (a f).totalDegree + f.totalDegree ≤ d) ∧
      ∑ f ∈ s, a f * f = g

theorem nsDerivesAdd_of_mem_NSspan {Γ : Set (MvPolynomial σ K)} {d : ℕ}
    {g : MvPolynomial σ K} (hg : g ∈ NSspan Γ d) : NSDerivesAdd Γ d g := by
  classical
  unfold NSspan at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f, hf, hdeg, rfl⟩ := hx
    refine ⟨{f}, fun _ => monomial m 1, ?_, ?_, by simp⟩
    · intro f' hf'; rw [Finset.mem_singleton] at hf'; subst hf'; exact hf
    · intro f' hf'
      rw [Finset.mem_singleton] at hf'; subst hf'
      right
      show (monomial m (1 : K)).totalDegree + f'.totalDegree ≤ d
      have : (monomial m (1 : K)).totalDegree ≤ NS.mdeg m := totalDegree_monomial_le m 1
      omega
  | zero => exact ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, a, hs, ha, rfl⟩ := hx
    obtain ⟨s', a', hs', ha', rfl⟩ := hy
    refine ⟨s ∪ s', fun f => (if f ∈ s then a f else 0) + (if f ∈ s' then a' f else 0),
      ?_, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_union.mp hf with h | h
      · exact hs f h
      · exact hs' f h
    · intro f _
      by_cases h1 : f ∈ s <;> by_cases h2 : f ∈ s'
      · simp only [h1, h2, if_true]
        rcases ha f h1 with e1 | e1 <;> rcases ha' f h2 with e2 | e2
        · left; rw [e1, e2, add_zero]
        · right; rw [e1, zero_add]; exact e2
        · right; rw [e2, add_zero]; exact e1
        · right
          have := totalDegree_add (a f) (a' f)
          rcases le_total (a f).totalDegree (a' f).totalDegree with h | h
          · rw [max_eq_right h] at this; omega
          · rw [max_eq_left h] at this; omega
      · simp only [h1, h2, if_true, if_false, add_zero]; exact ha f h1
      · simp only [h1, h2, if_true, if_false, zero_add]; exact ha' f h2
      · left; simp [h1, h2]
    · simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
        Finset.union_inter_cancel_right]
  | smul c x _ hx =>
    obtain ⟨s, a, hs, ha, rfl⟩ := hx
    refine ⟨s, fun f => c • a f, hs, ?_, ?_⟩
    · intro f hf
      rcases ha f hf with e | e
      · left
        show c • a f = 0
        rw [e, smul_zero]
      · right
        show (c • a f).totalDegree + f.totalDegree ≤ d
        have := totalDegree_smul_le c (a f)
        omega
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [smul_mul_assoc]

/-- **Target form of `lem:presentation`.**  An arbitrary polynomial `g` has a total-product
degree `≤ d` NS identity iff it lies in the image of the degree-`d` certificate map. -/
theorem nsDerives_iff_mem_NSspan {Γ : Set (MvPolynomial σ K)} {d : ℕ} {g : MvPolynomial σ K} :
    NSDerives Γ d g ↔ g ∈ NSspan Γ d := by
  constructor
  · rintro ⟨s, a, hs, hdeg, hsum⟩
    rw [← hsum]
    apply Submodule.sum_mem
    intro f hf
    by_cases ha : a f = 0
    · rw [ha, zero_mul]; exact Submodule.zero_mem _
    by_cases hf0 : f = 0
    · rw [hf0, mul_zero]; exact Submodule.zero_mem _
    apply mul_mem_NSspan (hs f hf)
    rw [← totalDegree_mul_of_isDomain ha hf0]
    exact hdeg f hf
  · intro h
    obtain ⟨s, a, hs, ha, hsum⟩ := nsDerivesAdd_of_mem_NSspan h
    refine ⟨s, a, hs, ?_, hsum⟩
    intro f hf
    rcases ha f hf with e | e
    · rw [e, zero_mul]; simp
    · exact le_trans (totalDegree_mul _ _) e

theorem nsDerivesAdd_iff_mem_NSspan {Γ : Set (MvPolynomial σ K)} {d : ℕ}
    {g : MvPolynomial σ K} : NSDerivesAdd Γ d g ↔ g ∈ NSspan Γ d := by
  constructor
  · rintro ⟨s, a, hs, hdeg, hsum⟩
    apply nsDerives_iff_mem_NSspan.mp
    refine ⟨s, a, hs, ?_, hsum⟩
    intro f hf
    rcases hdeg f hf with e | e
    · rw [e, zero_mul]; simp
    · exact le_trans (totalDegree_mul _ _) e
  · exact nsDerivesAdd_of_mem_NSspan

theorem NSDerives.mono {Γ : Set (MvPolynomial σ K)} {d d' : ℕ} (hdd : d ≤ d')
    {g : MvPolynomial σ K} (h : NSDerives Γ d g) : NSDerives Γ d' g := by
  obtain ⟨s, a, hs, hdeg, hsum⟩ := h
  exact ⟨s, a, hs, fun f hf => le_trans (hdeg f hf) hdd, hsum⟩

theorem nsDerives_one_iff {Γ : Set (MvPolynomial σ K)} {d : ℕ} :
    NSDerives Γ d 1 ↔ NSRefutes Γ d := Iff.rfl

/-- The NS certificate image consists of polynomials of degree `≤ d`. -/
theorem NSspan_le_Pd (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    NSspan Γ d ≤ restrictTotalDegree σ K d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m, f, _, hdeg, rfl⟩
  rw [SetLike.mem_coe, mem_restrictTotalDegree]
  have h1 := totalDegree_mul (monomial m (1 : K)) f
  have h2 : (monomial m (1 : K)).totalDegree ≤ NS.mdeg m := totalDegree_monomial_le m 1
  omega

/-- The PC closure at degree `d` consists of polynomials of degree `≤ d`. -/
theorem Vinf_le_Pd (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    Vinf Γ d ≤ restrictTotalDegree σ K d :=
  iSup_le fun j => V_le_W Γ d j

end NSTargets

/-! ### Minimum-degree profiles of an arbitrary target polynomial -/

section TargetDegrees

variable {σ : Type*} {K : Type*} [Field K]

open Classical in
/-- Least degree of an ordinary PC derivation of `g` from `Γ` (`⊤` if there is none). -/
noncomputable def tpcDegree (Γ : Set (MvPolynomial σ K)) (g : MvPolynomial σ K) : ℕ∞ :=
  if h : ∃ d, Derives Γ d g then ((Nat.find h : ℕ) : ℕ∞) else ⊤

open Classical in
/-- Least total-product degree of an NS identity for `g` from `Γ` (`⊤` if there is none). -/
noncomputable def tnsDegree (Γ : Set (MvPolynomial σ K)) (g : MvPolynomial σ K) : ℕ∞ :=
  if h : ∃ d, NSDerives Γ d g then ((Nat.find h : ℕ) : ℕ∞) else ⊤

theorem tpcDegree_le_iff (Γ : Set (MvPolynomial σ K)) (g : MvPolynomial σ K) (d : ℕ) :
    tpcDegree Γ g ≤ (d : ℕ∞) ↔ Derives Γ d g := by
  classical
  unfold tpcDegree
  split
  · rename_i h
    rw [Nat.cast_le]
    exact ⟨fun hle => (Nat.find_spec h).mono hle, fun hd => Nat.find_min' h hd⟩
  · rename_i h
    simp only [top_le_iff, ENat.coe_ne_top, false_iff]
    exact fun hd => h ⟨d, hd⟩

theorem tnsDegree_le_iff (Γ : Set (MvPolynomial σ K)) (g : MvPolynomial σ K) (d : ℕ) :
    tnsDegree Γ g ≤ (d : ℕ∞) ↔ NSDerives Γ d g := by
  classical
  unfold tnsDegree
  split
  · rename_i h
    rw [Nat.cast_le]
    exact ⟨fun hle => (Nat.find_spec h).mono hle, fun hd => Nat.find_min' h hd⟩
  · rename_i h
    simp only [top_le_iff, ENat.coe_ne_top, false_iff]
    exact fun hd => h ⟨d, hd⟩

theorem tpcDegree_le_iff_mem (Γ : Set (MvPolynomial σ K)) (g : MvPolynomial σ K) (d : ℕ) :
    tpcDegree Γ g ≤ (d : ℕ∞) ↔ g ∈ Vinf Γ d := by
  rw [tpcDegree_le_iff, derives_iff_mem_Vinf]

theorem tnsDegree_le_iff_mem (Γ : Set (MvPolynomial σ K)) (g : MvPolynomial σ K) (d : ℕ) :
    tnsDegree Γ g ≤ (d : ℕ∞) ↔ g ∈ NSspan Γ d := by
  rw [tnsDegree_le_iff, nsDerives_iff_mem_NSspan]

/-- For `g = 1` the target degrees are the refutation degrees. -/
theorem tpcDegree_one (Γ : Set (MvPolynomial σ K)) : tpcDegree Γ 1 = pcDegree Γ :=
  enat_eq_of_forall_le_iff fun d => by rw [tpcDegree_le_iff, pcDegree_le_iff]; rfl

theorem tnsDegree_one (Γ : Set (MvPolynomial σ K)) : tnsDegree Γ 1 = nsDegree Γ :=
  enat_eq_of_forall_le_iff fun d => by rw [tnsDegree_le_iff, nsDegree_le_iff]; rfl

/-- `d_PC ≤ d_NS` for every target, by an actual simulation of the certificate. -/
theorem tpcDegree_le_tnsDegree (Γ : Set (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    tpcDegree Γ g ≤ tnsDegree Γ g := by
  induction hns : tnsDegree Γ g using ENat.recTopCoe with
  | top => exact le_top
  | coe a =>
    rw [tpcDegree_le_iff_mem]
    apply NSspan_le_Vinf Γ a
    rw [← tnsDegree_le_iff_mem, hns]

/-- The zero target has degree zero in both systems (PC zero line, empty NS identity). -/
theorem tpcDegree_zero (Γ : Set (MvPolynomial σ K)) : tpcDegree Γ 0 = 0 := by
  apply le_antisymm _ (zero_le _)
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, tpcDegree_le_iff_mem]
  exact Submodule.zero_mem _

theorem tnsDegree_zero (Γ : Set (MvPolynomial σ K)) : tnsDegree Γ 0 = 0 := by
  apply le_antisymm _ (zero_le _)
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, tnsDegree_le_iff_mem]
  exact Submodule.zero_mem _

end TargetDegrees

/-! ### Membership descent for an arbitrary `K`-rational polynomial -/

section Descent

variable {σ : Type*} {K L : Type*} [Field K] [Field L] [Algebra K L]

open FieldDescent

theorem mem_Vinf_map_iff {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K} :
    map (algebraMap K L) f ∈ Vinf (mapSet L Γ) d ↔ f ∈ Vinf Γ d := by
  rw [← derives_iff_mem_Vinf, ← derives_iff_mem_Vinf]
  exact pc_derives_map_iff

theorem mem_NSspan_map_iff {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K} :
    map (algebraMap K L) f ∈ NSspan (mapSet L Γ) d ↔ f ∈ NSspan Γ d := by
  constructor
  · intro h
    obtain ⟨lam, hlam⟩ := exists_retraction K L
    have := NSspan_le_descendedNS Γ d h lam
    rwa [coeffwise_map, hlam, one_smul] at this
  · exact NSspan_map

end Descent

/-! ### Fully invariant targets -/

variable {K : Type} [Field K]

/-- **A fully invariant uniform target** for the template `T`. -/
structure Target (T : Template K) where
  /-- A fixed bound on the degree of the target (independent of the universe size). -/
  DG : ℕ
  /-- The rank-independent coefficient rule on global monomials. -/
  γ : (T.Var.Obj →₀ ℕ) → K
  γ_inv : ∀ (g : Equiv.Perm ℕ) (m : T.Var.Obj →₀ ℕ), γ (T.Var.monSMul g m) = γ m
  γ_deg : ∀ m, γ m ≠ 0 → BasisSystem.mdeg m ≤ DG

namespace Target

variable {T : Template K} (G : Target T)

theorem finite_support (t : ℕ) :
    (Function.support fun m : T.Var.Rk t →₀ ℕ => G.γ (T.Var.monUp t m)).Finite := by
  have hfin : Set.Finite {m : T.Var.Rk t →₀ ℕ | BasisSystem.mdeg m ≤ G.DG} :=
    Set.finite_coe_iff.mp (finite_mdeg_le (T.Var.Rk t) G.DG)
  apply hfin.subset
  intro m hm
  have := G.γ_deg _ hm
  rwa [mdeg_monUp] at this

/-- **The target polynomial** `G_t = ∑_{m supported in [t]} γ(m) m` at universe size `t`. -/
noncomputable def poly (t : ℕ) : MvPolynomial (T.Var.Rk t) K :=
  Finsupp.ofSupportFinite _ (G.finite_support t)

theorem coeff_poly (t : ℕ) (m : T.Var.Rk t →₀ ℕ) :
    MvPolynomial.coeff m (G.poly t) = G.γ (T.Var.monUp t m) := rfl

/-! #### The auxiliary one-axiom template (degree facts only) -/

/-- An auxiliary template with variables those of `T`, a single axiom index of empty support,
and that axiom equal to the target.  It is used only to quote the degree-stabilisation theorem
of `Templates.lean`; it is NOT a reduction of target derivability to refutation. -/
noncomputable def auxT : Template K where
  Var := T.Var
  Ax := BasisSystem.unit
  k := T.k
  s := 0
  D := G.DG
  n0 := max 1 (T.k * G.DG)
  hk := T.hk
  hn0 := le_max_left _ _
  hn0' := by simp only [Nat.add_zero]; exact le_max_right _ _
  var_bounded := T.var_bounded
  ax_bounded := BasisSystem.unit_bounded 0
  coeff := fun _ m => G.γ m
  coeff_inv := fun g _ m => G.γ_inv g m
  coeff_deg := fun _ m h => G.γ_deg m h

/-- The fixed starting rank of target-degree stabilisation, `max 1 (k·DG)`. -/
noncomputable def nG : ℕ := G.auxT.n0

theorem nG_eq : G.nG = max 1 (T.k * G.DG) := rfl

theorem auxT_poly (t : ℕ) (i : G.auxT.Ax.Rk t) : G.auxT.poly t i = G.poly t := by
  apply MvPolynomial.ext
  intro m
  rfl

/-- **The stable degree of the target**: the largest degree of a monomial with nonzero
coefficient (`0` for the zero target). -/
noncomputable def deg : ℕ := G.auxT.axDeg ()

theorem deg_le_DG : G.deg ≤ G.DG := G.auxT.axDeg_le_D ()

theorem mdeg_le_deg {m : T.Var.Obj →₀ ℕ} (h : G.γ m ≠ 0) : BasisSystem.mdeg m ≤ G.deg :=
  G.auxT.le_axDeg (i := ()) h

theorem totalDegree_poly_le (t : ℕ) : (G.poly t).totalDegree ≤ G.deg := by
  have := G.auxT.totalDegree_poly_le t ()
  rwa [G.auxT_poly] at this

/-- **Target-degree stabilisation.**  For `t ≥ nG` the degree of `G_t` is exactly `deg`. -/
theorem totalDegree_poly {t : ℕ} (ht : G.nG ≤ t) : (G.poly t).totalDegree = G.deg := by
  have := G.auxT.totalDegree_poly ht ()
  rwa [G.auxT_poly] at this

/-- Below the stable degree the target is not a degree-`d` consequence, in either system. -/
theorem not_mem_of_lt {t d : ℕ} (ht : G.nG ≤ t) (hd : d < G.deg)
    (Γ : Set (MvPolynomial (T.Var.Rk t) K)) :
    G.poly t ∉ Vinf Γ d ∧ G.poly t ∉ NSspan Γ d := by
  have hdeg := G.totalDegree_poly ht
  constructor
  · intro h
    have := (mem_restrictTotalDegree _ _ _).mp (Vinf_le_Pd Γ d h)
    omega
  · intro h
    have := (mem_restrictTotalDegree _ _ _).mp (NSspan_le_Pd Γ d h)
    omega

theorem mdeg_eq_zero' {α : Type*} {m : α →₀ ℕ} (h : BasisSystem.mdeg m = 0) : m = 0 := by
  ext a
  have := le_mdeg m a
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- A target of stable degree zero is the same constant at every rank. -/
theorem poly_eq_C_of_deg_zero (h0 : G.deg = 0) (t : ℕ) : G.poly t = C (G.γ 0) := by
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
    exact hm (mdeg_eq_zero' (by omega)).symm

/-! #### The target matrix and its realisation -/

/-- **The target matrix**: from the one-point system (singleton basis, empty support) into the
monomials of degree `≤ d`, with entry `γ(y)` in row `y`.  Invariance of `γ` is the invariance of
the matrix; rank independence is literal equality of entries at every rank. -/
noncomputable def targetM (d : ℕ) : InvMatrix K BasisSystem.unit (T.Var.mon d) where
  entry := fun y _ => G.γ y.1
  inv := fun g y _ => G.γ_inv g y.1

theorem targetM_entry (d : ℕ) (y : (T.Var.mon d).Obj) (u : BasisSystem.unit.Obj) :
    (G.targetM d).entry y u = G.γ y.1 := rfl

/-- The realised target at rank `t`, as an element of `P_{≤ d}`. -/
noncomputable def Gtr (t d : ℕ) : Pd (T.Var.Rk t) K d :=
  monBasis (T.Var.Rk t) K d ((G.targetM d).realise t (Finsupp.single () 1))

theorem coeff_Gtr (t d : ℕ) (y : (T.Var.mon d).Rk t) :
    MvPolynomial.coeff y.1 ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) =
      G.γ (T.Var.monUp t y.1) := by
  rw [← monBasis_symm_apply, Gtr, LinearEquiv.symm_apply_apply]
  exact InvMatrix.realise_single_apply (G.targetM d) t () y

/-- **The realised target is the target** once `d` bounds the degrees of all monomials with
nonzero coefficient (in particular for `d ≥ deg`). -/
theorem Gtr_coe_of {t d : ℕ} (hγ : ∀ m, G.γ m ≠ 0 → BasisSystem.mdeg m ≤ d) :
    ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) = G.poly t := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : BasisSystem.mdeg m ≤ d
  · have := G.coeff_Gtr t d ⟨m, hm⟩
    rw [this, coeff_poly]
  · rw [coeff_poly]
    have h1 : MvPolynomial.coeff m
        ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) = 0 := by
      by_contra hne
      have hmem := (G.Gtr t d).2
      rw [mem_restrictTotalDegree] at hmem
      have := le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
      exact hm (le_trans this hmem)
    rw [h1]
    by_contra hne
    have := hγ _ (Ne.symm hne)
    rw [mdeg_monUp] at this
    exact hm this

theorem Gtr_coe {t d : ℕ} (hd : G.deg ≤ d) :
    ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) = G.poly t :=
  G.Gtr_coe_of fun _ hm => le_trans (G.mdeg_le_deg hm) hd

/-- The target map `K → P_{≤ d}`, `a ↦ a • G_t`. -/
noncomputable def targetMap (t d : ℕ) : K →ₗ[K] Pd (T.Var.Rk t) K d :=
  LinearMap.toSpanSingleton K (Pd (T.Var.Rk t) K d) (G.Gtr t d)

/-- **Actual realisation of the target matrix**: in the monomial basis, the rank-`t`
realisation of `targetM d` is the map `a ↦ a • G_t` (precomposed with the basis of the trivial
module). -/
theorem targetM_realise (t d : ℕ) :
    (monBasis (T.Var.Rk t) K d).toLinearMap ∘ₗ (G.targetM d).realise t =
      G.targetMap t d ∘ₗ (Template.unitEquiv (K := K) t).toLinearMap := by
  apply Finsupp.lhom_ext'
  intro u
  apply LinearMap.ext_ring
  have hu : u = () := rfl
  subst hu
  have h1 : Template.unitEquiv (K := K) t (Finsupp.single () 1) = 1 := by
    show Finsupp.LinearEquiv.finsuppUnique K K Unit (Finsupp.single (() : Unit) (1 : K)) = 1
    rw [Finsupp.LinearEquiv.finsuppUnique_apply]
    exact Finsupp.single_eq_same
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lsingle_apply, h1, targetMap, LinearMap.toSpanSingleton_apply, one_smul]
  rfl

theorem range_targetMap_le_iff (t d : ℕ) (R : Submodule K (Pd (T.Var.Rk t) K d)) :
    LinearMap.range (G.targetMap t d) ≤ R ↔ G.Gtr t d ∈ R := by
  unfold targetMap
  rw [LinearMap.range_toSpanSingleton, Submodule.span_singleton_le_iff_mem]

theorem Gtr_mem_map_iff (t d : ℕ) (R : Submodule K (Pd (T.Var.Rk t) K d)) :
    ((G.Gtr t d : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) ∈
        R.map (Pd (T.Var.Rk t) K d).subtype ↔ G.Gtr t d ∈ R := by
  constructor
  · rintro ⟨x, hx, hx1⟩
    have : x = G.Gtr t d := Subtype.ext hx1
    rwa [← this]
  · intro h
    exact ⟨_, h, rfl⟩

/-! #### Field maps -/

/-- The same target with coefficients mapped along a field homomorphism. -/
@[reducible] def map {S : Type} [Field S] (φ : K →+* S) : Target (T.map φ) where
  DG := G.DG
  γ := fun m => φ (G.γ m)
  γ_inv := fun g m => by rw [G.γ_inv]
  γ_deg := fun m h => G.γ_deg m fun h0 => h (by rw [h0, map_zero])

theorem map_poly {S : Type} [Field S] (φ : K →+* S) (t : ℕ) :
    (G.map φ).poly t = MvPolynomial.map φ (G.poly t) := by
  apply MvPolynomial.ext
  intro m
  exact (MvPolynomial.coeff_map φ (G.poly t) m).symm

theorem map_γ_ne {S : Type} [Field S] (φ : K →+* S) {m : T.Var.Obj →₀ ℕ}
    (h : (G.map φ).γ m ≠ 0) : G.γ m ≠ 0 := fun h0 => h (by show φ _ = 0; rw [h0, map_zero])

theorem map_nG {S : Type} [Field S] (φ : K →+* S) : (G.map φ).nG = G.nG := rfl

end Target

end UniformConsequence
