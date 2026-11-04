/-
Uniform consequences, Claude return 002 (5 October 2026).  Part 2: the concrete transfer of
bounded-support INDEXED targets through the actual exact deletion functor, with doubled-support
detection of subquotients of the TARGET polynomial space.

Setting.  `T` a template, `G` an indexed target with index support `≤ t`, `d ≥ 1`.  The class
support is the conservative affine budget

    R(d) = 2kd + s + t   (the class support of `inflate T t`, whose instances are those of `T`).

The source of the target map is the permutation module of the target indices of degree `≤ d`
(support `≤ t`), NOT the trivial module, and it is not assumed simple.

* `DetectsSubquotients F W`: a subobject of a quotient of `W` killed by `F` is zero.
  `constMem_iff_of_detects`, `image_membership_iff_of_detects`: membership of the image of an
  ARBITRARY map transfers and is reflected along an exact `F` that detects subquotients of the
  ambient object.  (Proof: if `F (g) = 0` then `F (image g) = 0`, and `image g` is a subobject of a
  quotient of the ambient object.)
* `detects_canonical`: the actual shifted functor `canonicalΨ` detects subquotients of
  `K[𝒰_N]` whenever `2·supp(𝒰) ≤` the witness support.  This is the existing doubled-support
  detector `ClaudeComparison.detect` (pairing `S^⊥ ⊗ S'/S → K`); for the target ambient
  `𝒰 = monomials of degree ≤ d` the ORIGINAL bound `kd` is used, so `2kd ≤ 2kd + s + t`.
* `concDatumJ`, `catDatumJ`, `ωCompatJ`, `ΦCompatJW`: the datum with distinguished map the actual
  target matrix `J = aux.axM d` (entry `γ(b, μ)` in row `μ`, column `b`); its compatibility with
  the deletion functor is the existing `M5w.δ_mat` applied to `J`.
* `pc_all_stage_iff`, `ns_all_iff`: bridges to the actual consequence spaces of the instance.
* `all_pc_step_of_detects`, `all_ns_step_of_detects`, `all_step_of_witness`: one step.
* **`indexed_transfer`**: for every field of characteristic `p`, every `d`, every `q = p^a > R(d)`
  and every `n ≥ max(n₀, 1, k·DG + t)` with `n ≥ 2R(d) − 1`: every target indexed by `B_{n+q}` is
  a degree-`d` PC (resp. NS) consequence of `T_{n+q}` iff every target indexed by `B_n` is one
  of `T_n`.
-/
import UCIndexedTarget

set_option autoImplicit false

universe v₂ v₃ v₄ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace UniformConsequence.Indexed

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.Concrete
open DegreeProfilesReview.Deletion DegreeProfilesReview.Transport DegreeProfilesReview.SymRep
open UniformConsequence

variable {K : Type} [Field K]

/-! ### Abstract transfer through an exact functor that detects subquotients -/

section Abstract

universe v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

/-- `F` detects the subquotients of `W`: every subobject of a quotient of `W` that `F` kills is
zero.  (No faithfulness of `F` is assumed or implied elsewhere.) -/
def DetectsSubquotients (F : C ⥤ D) (W : C) : Prop :=
  ∀ ⦃Q Y : C⦄ (π : W ⟶ Q) (m : Y ⟶ Q), Epi π → Mono m → IsZero (F.obj Y) → IsZero Y

/-- An exact functor detecting the subquotients of `W` reflects vanishing of every map into a
quotient of `W`, from an ARBITRARY source. -/
theorem map_eq_zero_iff_of_detects (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesMonomorphisms] [F.PreservesEpimorphisms] {W : C} (hF : DetectsSubquotients F W)
    {Q X : C} (π : W ⟶ Q) [Epi π] (g : X ⟶ Q) : F.map g = 0 ↔ g = 0 := by
  constructor
  · intro h
    have h1 : F.map (factorThruImage g) ≫ F.map (image.ι g) = 0 := by
      rw [← F.map_comp, image.fac, h]
    have h2 : F.map (factorThruImage g) = 0 :=
      (cancel_mono (F.map (image.ι g))).mp (by rw [h1, zero_comp])
    have h3 : IsZero (F.obj (image g)) := IsZero.of_epi_eq_zero _ h2
    have h4 : IsZero (image g) := hF π (image.ι g) inferInstance inferInstance h3
    rw [← image.fac g, h4.eq_zero_of_tgt (factorThruImage g), zero_comp]
  · intro h
    rw [h, F.map_zero]

/-- **PC stage membership of an arbitrary map transfers and is reflected** along an exact functor
that detects subquotients of the ambient object. -/
theorem constMem_iff_of_detects (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P : PCDatum C} {Q : PCDatum D} (hF : DetectsSubquotients F P.W) (h : PCCompat F P Q)
    (j : ℕ) : P.ConstMem j ↔ Q.ConstMem j := by
  obtain ⟨β, hβ⟩ := stage_iso F h j
  obtain ⟨q, hq⟩ := cokernel_transport F (P.stage j).hom (Q.stage j).hom β h.αW hβ
  have key : F.map (P.c ≫ P.quot (P.stage j)) ≫ q.hom =
      h.αU.hom ≫ (Q.c ≫ Q.quot (Q.stage j)) := by
    rw [F.map_comp, Category.assoc, show F.map (P.quot (P.stage j)) ≫ q.hom =
      h.αW.hom ≫ Q.quot (Q.stage j) from hq, ← Category.assoc, h.hc, Category.assoc]
  unfold PCDatum.ConstMem
  constructor
  · intro h0
    rw [h0, F.map_zero, zero_comp] at key
    apply (cancel_epi h.αU.hom).mp
    rw [← key, comp_zero]
  · intro h0
    rw [h0, comp_zero] at key
    haveI : Epi (P.quot (P.stage j)) := by unfold PCDatum.quot; infer_instance
    apply (map_eq_zero_iff_of_detects F hF (P.quot (P.stage j)) _).mp
    apply (cancel_mono q.hom).mp
    rw [key, zero_comp]

/-- **NS image membership of an arbitrary map transfers and is reflected** along an exact functor
that detects subquotients of the ambient object. -/
theorem image_membership_iff_of_detects (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {U V S : C} (hF : DetectsSubquotients F V)
    (A : U ⟶ V) (j : S ⟶ V) {U' V' S' : D} (A' : U' ⟶ V') (j' : S' ⟶ V')
    (αU : F.obj U ≅ U') (αV : F.obj V ≅ V') (αS : F.obj S ≅ S')
    (hA : F.map A ≫ αV.hom = αU.hom ≫ A')
    (hj : F.map j ≫ αV.hom = αS.hom ≫ j') :
    j ≫ cokernel.π A = 0 ↔ j' ≫ cokernel.π A' = 0 := by
  obtain ⟨q, hq⟩ := cokernel_transport F A A' αU αV hA
  have key : F.map (j ≫ cokernel.π A) ≫ q.hom = αS.hom ≫ (j' ≫ cokernel.π A') := by
    rw [F.map_comp, Category.assoc, hq, ← Category.assoc, hj, Category.assoc]
  constructor
  · intro h0
    rw [h0, F.map_zero, zero_comp] at key
    apply (cancel_epi αS.hom).mp
    rw [← key, comp_zero]
  · intro h0
    rw [h0, comp_zero] at key
    apply (map_eq_zero_iff_of_detects F hF (cokernel.π A) _).mp
    apply (cancel_mono q.hom).mp
    rw [key, zero_comp]

end Abstract

/-! ### Doubled-support detection for the actual shifted functor -/

section Detection

open ClaudeComparison SelfContainedCycle003 SelfContainedCycle004 ClaudeCP
open DegreeProfilesReview.ShiftedM5 DegreeProfilesReview.Shifted

variable {G' : Type} [Group G']

theorem ker_isInv {X Y : Rep K G'} (f : X ⟶ Y) : IsInv X.ρ (LinearMap.ker f.hom.hom) := by
  intro g x hx
  rw [Submodule.mem_comap, LinearMap.mem_ker] at *
  have h := congrArg (fun φ => φ.hom x) (f.comm g)
  change f.hom.hom (X.ρ g x) = Y.ρ g (f.hom.hom x) at h
  rw [h, hx, map_zero]

theorem comap_range_isInv {X Y Z : Rep K G'} (f : X ⟶ Y) (m : Z ⟶ Y) :
    IsInv X.ρ ((LinearMap.range m.hom.hom).comap f.hom.hom) := by
  intro g x hx
  rw [Submodule.mem_comap, Submodule.mem_comap] at *
  have h := congrArg (fun φ => φ.hom x) (f.comm g)
  change f.hom.hom (X.ρ g x) = Y.ρ g (f.hom.hom x) at h
  rw [h]
  exact range_isInv m g hx

theorem isZero_of_subsingleton (X : Rep K G') (h : Subsingleton X.V) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

variable {p : ℕ} [Fact p.Prime] [CharP K p] {a n : ℕ} {c : Fin a → K}

/-- **Doubled-support detection for the actual deletion functor.**  With a top-power witness of
support `R`, the actual shifted functor on the canonical class of support `R` detects the
subquotients of `K[𝒰_N]` whenever `𝒰` has support `≤ r` with `2r ≤ R`.  This is the existing
`ClaudeComparison.detect`; no simplicity of any source and no faithfulness are used. -/
theorem detects_canonical (hc : Generic p c) {R : ℕ} (hRq : R < p ^ a)
    {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p R a n c w)
    {𝒰 : BasisSystem} {r : ℕ} (hU : 𝒰.Bounded r) (h2r : r + r ≤ R) (hUR : 𝒰.Bounded R) :
    DetectsSubquotients (canonicalΨ p a n R c)
      ((canonicalSchurClass K R (n + p ^ a)).toM4.perm 𝒰 hUR) := by
  intro Q Y π m hπ hm hY
  let ιN := (canonicalSchurClass K R (n + p ^ a)).P.ι
  let ιn := (canonicalSchurClass K R n).P.ι
  -- concrete facts about `π` and `m`
  have hπs : Function.Surjective (ιN.map π).hom.hom :=
    (Rep.epi_iff_surjective _).mp inferInstance
  have hmi : Function.Injective (ιN.map m).hom.hom :=
    (Rep.mono_iff_injective _).mp inferInstance
  -- the deletion of `Y` vanishes, so the projector acts as zero on `Y`
  have hY1 : IsZero ((Ψhat p a n c).obj Y.obj) := ιn.map_isZero hY
  have hY2 : Subsingleton ((Ψhat p a n c).obj Y.obj).V :=
    ModuleCat.subsingleton_of_isZero ((Action.forget (ModuleCat K) (Sfin n)).map_isZero hY1)
  have htop : topProj c w Y.obj = 0 :=
    topProj_eq_zero_of_subsingleton hc hRq hw Y.property hY2
  -- the two invariant subspaces of `K[𝒰_N]`
  let S : Submodule K (𝒰.Rk (n + p ^ a) →₀ K) := LinearMap.ker (ιN.map π).hom.hom
  let S' : Submodule K (𝒰.Rk (n + p ^ a) →₀ K) :=
    (LinearMap.range (ιN.map m).hom.hom).comap (ιN.map π).hom.hom
  have hS : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S := ker_isInv (ιN.map π)
  have hS' : IsInv (permRep K 𝒰 (n + p ^ a)).ρ S' := comap_range_isInv (ιN.map π) (ιN.map m)
  have he : ∀ x ∈ S', topProj c w (permRep K 𝒰 (n + p ^ a)) x ∈ S := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    show (ιN.map π).hom.hom (topProj c w (permRep K 𝒰 (n + p ^ a)) x) = 0
    have h1 := algebra_action_comm (ιN.map π) (topElt p a n c w) x
    have h2 := algebra_action_comm (ιN.map m) (topElt p a n c w) y
    change (ιN.map π).hom.hom (topProj c w (permRep K 𝒰 (n + p ^ a)) x) =
      topProj c w Q.obj ((ιN.map π).hom.hom x) at h1
    change (ιN.map m).hom.hom (topProj c w Y.obj y) =
      topProj c w Q.obj ((ιN.map m).hom.hom y) at h2
    have h3 : topProj c w Q.obj ((ιN.map π).hom.hom x) =
        topProj c w Q.obj ((ιN.map m).hom.hom y) := congrArg _ hy.symm
    rw [h1, h3, ← h2, htop, LinearMap.zero_apply, map_zero]
  have hle : S' ≤ S := detect hc hRq hw hU h2r hS hS' he
  -- hence `Y = 0`
  have hYsub : Subsingleton Y.obj.V := by
    constructor
    intro y y'
    have hz : ∀ y : Y.obj.V, y = 0 := by
      intro y
      obtain ⟨x, hx⟩ := hπs ((ιN.map m).hom.hom y)
      have hxS' : x ∈ S' := ⟨y, hx.symm⟩
      have hxS := hle hxS'
      apply hmi
      rw [map_zero, ← hx]
      exact hxS
    rw [hz y, hz y']
  have hY0 : IsZero (ιN.obj Y) := isZero_of_subsingleton _ hYsub
  rw [IsZero.iff_id_eq_zero]
  apply ιN.map_injective
  rw [ιN.map_id, ιN.map_zero]
  exact hY0.eq_of_src _ _

end Detection

/-! ### The datum with distinguished map the actual target matrix -/

namespace ITarget

variable {T : Template K} (G : ITarget T) {d : ℕ} (hd : 1 ≤ d)

/-- The class support of the indexed datum, `2kd + s + t`. -/
abbrev supp (d : ℕ) : ℕ := (inflate T G.t).k * d + (inflate T G.t).s

theorem supp_eq (d : ℕ) : G.supp d = 2 * T.k * d + T.s + G.t := inflate_support T G.t d

/-- The source of the target map (indices of degree `≤ d`) has support `≤ t ≤ 2kd + s + t`. -/
theorem src_bounded (d : ℕ) : (G.aux.axSys d).Bounded (G.supp d) :=
  (sub_bounded G.hB _ _).mono (by show G.t ≤ 2 * T.k * d + (T.s + G.t); omega)

/-- The span of the targets of degree `≤ d` is the range of the actual axiom map of `aux`. -/
theorem range_axMap_le_iff (n : ℕ) (R : Submodule K (Pd (T.Var.Rk n) K d)) :
    LinearMap.range (G.aux.axMap d n) ≤ R ↔
      ∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ R.map (Pd (T.Var.Rk n) K d).subtype := by
  unfold Template.axMap
  rw [Finsupp.range_linearCombination, Submodule.span_le, Set.range_subset_iff]
  apply forall_congr'
  intro i
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨x, hx, hx1⟩
    convert hx using 1
    exact Subtype.ext hx1.symm

/-! #### The actual target matrix and its realisation -/

/-- The target matrix `J = aux.axM d`: row `μ` (a monomial of degree `≤ d`), column `b` (an index
of degree `≤ d`), entry `γ(b, μ)`. -/
theorem J_entry (y : (T.Var.mon d).Obj) (i : (G.aux.axSys d).Obj) :
    (G.aux.axM d).entry y i = G.γ i.1 y.1 := rfl

/-- **Actual realisation of the target matrix**: read in the monomial basis, the rank-`n`
realisation of `J` is the actual target map `[b] ↦ G_{b,n}`. -/
theorem J_realise (n : ℕ) :
    (monBasis (T.Var.Rk n) K d).toLinearMap ∘ₗ (G.aux.axM d).realise n = G.aux.axMap d n :=
  G.aux.axM_realise d n

theorem J_realise_single (n : ℕ) (i : (G.aux.axSys d).Rk n) :
    ((monBasis (T.Var.Rk n) K d ((G.aux.axM d).realise n (Finsupp.single i 1)) :
        Pd (T.Var.Rk n) K d) : MvPolynomial (T.Var.Rk n) K) = G.poly n i.1 := by
  have h := congrArg (fun f => ((f (Finsupp.single i 1) : Pd (T.Var.Rk n) K d) :
    MvPolynomial (T.Var.Rk n) K)) (G.J_realise n)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  refine h.trans ?_
  unfold Template.axMap
  erw [Finsupp.linearCombination_single, one_smul]
  rfl

/-! #### Concrete datum -/

/-- The PC datum of actual polynomial spaces at size `n`, with distinguished map the actual
target map `K[(indices of degree ≤ d)_n] → P_{≤ d}`, `[b] ↦ G_{b,n}`. -/
noncomputable def concDatumJ (n : ℕ) : PCDatum (ModuleCat.{0} K) :=
  { (inflate T G.t).concDatum hd n with
    U := ModuleCat.of K ((G.aux.axSys d).Rk n →₀ K)
    c := ModuleCat.ofHom (G.aux.axMap d n) }

theorem concDatumJ_c (n : ℕ) : (G.concDatumJ hd n).c = ModuleCat.ofHom (G.aux.axMap d n) := rfl

theorem concDatumJ_stage (n j : ℕ) :
    (G.concDatumJ hd n).stage j = ((inflate T G.t).concDatum hd n).stage j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show (G.concDatumJ hd n).next ((G.concDatumJ hd n).stage j) =
      ((inflate T G.t).concDatum hd n).next (((inflate T G.t).concDatum hd n).stage j)
    rw [ih]
    rfl

/-- **Concrete bridge, PC.**  Beyond `n₀` (of the ORIGINAL template): categorical membership of
the target map in stage `j` is membership of every actual target of degree `≤ d` in the `j`-th
stage of the actual closure of the actual instance. -/
theorem concMem_iff {n : ℕ} (hn : T.n0 ≤ n) (j : ℕ) :
    (G.concDatumJ hd n).ConstMem j ↔
      ∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ V (T.inst n) d j := by
  unfold PCDatum.ConstMem PCDatum.quot
  rw [comp_cokernel_π_eq_zero_iff, G.concDatumJ_stage hd n j,
    ← rng_stage hd ((inflate T G.t).axMap d n) (T.inst n) (T.range_axMap d hn) j]
  exact G.range_axMap_le_iff n _

/-! #### Categorical datum inside an `M4` realisation -/

section Rank

variable {n : ℕ} {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (P : M4.{v₂, v₃, u₂, u₃} K (G.supp d) n B)

/-- The PC datum inside `B` with source the target-index module and distinguished map the target
matrix `J = aux.axM d`. -/
noncomputable def catDatumJ : PCDatum B :=
  { (inflate T G.t).catDatum hd P with
    U := P.perm (G.aux.axSys d) (G.src_bounded d)
    c := P.mat (G.src_bounded d) ((inflate T G.t).mon_bounded' d) (G.aux.axM d) }

theorem catDatumJ_c :
    (G.catDatumJ hd P).c =
      P.mat (G.src_bounded d) ((inflate T G.t).mon_bounded' d) (G.aux.axM d) := rfl

/-- The underlying-space functor carries the categorical datum to the concrete one; the new
square is the actual realisation `aux.axM_realise` of the target matrix. -/
noncomputable def ωCompatJ : PCCompat P.ω (G.catDatumJ hd P) (G.concDatumJ hd n) :=
  { (inflate T G.t).ωCompat hd P with
    αU := P.basis _ _ ≪≫ (LinearEquiv.refl K _).toModuleIso
    hc := P.sq_of_realise _ _ (G.aux.axM d) _ _ _ (G.aux.axM_realise d n) }

/-- **Bridge, PC.** -/
theorem pc_all_stage_iff (hn : T.n0 ≤ n) (j : ℕ) :
    (G.catDatumJ hd P).ConstMem j ↔
      ∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ V (T.inst n) d j :=
  (const_mem_iff P.ω (G.ωCompatJ hd P) j).trans (G.concMem_iff hd hn j)

/-- **Bridge, NS.** -/
theorem ns_all_iff (hn : T.n0 ≤ n) :
    P.mat (G.src_bounded d) ((inflate T G.t).mon_bounded' d) (G.aux.axM d) ≫
        cokernel.π (P.mat ((inflate T G.t).cert_bounded d) ((inflate T G.t).mon_bounded' d)
          ((inflate T G.t).certM d)) = 0 ↔
      ∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ NSspan (T.inst n) d := by
  have hA := P.sq_of_realise ((inflate T G.t).cert_bounded d) ((inflate T G.t).mon_bounded' d)
    ((inflate T G.t).certM d) (LinearEquiv.refl K _) (monBasis (T.Var.Rk n) K d)
    ((inflate T G.t).certMap d n) ((inflate T G.t).certM_realise d n)
  have hj := P.sq_of_realise (G.src_bounded d) ((inflate T G.t).mon_bounded' d) (G.aux.axM d)
    (LinearEquiv.refl K _) (monBasis (T.Var.Rk n) K d) (G.aux.axMap d n) (G.aux.axM_realise d n)
  have h1 := image_membership_iff P.ω
    (P.mat ((inflate T G.t).cert_bounded d) ((inflate T G.t).mon_bounded' d)
      ((inflate T G.t).certM d))
    (P.mat (G.src_bounded d) ((inflate T G.t).mon_bounded' d) (G.aux.axM d))
    (ModuleCat.ofHom ((inflate T G.t).certMap d n)) (ModuleCat.ofHom (G.aux.axMap d n))
    _ _ _ hA hj
  refine h1.trans ?_
  rw [comp_cokernel_π_eq_zero_iff]
  refine (G.range_axMap_le_iff n _).trans ?_
  have e : (LinearMap.range ((inflate T G.t).certMap d n)).map (Pd (T.Var.Rk n) K d).subtype =
      NSspan (T.inst n) d := T.range_certMap d hn
  rw [ModuleCat.hom_ofHom, e]

end Rank

/-! #### Compatibility with the deletion functor, from the existing `δ_mat` -/

section Deletion

variable {N n : ℕ}
  {BN : Type u₂} [Category.{v₂} BN] [Abelian BN] {Bn : Type u₂} [Category.{v₂} Bn] [Abelian Bn]
  {PN : M4.{v₂, v₃, u₂, u₃} K (G.supp d) N BN}
  {Pn : M4.{v₂, v₃, u₂, u₃} K (G.supp d) n Bn} {Φ : BN ⥤ Bn}

/-- **Actual target-matrix transport.**  The deletion functor carries the rank-`N` realisation of
`J` to its rank-`n` realisation: the existing field `M5w.δ_mat`, instantiated at `J`. -/
theorem J_transport (m5 : M5w.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ) :
    Φ.map (PN.mat (G.src_bounded d) ((inflate T G.t).mon_bounded' d) (G.aux.axM d)) ≫
        (m5.δ (T.Var.mon d) ((inflate T G.t).mon_bounded' d)).hom =
      (m5.δ (G.aux.axSys d) (G.src_bounded d)).hom ≫
        Pn.mat (G.src_bounded d) ((inflate T G.t).mon_bounded' d) (G.aux.axM d) :=
  m5.δ_mat _ _ (G.aux.axM d)

/-- The deletion functor carries the rank-`N` indexed datum to the rank-`n` one.  All fields are
those of the existing `ΦCompatW` except the source and the distinguished square, which is
`J_transport`. -/
noncomputable def ΦCompatJW (m5 : M5w.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ) :
    PCCompat Φ (G.catDatumJ hd PN) (G.catDatumJ hd Pn) :=
  { (inflate T G.t).ΦCompatW hd m5 with
    αU := m5.δ _ _
    hc := m5.δ_mat _ _ (G.aux.axM d) }

end Deletion

/-! #### One step along an exact functor that detects subquotients of `P_{≤ d}` -/

section Step

variable {N n : ℕ} {BN Bn : Type 1} [Category.{0} BN] [Abelian BN] [Category.{0} Bn]
  [Abelian Bn]
  {PN : M4.{0, 0, 1, 1} K (G.supp d) N BN} {Pn : M4.{0, 0, 1, 1} K (G.supp d) n Bn}
  {F : BN ⥤ Bn} [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem forall_mem_Vinf_iff {σ ι : Type*} [Finite ι] {Γ : Set (MvPolynomial σ K)} {d : ℕ}
    (f : ι → MvPolynomial σ K) :
    (∀ i, f i ∈ Vinf Γ d) ↔ ∃ j, ∀ i, f i ∈ V Γ d j := by
  classical
  constructor
  · intro h
    choose J hJ using fun i => mem_Vinf_iff.mp (h i)
    haveI := Fintype.ofFinite ι
    exact ⟨Finset.univ.sup J,
      fun i => V_mono Γ d (Finset.le_sup (Finset.mem_univ i)) (hJ i)⟩
  · rintro ⟨j, hj⟩ i
    exact mem_Vinf_iff.mpr ⟨j, hj i⟩

include hd in
/-- **Indexed transfer, ordinary PC, abstract form.** -/
theorem all_pc_step_of_detects (hN : T.n0 ≤ N) (hn : T.n0 ≤ n)
    (m5 : M5w.{0, 0, 0, 1, 1, 1} PN Pn F)
    (hdet : DetectsSubquotients F (PN.perm (T.Var.mon d) ((inflate T G.t).mon_bounded' d))) :
    (∀ i : (G.aux.axSys d).Rk N, G.poly N i.1 ∈ Vinf (T.inst N) d) ↔
      (∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ Vinf (T.inst n) d) := by
  rw [forall_mem_Vinf_iff (fun i : (G.aux.axSys d).Rk N => G.poly N i.1),
    forall_mem_Vinf_iff (fun i : (G.aux.axSys d).Rk n => G.poly n i.1)]
  apply exists_congr
  intro j
  rw [← G.pc_all_stage_iff hd PN hN j, ← G.pc_all_stage_iff hd Pn hn j]
  exact constMem_iff_of_detects F hdet (G.ΦCompatJW hd m5) j

/-- **Indexed transfer, Nullstellensatz, abstract form.** -/
theorem all_ns_step_of_detects (hN : T.n0 ≤ N) (hn : T.n0 ≤ n)
    (m5 : M5w.{0, 0, 0, 1, 1, 1} PN Pn F)
    (hdet : DetectsSubquotients F (PN.perm (T.Var.mon d) ((inflate T G.t).mon_bounded' d))) :
    (∀ i : (G.aux.axSys d).Rk N, G.poly N i.1 ∈ NSspan (T.inst N) d) ↔
      (∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ NSspan (T.inst n) d) := by
  rw [← G.ns_all_iff PN hN, ← G.ns_all_iff Pn hn]
  exact image_membership_iff_of_detects F hdet _ _ _ _ (m5.δ _ _) (m5.δ _ _) (m5.δ _ _)
    (m5.δ_mat _ _ _) (m5.δ_mat _ _ _)

end Step

/-! #### One step through the actual shifted functor -/

section Canonical

open DegreeProfilesReview.SymRep DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedFunctor
open DegreeProfilesReview.ShiftedM5 SelfContainedCycle003 SelfContainedCycle004 ClaudeCP

include hd in
/-- **Indexed transfer through the actual shifted functor** `canonicalΨ = ker z/(ker z ∩ im z)`
with its actual `canonicalM5w` data and a top-power witness of support `R(d) = 2kd + s + t`. -/
theorem all_step_of_witness {p : ℕ} [Fact p.Prime] [CharP K p] {a n : ℕ} (hn0 : T.n0 ≤ n)
    (hRq : G.supp d < p ^ a) {c : Fin a → K} (hc : Generic p c)
    {w : MonoidAlgebra K (Sfin (n + p ^ a))} (hw : IsTopWitness p (G.supp d) a n c w) :
    ((∀ i : (G.aux.axSys d).Rk (n + p ^ a),
        G.poly (n + p ^ a) i.1 ∈ Vinf (T.inst (n + p ^ a)) d) ↔
      (∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ Vinf (T.inst n) d)) ∧
    ((∀ i : (G.aux.axSys d).Rk (n + p ^ a),
        G.poly (n + p ^ a) i.1 ∈ NSspan (T.inst (n + p ^ a)) d) ↔
      (∀ i : (G.aux.axSys d).Rk n, G.poly n i.1 ∈ NSspan (T.inst n) d)) := by
  haveI : PreservesFiniteLimits (canonicalΨ p a n (G.supp d) c) :=
    top_preserves_finiteLimits hc hRq hw le_rfl
  haveI : PreservesFiniteColimits (canonicalΨ p a n (G.supp d) c) :=
    top_preserves_finiteColimits hc hRq hw le_rfl
  letI : (canonicalΨ p a n (G.supp d) c).PreservesZeroMorphisms := inferInstance
  let m5 := canonicalM5w (n := n) (r := G.supp d) hc hRq
  have h2r : T.k * d + T.k * d ≤ G.supp d := by rw [G.supp_eq]; ring_nf; omega
  have hdet := detects_canonical hc hRq hw (mon_bounded T.var_bounded d) h2r
    ((inflate T G.t).mon_bounded' d)
  have hN : T.n0 ≤ n + p ^ a := le_trans hn0 (Nat.le_add_right _ _)
  exact ⟨G.all_pc_step_of_detects hd (F := canonicalΨ p a n (G.supp d) c) hN hn0 m5 hdet,
    G.all_ns_step_of_detects (F := canonicalΨ p a n (G.supp d) c) hN hn0 m5 hdet⟩

end Canonical

end ITarget

/-! ### The unconditional indexed transfer over every field of characteristic `p` -/

namespace ITarget

variable {T : Template K} (G : ITarget T)

/-- Once `d` bounds every target degree, the indices of degree `≤ d` are all indices. -/
theorem forall_axSys_iff {d n : ℕ} (hd : ∀ b, G.deg b ≤ d) (Pr : G.B.Rk n → Prop) :
    (∀ i : (G.aux.axSys d).Rk n, Pr i.1) ↔ ∀ b : G.B.Rk n, Pr b :=
  ⟨fun h b => h ⟨b, hd _⟩, fun h i => h i.1⟩

theorem allPC_map_iff (L : Type) [Field L] [Algebra K L] (n d : ℕ) :
    (∀ b : G.B.Rk n, (G.map (algebraMap K L)).poly n b ∈
        Vinf ((T.map (algebraMap K L)).inst n) d) ↔ G.AllPC n d := by
  apply forall_congr'
  intro b
  rw [G.map_poly, T.inst_map, mem_Vinf_map_iff]

theorem allNS_map_iff (L : Type) [Field L] [Algebra K L] (n d : ℕ) :
    (∀ b : G.B.Rk n, (G.map (algebraMap K L)).poly n b ∈
        NSspan ((T.map (algebraMap K L)).inst n) d) ↔ G.AllNS n d := by
  apply forall_congr'
  intro b
  rw [G.map_poly, T.inst_map, mem_NSspan_map_iff]

end ITarget

section Final

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] {T : Template R}

/-- **Concrete bounded-support indexed-target transfer (unconditional).**  Let `T` be a uniform
template over a field `R` of prime characteristic `p` and `G` a bounded-support indexed target
(index support `≤ t`, degrees `≤ DG`).  Put `R(d) = 2kd + s + t`.  For every degree `d`, every
`q = p^a > R(d)` and every retained rank `n ≥ max(n₀, 1, k·DG + t)` with `n ≥ 2R(d) − 1`:

  every target `G_{b,n+q}`, `b ∈ B_{n+q}`, has a degree-`d` ordinary PC derivation from `T_{n+q}`
  iff every target `G_{b,n}`, `b ∈ B_n`, has one from `T_n`;

and the same for total-product degree-`d` NS identities.  For `d ≥ maxDeg` (and `d ≥ 1`) the
proof is the exact-deletion transfer of the actual target matrix over the algebraic closure, with
reflection by doubled-support detection of the subquotient `(H + im J)/H` of the TARGET polynomial
space, followed by descent to `R`; for `1 ≤ d < maxDeg` both sides are false; for `d = 0` both
sides are the rank-independent condition `ZeroDerivable`. -/
theorem indexed_transfer (G : ITarget T) {d a n : ℕ} (hn0 : T.n0 ≤ n) (hna : G.aux.n0 ≤ n)
    (hW : 2 * G.supp d - 1 ≤ n) (hRq : G.supp d < p ^ a) :
    (G.AllPC (n + p ^ a) d ↔ G.AllPC n d) ∧ (G.AllNS (n + p ^ a) d ↔ G.AllNS n d) := by
  have hn0' : T.n0 ≤ n + p ^ a := le_trans hn0 (Nat.le_add_right _ _)
  have hna' : G.aux.n0 ≤ n + p ^ a := le_trans hna (Nat.le_add_right _ _)
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    rw [G.allPC_zero_iff hn0' hna', G.allPC_zero_iff hn0 hna, G.allNS_zero_iff hn0' hna',
      G.allNS_zero_iff hn0 hna]
    exact ⟨Iff.rfl, Iff.rfl⟩
  by_cases hdeg : d < G.maxDeg
  · have h1 := G.not_all_of_lt hna' hdeg
    have h2 := G.not_all_of_lt hna hdeg
    exact ⟨iff_of_false h1.1 h2.1, iff_of_false h1.2 h2.2⟩
  push_neg at hdeg
  -- the exact-deletion step over the algebraic closure
  set L := AlgebraicClosure R
  obtain ⟨c, hc, w, hw⟩ := LinearFinal.topWitnessHypothesis_linear p L (G.supp d) a n hRq hW
  have hstep := (G.map (algebraMap R L)).all_step_of_witness hd hn0 hRq hc hw
  have hdL : ∀ b, (G.map (algebraMap R L)).deg b ≤ d :=
    fun b => le_trans (G.map_deg_le _ b) (le_trans (G.deg_le_maxDeg b) hdeg)
  have e1 : ∀ m, (∀ i : ((G.map (algebraMap R L)).aux.axSys d).Rk m,
      (G.map (algebraMap R L)).poly m i.1 ∈ Vinf ((T.map (algebraMap R L)).inst m) d) ↔
        G.AllPC m d := fun m =>
    ((G.map (algebraMap R L)).forall_axSys_iff hdL
      (fun b => (G.map (algebraMap R L)).poly m b ∈ Vinf ((T.map (algebraMap R L)).inst m) d)).trans
      (G.allPC_map_iff L m d)
  have e2 : ∀ m, (∀ i : ((G.map (algebraMap R L)).aux.axSys d).Rk m,
      (G.map (algebraMap R L)).poly m i.1 ∈ NSspan ((T.map (algebraMap R L)).inst m) d) ↔
        G.AllNS m d := fun m =>
    ((G.map (algebraMap R L)).forall_axSys_iff hdL
      (fun b => (G.map (algebraMap R L)).poly m b ∈
        NSspan ((T.map (algebraMap R L)).inst m) d)).trans
      (G.allNS_map_iff L m d)
  exact ⟨(e1 _).symm.trans (hstep.1.trans (e1 _)), (e2 _).symm.trans (hstep.2.trans (e2 _))⟩

/-- The same transfer in the written conservative range `n > 2R(d)`, `R(d) = 2kd + s + t`. -/
theorem indexed_transfer_written_range (G : ITarget T) {d a n : ℕ} (hn0 : T.n0 ≤ n)
    (hna : G.aux.n0 ≤ n) (hn : 2 * (2 * T.k * d + T.s + G.t) < n)
    (hRq : 2 * T.k * d + T.s + G.t < p ^ a) :
    (G.AllPC (n + p ^ a) d ↔ G.AllPC n d) ∧ (G.AllNS (n + p ^ a) d ↔ G.AllNS n d) := by
  have e := G.supp_eq d
  exact indexed_transfer p G hn0 hna (by omega) (by omega)

/-- The transfer stated for the actual proof systems: ordinary PC derivations and total-product
NS identities of every actual target polynomial. -/
theorem indexed_transfer_derivations (G : ITarget T) {d a n : ℕ} (hn0 : T.n0 ≤ n)
    (hna : G.aux.n0 ≤ n) (hW : 2 * G.supp d - 1 ≤ n) (hRq : G.supp d < p ^ a) :
    ((∀ b, Derives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a) b)) ↔
        ∀ b, Derives (T.inst n) d (G.poly n b)) ∧
    ((∀ b, NSDerives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a) b)) ↔
        ∀ b, NSDerives (T.inst n) d (G.poly n b)) := by
  rw [← G.allPC_iff_derives, ← G.allPC_iff_derives, ← G.allNS_iff_nsDerives,
    ← G.allNS_iff_nsDerives]
  exact indexed_transfer p G hn0 hna hW hRq

/-- **One fixed global orbit: representative transfer.**  For a fixed global index `o` and
representatives `b_N`, `b_n` of its orbit at the two ranks, the representative at rank `n + q` is
a consequence iff the representative at rank `n` is (equivalently, iff the whole orbit is). -/
theorem orbit_rep_transfer (G : ITarget T) (o : G.B.Obj) {d a n : ℕ} (hn0 : T.n0 ≤ n)
    (hna : G.aux.n0 ≤ n) (hW : 2 * G.supp d - 1 ≤ n) (hRq : G.supp d < p ^ a)
    {bN : G.B.Rk (n + p ^ a)} (hbN : G.InOrbit o bN) {bn : G.B.Rk n} (hbn : G.InOrbit o bn) :
    (G.poly (n + p ^ a) bN ∈ Vinf (T.inst (n + p ^ a)) d ↔ G.poly n bn ∈ Vinf (T.inst n) d) ∧
    (G.poly (n + p ^ a) bN ∈ NSspan (T.inst (n + p ^ a)) d ↔
      G.poly n bn ∈ NSspan (T.inst n) d) := by
  rw [G.rep_iff_orbit_pc o hbN, G.rep_iff_orbit_pc o hbn, G.rep_iff_orbit_ns o hbN,
    G.rep_iff_orbit_ns o hbn]
  exact indexed_transfer p (G.orbit o) hn0 hna hW hRq

end Final

end UniformConsequence.Indexed
