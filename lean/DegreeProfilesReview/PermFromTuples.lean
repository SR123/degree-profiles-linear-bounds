/-
Stage 3: from the injection modules to ALL bounded-support permutation modules.

`injTuples b` is the basis system of injective `b`-tuples of labels; its permutation module at
rank `t` is `P_b(t) = K[S_t / S_{t-b}] = M^{(t-b, 1^b)}`.

Theorem (`perm_mem_of_injTuples`).  Let `P` be a class of representations of `S_t` closed under
ambient quotients and binary direct sums (an `IsExactClass`).  If `P` contains `P_b(t)` for
every `b ≤ r`, then it contains `K[𝒰_t]` for EVERY basis system `𝒰` of support `≤ r`.

Proof.  For `x₀ ∈ 𝒰_t` with support `s`, `|s| = b ≤ r`, enumerate `s` by an injective tuple
`e₀`.  Any injective `b`-tuple `τ` in `{0,…,t-1}` is `g ∘ e₀` for some `g ∈ S_t`, and `g x₀`
does not depend on the choice of `g` because a permutation fixing `s` pointwise fixes `x₀`.
So `τ ↦ g x₀` is an `S_t`-equivariant map `(injTuples b)_t → 𝒰_t` hitting `x₀`, hence a
morphism `P_b(t) → K[𝒰_t]` whose image contains `e_{x₀}`.  Summing over the finitely many `x₀`
gives an epimorphism from a finite direct sum of injection modules onto `K[𝒰_t]`.

This is the second half of step 6 of the manuscript's repair ("then use finite sums and
quotients for all bounded-support permutation bases"), now a theorem.  What remains external
for M4 is that the injection modules themselves lie in the Schur image.
-/
import DegreeProfilesReview.ConcreteM4
import DegreeProfilesReview.TemplateExample
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Sort

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace DegreeProfilesReview.ConcreteM4

open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ClosedSub

/-! ### Injective tuples -/

/-- Injective `b`-tuples of labels. -/
def injTuples (b : ℕ) : BasisSystem :=
  (tuples b).sub (fun f => Function.Injective f) fun g f => by
    show Function.Injective (fun i => g (f i)) ↔ Function.Injective f
    constructor
    · intro h i j hij
      exact h (by show g (f i) = g (f j); rw [hij])
    · intro h i j hij
      exact h (g.injective hij)

theorem injTuples_bounded (b : ℕ) : (injTuples b).Bounded b :=
  BasisSystem.sub_bounded (tuples_bounded b) _ _

/-- The labels of a rank-`t` injective tuple. -/
def tupleVal {b t : ℕ} (τ : (injTuples b).Rk t) : Fin b → ℕ := fun i => (τ.1 i).val

theorem up_injTuples {b t : ℕ} (τ : (injTuples b).Rk t) :
    ((injTuples b).up t τ).1 = tupleVal τ := rfl

theorem tupleVal_lt {b t : ℕ} (τ : (injTuples b).Rk t) (i : Fin b) : tupleVal τ i < t :=
  (τ.1 i).2

theorem tupleVal_injective {b t : ℕ} (τ : (injTuples b).Rk t) : Function.Injective (tupleVal τ) :=
  τ.2

theorem tupleVal_smul {b t : ℕ} (g : Sfin t) (τ : (injTuples b).Rk t) (i : Fin b) :
    tupleVal (g • τ) i = g.1 (tupleVal τ i) := by
  have h := congrArg Subtype.val (up_smul g τ)
  exact congrFun h i

/-! ### Moving one injective tuple to another -/

/-- Two injective `b`-tuples with values below `t` differ by an element of `S_t`. -/
theorem exists_Sfin_map {b t : ℕ} (e τ : Fin b → ℕ) (he : Function.Injective e)
    (hτ : Function.Injective τ) (het : ∀ i, e i < t) (hτt : ∀ i, τ i < t) :
    ∃ g : Sfin t, ∀ i, g.1 (e i) = τ i := by
  classical
  let e' : Fin b → Fin t := fun i => ⟨e i, het i⟩
  let τ' : Fin b → Fin t := fun i => ⟨τ i, hτt i⟩
  have he' : Function.Injective e' := fun i j h => he (congrArg Fin.val h)
  have hτ' : Function.Injective τ' := fun i j h => hτ (congrArg Fin.val h)
  let E : {x : Fin t // x ∈ Set.range e'} ≃ {x : Fin t // x ∈ Set.range τ'} :=
    (Equiv.ofInjective e' he').symm.trans (Equiv.ofInjective τ' hτ')
  let σ : Equiv.Perm (Fin t) := E.extendSubtype
  let f : Fin t ≃ {k : ℕ // k < t} := Fin.equivSubtype
  let g : Equiv.Perm ℕ := σ.extendDomain f
  have hg : g ∈ Sfin t := fun k hk =>
    Equiv.Perm.extendDomain_apply_not_subtype σ f (by omega)
  refine ⟨⟨g, hg⟩, fun i => ?_⟩
  show g (e i) = τ i
  rw [Equiv.Perm.extendDomain_apply_subtype σ f (het i)]
  have h1 : f.symm ⟨e i, het i⟩ = e' i := rfl
  rw [h1]
  have h2 : σ (e' i) = τ' i := by
    show E.extendSubtype (e' i) = τ' i
    rw [E.extendSubtype_apply_of_mem (e' i) ⟨i, rfl⟩]
    show ((Equiv.ofInjective τ' hτ') ((Equiv.ofInjective e' he').symm ⟨e' i, ⟨i, rfl⟩⟩) : Fin t)
      = τ' i
    rw [Equiv.ofInjective_symm_apply]
    rfl
  rw [h2]
  rfl

/-! ### The orbit map of a basis element -/

section Orbit

variable {𝒰 : BasisSystem} {t : ℕ}

/-- Two elements of `S_t` that agree on the support of `x₀` move `x₀` to the same element. -/
theorem smul_eq_of_agree (x₀ : 𝒰.Rk t) (g g' : Sfin t)
    (h : ∀ l ∈ 𝒰.supp (𝒰.up t x₀), g.1 l = g'.1 l) : g • x₀ = g' • x₀ := by
  apply 𝒰.up_inj t
  rw [up_smul, up_smul]
  have h1 : (g'.1⁻¹ * g.1) • 𝒰.up t x₀ = 𝒰.up t x₀ := by
    apply 𝒰.fixed
    intro l hl
    rw [Equiv.Perm.mul_apply, h l hl]
    exact Equiv.symm_apply_apply g'.1 l
  rw [mul_smul] at h1
  exact inv_smul_eq_iff.mp h1

/-- The number of labels of `x₀`. -/
abbrev suppCard (x₀ : 𝒰.Rk t) : ℕ := (𝒰.supp (𝒰.up t x₀)).card

/-- The labels of `x₀`, in increasing order. -/
noncomputable def enum (x₀ : 𝒰.Rk t) : Fin (suppCard x₀) → ℕ :=
  fun i => (𝒰.supp (𝒰.up t x₀)).orderEmbOfFin rfl i

theorem enum_injective (x₀ : 𝒰.Rk t) : Function.Injective (enum x₀) :=
  ((𝒰.supp (𝒰.up t x₀)).orderEmbOfFin rfl).injective

theorem enum_mem (x₀ : 𝒰.Rk t) (i : Fin (suppCard x₀)) : enum x₀ i ∈ 𝒰.supp (𝒰.up t x₀) :=
  Finset.orderEmbOfFin_mem _ rfl i

theorem enum_lt (x₀ : 𝒰.Rk t) (i : Fin (suppCard x₀)) : enum x₀ i < t :=
  Finset.mem_range.mp (𝒰.supp_up t x₀ (enum_mem x₀ i))

theorem exists_enum (x₀ : 𝒰.Rk t) {l : ℕ} (hl : l ∈ 𝒰.supp (𝒰.up t x₀)) :
    ∃ i, enum x₀ i = l := by
  have h := Finset.range_orderEmbOfFin (𝒰.supp (𝒰.up t x₀)) rfl
  have hl' : l ∈ Set.range ((𝒰.supp (𝒰.up t x₀)).orderEmbOfFin rfl) := by
    rw [h]
    exact hl
  exact hl'

/-- An element of `S_t` carrying the labels of `x₀` to the entries of `τ`. -/
noncomputable def mover (x₀ : 𝒰.Rk t) (τ : (injTuples (suppCard x₀)).Rk t) : Sfin t :=
  Classical.choose (exists_Sfin_map (enum x₀) (tupleVal τ) (enum_injective x₀)
    (tupleVal_injective τ) (enum_lt x₀) (tupleVal_lt τ))

theorem mover_spec (x₀ : 𝒰.Rk t) (τ : (injTuples (suppCard x₀)).Rk t) (i : Fin (suppCard x₀)) :
    (mover x₀ τ).1 (enum x₀ i) = tupleVal τ i :=
  Classical.choose_spec (exists_Sfin_map (enum x₀) (tupleVal τ) (enum_injective x₀)
    (tupleVal_injective τ) (enum_lt x₀) (tupleVal_lt τ)) i

/-- **The orbit map** `τ ↦ g_τ x₀`, where `g_τ` carries the labels of `x₀` to `τ`. -/
noncomputable def orbitMap (x₀ : 𝒰.Rk t) (τ : (injTuples (suppCard x₀)).Rk t) : 𝒰.Rk t :=
  mover x₀ τ • x₀

/-- The orbit map is `S_t`-equivariant. -/
theorem orbitMap_smul (x₀ : 𝒰.Rk t) (g : Sfin t) (τ : (injTuples (suppCard x₀)).Rk t) :
    orbitMap x₀ (g • τ) = g • orbitMap x₀ τ := by
  unfold orbitMap
  rw [← mul_smul]
  apply smul_eq_of_agree
  intro l hl
  obtain ⟨i, rfl⟩ := exists_enum x₀ hl
  rw [mover_spec, tupleVal_smul, Subgroup.coe_mul, Equiv.Perm.mul_apply, mover_spec]

/-- The tuple of labels of `x₀` itself. -/
noncomputable def baseTuple (x₀ : 𝒰.Rk t) : (injTuples (suppCard x₀)).Rk t :=
  ⟨fun i => ⟨enum x₀ i, enum_lt x₀ i⟩, enum_injective x₀⟩

theorem tupleVal_baseTuple (x₀ : 𝒰.Rk t) : tupleVal (baseTuple x₀) = enum x₀ := rfl

/-- The orbit map hits `x₀`. -/
theorem orbitMap_baseTuple (x₀ : 𝒰.Rk t) : orbitMap x₀ (baseTuple x₀) = x₀ := by
  have h : mover x₀ (baseTuple x₀) • x₀ = (1 : Sfin t) • x₀ := by
    apply smul_eq_of_agree
    intro l hl
    obtain ⟨i, rfl⟩ := exists_enum x₀ hl
    rw [mover_spec, tupleVal_baseTuple]
    rfl
  unfold orbitMap
  rw [h, one_smul]

variable (K : Type) [Field K]

theorem orbit_comm (x₀ : 𝒰.Rk t) (g : Sfin t) :
    Finsupp.lmapDomain K K (orbitMap x₀) ∘ₗ
        Representation.ofMulAction K (Sfin t) ((injTuples (suppCard x₀)).Rk t) g =
      Representation.ofMulAction K (Sfin t) (𝒰.Rk t) g ∘ₗ
        Finsupp.lmapDomain K K (orbitMap x₀) := by
  apply Finsupp.lhom_ext'
  intro τ
  apply LinearMap.ext_ring
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.lsingle_apply, Representation.ofMulAction_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Representation.ofMulAction_single, orbitMap_smul]

/-- **The orbit morphism** `P_b(t) ⟶ K[𝒰_t]`, `b` the number of labels of `x₀`. -/
noncomputable def orbitHom (x₀ : 𝒰.Rk t) :
    permRep K (injTuples (suppCard x₀)) t ⟶ permRep K 𝒰 t where
  hom := ModuleCat.ofHom (Finsupp.lmapDomain K K (orbitMap x₀))
  comm := fun g => by
    apply ModuleCat.hom_ext
    exact orbit_comm K x₀ g

theorem orbitHom_single (x₀ : 𝒰.Rk t) :
    (orbitHom K x₀).hom.hom (Finsupp.single (baseTuple x₀) 1) = Finsupp.single x₀ 1 := by
  show Finsupp.lmapDomain K K (orbitMap x₀) (Finsupp.single (baseTuple x₀) 1) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, orbitMap_baseTuple]

end Orbit

/-! ### Covering a permutation module by injection modules -/

section Cover

variable {K : Type} [Field K] {r t : ℕ} (P : ObjectProperty (Rep K (Sfin t))) [IsExactClass P]

theorem rep_comp_apply {A B C : Rep K (Sfin t)} (f : A ⟶ B) (g : B ⟶ C) (m : A.V) :
    (f ≫ g).hom.hom m = g.hom.hom (f.hom.hom m) := rfl

/-- Finitely many basis vectors of `K[𝒰_t]` are covered by an object of the class. -/
theorem exists_cover (hP : ∀ b, b ≤ r → P (permRep K (injTuples b) t)) {𝒰 : BasisSystem}
    (hU : 𝒰.Bounded r) (s : Finset (𝒰.Rk t)) :
    ∃ (M : Rep K (Sfin t)) (f : M ⟶ permRep K 𝒰 t), P M ∧
      ∀ x ∈ s, (Finsupp.single x (1 : K) : 𝒰.Rk t →₀ K) ∈ LinearMap.range f.hom.hom := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, 0, prop_zero P, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | insert x₀ s _ ih =>
    obtain ⟨M, f, hM, hf⟩ := ih
    refine ⟨permRep K (injTuples (suppCard x₀)) t ⊞ M, biprod.desc (orbitHom K x₀) f,
      IsExactClass.biprod (hP _ (hU _)) hM, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine ⟨(biprod.inl : _ ⟶ permRep K (injTuples (suppCard x)) t ⊞ M).hom.hom
        (Finsupp.single (baseTuple x) 1), ?_⟩
      have h : biprod.inl ≫ biprod.desc (orbitHom K x) f = orbitHom K x := biprod.inl_desc _ _
      rw [← rep_comp_apply, h, orbitHom_single]
    · obtain ⟨m, hm⟩ := hf x hx
      refine ⟨(biprod.inr : _ ⟶ permRep K (injTuples (suppCard x₀)) t ⊞ M).hom.hom m, ?_⟩
      have h : biprod.inr ≫ biprod.desc (orbitHom K x₀) f = f := biprod.inr_desc _ _
      rw [← rep_comp_apply, h, hm]

/-- **From the injection modules to all bounded-support permutation modules.** -/
theorem perm_mem_of_injTuples (hP : ∀ b, b ≤ r → P (permRep K (injTuples b) t))
    (𝒰 : BasisSystem) (hU : 𝒰.Bounded r) : P (permRep K 𝒰 t) := by
  classical
  haveI : Fintype (𝒰.Rk t) := Fintype.ofFinite _
  obtain ⟨M, f, hM, hf⟩ := exists_cover P hP hU (Finset.univ : Finset (𝒰.Rk t))
  have hsurj : ∀ v : 𝒰.Rk t →₀ K, v ∈ LinearMap.range f.hom.hom := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add v w hv hw => exact Submodule.add_mem _ hv hw
    | single x c =>
      have h : (Finsupp.single x c : 𝒰.Rk t →₀ K) = c • Finsupp.single x 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [h]
      exact Submodule.smul_mem _ c (hf x (Finset.mem_univ x))
  haveI : Epi f := (Rep.epi_iff_surjective f).mpr fun v => by
    obtain ⟨m, hm⟩ := hsurj v
    exact ⟨m, hm⟩
  exact P.prop_of_epi f hM

end Cover

/-- A `SchurClass` from an exact class containing the injection modules `P_b(t)`, `b ≤ r`. -/
def SchurClass.ofInjTuples {K : Type} [Field K] {r t : ℕ} (P : ObjectProperty (Rep K (Sfin t)))
    [IsExactClass P] (hP : ∀ b, b ≤ r → P (permRep K (injTuples b) t)) : SchurClass K r t where
  P := P
  perm_mem := perm_mem_of_injTuples P hP

end DegreeProfilesReview.ConcreteM4
