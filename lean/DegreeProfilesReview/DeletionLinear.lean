/-
Stage 3, step 4a: the deletion construction, at the level of linear algebra.

Let a group `Γ` act linearly on `V` (`ρ`), and let `A ≤ Γ` be a subgroup.

* `inv A ρ`  — the `A`-invariants `V^A`;
* `aug A ρ`  — the span of all `a v - v`, `a ∈ A`  (so `V / aug = V_A`, the coinvariants);
* `del A ρ`  — the image of `V^A` in `V_A`.

`del` is the unit component of the semisimplification of `V|_A`: a morphism `K → V` is
negligible iff its image in `V_A` vanishes.  It is functorial for `A`-equivariant linear maps
(`delMap`), and every element of `Γ` commuting with `A` acts on it (`delRep`).

Main result (`psi_bijective`).  Let `Γ` act on a finite set `X` and linearly on `Y` (`σ`), and
let `Γ` act on `X →₀ Y = K[X] ⊗ Y` by `γ (x ⊗ y) = γx ⊗ γy` (`twist σ`).  Let `j : F → X` be an
injection onto the `A`-fixed points of `X`, and suppose every other `A`-orbit has cardinality
zero in `K`.  Then

      `F →₀ del A σ  ⟶  del A (twist σ)`,   `f ⊗ [y] ↦ [j f ⊗ y]`

is a linear bijection.  With `Y = K` this computes `del` of a permutation module as the
permutation module on the fixed points (the Brauer quotient); in general it is the statement
"the deletion functor commutes with tensoring by a permutation module".

`orbit_card_eq_zero`: the orbit hypothesis holds when `A` is a finite `p`-group and `K` has
characteristic `p`.

Everything here is proved; there is no external hypothesis.
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.CharP.Basic

namespace DegreeProfilesReview.Del

variable {K : Type*} [Field K] {Γ : Type*} [Group Γ] (A : Subgroup Γ)

/-! ### Invariants, augmentation part, and the image of invariants in coinvariants -/

section Basic

variable {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)

/-- The `A`-invariants. -/
def inv : Submodule K V where
  carrier := {v | ∀ a ∈ A, ρ a v = v}
  add_mem' := fun {v w} hv hw a ha => by rw [map_add, hv a ha, hw a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

theorem mem_inv {v : V} : v ∈ inv A ρ ↔ ∀ a ∈ A, ρ a v = v := Iff.rfl

/-- The span of all `a v - v`. -/
def aug : Submodule K V := Submodule.span K {w | ∃ a ∈ A, ∃ v, w = ρ a v - v}

theorem sub_mem_aug {a : Γ} (ha : a ∈ A) (v : V) : ρ a v - v ∈ aug A ρ :=
  Submodule.subset_span ⟨a, ha, v, rfl⟩

theorem mkQ_smul {a : Γ} (ha : a ∈ A) (v : V) :
    (aug A ρ).mkQ (ρ a v) = (aug A ρ).mkQ v := by
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact sub_mem_aug A ρ ha v

/-- The image of the invariants in the coinvariants. -/
def del : Submodule K (V ⧸ aug A ρ) := (inv A ρ).map (aug A ρ).mkQ

/-- The class of an invariant vector. -/
def delMk (v : V) (hv : v ∈ inv A ρ) : del A ρ :=
  ⟨(aug A ρ).mkQ v, Submodule.mem_map_of_mem hv⟩

theorem coe_delMk (v : V) (hv : v ∈ inv A ρ) :
    ((delMk A ρ v hv : del A ρ) : V ⧸ aug A ρ) = (aug A ρ).mkQ v := rfl

theorem del_induction (d : del A ρ) : ∃ v hv, d = delMk A ρ v hv := by
  obtain ⟨_, ⟨v, hv, rfl⟩⟩ := d
  exact ⟨v, hv, rfl⟩

theorem delMk_eq_zero_iff (v : V) (hv : v ∈ inv A ρ) :
    delMk A ρ v hv = 0 ↔ v ∈ aug A ρ := by
  rw [← Subtype.coe_inj, coe_delMk, Submodule.coe_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

end Basic

/-! ### Functoriality -/

section Functorial

variable {V W U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]
  (ρ : Representation K Γ V) (σ : Representation K Γ W) (υ : Representation K Γ U)

/-- `f` commutes with the action of `A`. -/
def AEquivariant (f : V →ₗ[K] W) : Prop := ∀ a ∈ A, ∀ v, f (ρ a v) = σ a (f v)

variable {A ρ σ υ}

theorem map_mem_inv {f : V →ₗ[K] W} (hf : AEquivariant A ρ σ f) {v : V} (hv : v ∈ inv A ρ) :
    f v ∈ inv A σ := fun a ha => by rw [← hf a ha, hv a ha]

theorem aug_le_comap {f : V →ₗ[K] W} (hf : AEquivariant A ρ σ f) :
    aug A ρ ≤ (aug A σ).comap f := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, hf a ha]
  exact sub_mem_aug A σ ha (f v)

/-- The map induced on `del` by an `A`-equivariant linear map. -/
def delMap (f : V →ₗ[K] W) (hf : AEquivariant A ρ σ f) : del A ρ →ₗ[K] del A σ :=
  ((aug A ρ).mapQ (aug A σ) f (aug_le_comap hf)).restrict (p := del A ρ) (q := del A σ) (by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨f v, map_mem_inv hf hv, rfl⟩)

theorem delMap_delMk (f : V →ₗ[K] W) (hf : AEquivariant A ρ σ f) (v : V) (hv : v ∈ inv A ρ) :
    delMap f hf (delMk A ρ v hv) = delMk A σ (f v) (map_mem_inv hf hv) := rfl

theorem delMap_id (h : AEquivariant A ρ ρ LinearMap.id) : delMap LinearMap.id h = LinearMap.id := by
  apply LinearMap.ext
  intro d
  obtain ⟨v, hv, rfl⟩ := del_induction A ρ d
  rfl

theorem delMap_comp {f : V →ₗ[K] W} {g : W →ₗ[K] U} (hf : AEquivariant A ρ σ f)
    (hg : AEquivariant A σ υ g) (hgf : AEquivariant A ρ υ (g ∘ₗ f)) :
    delMap (g ∘ₗ f) hgf = delMap g hg ∘ₗ delMap f hf := by
  apply LinearMap.ext
  intro d
  obtain ⟨v, hv, rfl⟩ := del_induction A ρ d
  rfl

theorem delMap_congr {f g : V →ₗ[K] W} (hf : AEquivariant A ρ σ f) (hg : AEquivariant A ρ σ g)
    (h : f = g) : delMap f hf = delMap g hg := by
  subst h
  rfl

theorem AEquivariant.comp {f : V →ₗ[K] W} {g : W →ₗ[K] U} (hf : AEquivariant A ρ σ f)
    (hg : AEquivariant A σ υ g) : AEquivariant A ρ υ (g ∘ₗ f) := fun a ha v => by
  rw [LinearMap.comp_apply, hf a ha, hg a ha, LinearMap.comp_apply]

theorem AEquivariant.symm (e : V ≃ₗ[K] W) (he : AEquivariant A ρ σ e.toLinearMap) :
    AEquivariant A σ ρ e.symm.toLinearMap := fun a ha w => by
  apply e.injective
  have := he a ha (e.symm w)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
  exact this.symm

/-- An `A`-equivariant linear equivalence induces a linear equivalence on `del`. -/
def delEquiv (e : V ≃ₗ[K] W) (he : AEquivariant A ρ σ e.toLinearMap) : del A ρ ≃ₗ[K] del A σ :=
  LinearEquiv.ofLinear (delMap e.toLinearMap he) (delMap e.symm.toLinearMap (he.symm e))
    (by
      apply LinearMap.ext
      intro d
      obtain ⟨w, hw, rfl⟩ := del_induction A σ d
      rw [LinearMap.comp_apply, delMap_delMk, delMap_delMk]
      apply Subtype.ext
      simp [coe_delMk])
    (by
      apply LinearMap.ext
      intro d
      obtain ⟨v, hv, rfl⟩ := del_induction A ρ d
      rw [LinearMap.comp_apply, delMap_delMk, delMap_delMk]
      apply Subtype.ext
      simp [coe_delMk])

theorem delEquiv_delMk (e : V ≃ₗ[K] W) (he : AEquivariant A ρ σ e.toLinearMap) (v : V)
    (hv : v ∈ inv A ρ) : delEquiv e he (delMk A ρ v hv) = delMk A σ (e v) (map_mem_inv he hv) :=
  rfl

end Functorial

/-! ### The residual action -/

section Residual

variable {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)
  {G₀ : Type*} [Group G₀] (i : G₀ →* Γ) (hcomm : ∀ g, ∀ a ∈ A, i g * a = a * i g)

include hcomm in
theorem aequivariant_of_comm (g : G₀) : AEquivariant A ρ ρ (ρ (i g)) := fun a ha v => by
  rw [← Module.End.mul_apply, ← map_mul, hcomm g a ha, map_mul, Module.End.mul_apply]

/-- The action on `del` of a group commuting with `A`. -/
def delRep : Representation K G₀ (del A ρ) where
  toFun g := delMap (ρ (i g)) (aequivariant_of_comm A ρ i hcomm g)
  map_one' := by
    apply LinearMap.ext
    intro d
    obtain ⟨v, hv, rfl⟩ := del_induction A ρ d
    rw [delMap_delMk]
    apply Subtype.ext
    simp [coe_delMk]
  map_mul' := fun g h => by
    apply LinearMap.ext
    intro d
    obtain ⟨v, hv, rfl⟩ := del_induction A ρ d
    rw [Module.End.mul_apply, delMap_delMk, delMap_delMk, delMap_delMk]
    apply Subtype.ext
    simp [coe_delMk]

theorem delRep_delMk (g : G₀) (v : V) (hv : v ∈ inv A ρ) :
    delRep A ρ i hcomm g (delMk A ρ v hv) =
      delMk A ρ (ρ (i g) v) (map_mem_inv (aequivariant_of_comm A ρ i hcomm g) hv) := rfl

end Residual

/-! ### The action on `X →₀ Y = K[X] ⊗ Y` -/

section Twist

variable {X : Type*} [MulAction Γ X] {Y : Type*} [AddCommGroup Y] [Module K Y]
  (σ : Representation K Γ Y)

/-- `γ (x ⊗ y) = γ x ⊗ γ y` on `X →₀ Y`. -/
noncomputable def twist : Representation K Γ (X →₀ Y) where
  toFun γ := Finsupp.lsum K fun x => Finsupp.lsingle (γ • x) ∘ₗ σ γ
  map_one' := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro y
    simp
  map_mul' := fun γ γ' => by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro y
    simp [mul_smul]

theorem twist_single (γ : Γ) (x : X) (y : Y) :
    twist (X := X) σ γ (Finsupp.single x y) = Finsupp.single (γ • x) (σ γ y) := by
  simp [twist]

theorem twist_smul_apply (γ : Γ) (m : X →₀ Y) (x : X) :
    (twist σ γ m) (γ • x) = σ γ (m x) := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' => rw [map_add, Finsupp.add_apply, hm, hm', Finsupp.add_apply, map_add]
  | single x' y =>
    rw [twist_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : x' = x
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun h' => h (smul_left_cancel γ h')), map_zero]

/-- An invariant element of `X →₀ Y` has `A`-equivariant coefficients. -/
theorem apply_smul_of_mem_inv {m : X →₀ Y} (hm : m ∈ inv A (twist (X := X) σ)) {a : Γ}
    (ha : a ∈ A) (x : X) : m (a • x) = σ a (m x) := by
  rw [← twist_smul_apply σ a m x, hm a ha]

end Twist

/-! ### The comparison map and its bijectivity -/

section Psi

variable {X : Type*} [MulAction Γ X] {Y : Type*} [AddCommGroup Y] [Module K Y]
  (σ : Representation K Γ Y) {F : Type*} (j : F → X)
  (hfix : ∀ f, ∀ a ∈ A, a • j f = j f)

include hfix in
theorem lsingle_aequivariant (f : F) :
    AEquivariant A σ (twist (X := X) σ) (Finsupp.lsingle (j f)) := fun a ha y => by
  rw [Finsupp.lsingle_apply, Finsupp.lsingle_apply, twist_single, hfix f a ha]

include hfix in
theorem lapply_aequivariant (f : F) :
    AEquivariant A (twist (X := X) σ) σ (Finsupp.lapply (j f)) := fun a ha m => by
  rw [Finsupp.lapply_apply, Finsupp.lapply_apply]
  conv_lhs => rw [← hfix f a ha]
  exact twist_smul_apply σ a m (j f)

/-- `f ⊗ [y] ↦ [j f ⊗ y]`. -/
noncomputable def psi : (F →₀ del A σ) →ₗ[K] del A (twist (X := X) σ) :=
  Finsupp.lsum K fun f => delMap (Finsupp.lsingle (j f)) (lsingle_aequivariant A σ j hfix f)

theorem psi_single (f : F) (y : Y) (hy : y ∈ inv A σ) :
    psi A σ j hfix (Finsupp.single f (delMk A σ y hy)) =
      delMk A (twist σ) (Finsupp.single (j f) y)
        (map_mem_inv (lsingle_aequivariant A σ j hfix f) hy) := by
  simp [psi, delMap_delMk]

variable (hj : Function.Injective j)

include hj in
/-- Evaluation at a fixed point recovers the coefficient. -/
theorem eval_psi (f₀ : F) :
    delMap (Finsupp.lapply (j f₀)) (lapply_aequivariant A σ j hfix f₀) ∘ₗ psi A σ j hfix =
      Finsupp.lapply f₀ := by
  classical
  apply Finsupp.lhom_ext'
  intro f
  apply LinearMap.ext
  intro d
  obtain ⟨y, hy, rfl⟩ := del_induction A σ d
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, psi_single,
    delMap_delMk, LinearMap.comp_apply, Finsupp.lsingle_apply]
  apply Subtype.ext
  rw [coe_delMk, Finsupp.lapply_apply, Finsupp.lapply_apply, Finsupp.single_apply,
    Finsupp.single_apply]
  by_cases h : f = f₀
  · subst h
    rw [if_pos rfl, if_pos rfl, coe_delMk]
  · rw [if_neg h, if_neg (fun h' => h (hj h')), map_zero, Submodule.coe_zero]

include hj in
theorem psi_injective : Function.Injective (psi A σ j hfix) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  ext f₀
  have h := LinearMap.congr_fun (eval_psi A σ j hfix hj f₀) v
  rw [LinearMap.comp_apply, hv, map_zero, Finsupp.lapply_apply] at h
  rw [← h, Finsupp.zero_apply, Submodule.coe_zero]

end Psi

/-! ### Surjectivity: the non-fixed orbits contribute nothing -/

section Surj

variable {X : Type*} [MulAction Γ X] {Y : Type*} [AddCommGroup Y] [Module K Y]
  (σ : Representation K Γ Y) {F : Type*} (j : F → X)
  (hfix : ∀ f, ∀ a ∈ A, a • j f = j f)

open Classical in
include hfix in
/-- For an invariant element, the terms at points outside the image of `j` cancel in the
coinvariants, orbit by orbit: all terms of an orbit are equal and the orbit has cardinality
zero in `K`. -/
theorem sum_nonfixed_eq_zero [Fintype X]
    (horb : ∀ x, x ∉ Set.range j → ((Nat.card (MulAction.orbit A x) : ℕ) : K) = 0)
    {m : X →₀ Y} (hm : m ∈ inv A (twist (X := X) σ)) :
    ∑ x : X, (if x ∈ Set.range j then 0
      else (aug A (twist (X := X) σ)).mkQ (Finsupp.single x (m x))) = 0 := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient A X) := Fintype.ofFinite _
  rw [← Finset.sum_fiberwise Finset.univ
    (fun x => (Quotient.mk'' x : MulAction.orbitRel.Quotient A X))]
  apply Finset.sum_eq_zero
  intro ω _
  obtain ⟨x₀, rfl⟩ := Quotient.exists_rep ω
  have hmem : ∀ x, (Quotient.mk'' x : MulAction.orbitRel.Quotient A X) = Quotient.mk'' x₀ ↔
      x ∈ MulAction.orbit A x₀ := fun x => by
    rw [Quotient.eq'', MulAction.orbitRel_apply]
  by_cases h0 : x₀ ∈ Set.range j
  · apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨⟨a, ha⟩, rfl⟩ := (hmem x).mp hx.2
    obtain ⟨f, rfl⟩ := h0
    rw [if_pos]
    exact ⟨f, (hfix f a ha).symm⟩
  · have hterm : ∀ x ∈ Finset.univ.filter (fun x =>
        (Quotient.mk'' x : MulAction.orbitRel.Quotient A X) = Quotient.mk'' x₀),
        (if x ∈ Set.range j then 0
          else (aug A (twist (X := X) σ)).mkQ (Finsupp.single x (m x))) =
        (aug A (twist (X := X) σ)).mkQ (Finsupp.single x₀ (m x₀)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨⟨a, ha⟩, rfl⟩ := (hmem x).mp hx.2
      have hnot : (⟨a, ha⟩ : A) • x₀ ∉ Set.range j := by
        rintro ⟨f, hf⟩
        apply h0
        refine ⟨f, ?_⟩
        have h1 : a⁻¹ • j f = j f := hfix f a⁻¹ (A.inv_mem ha)
        have h2 : a • x₀ = j f := hf.symm
        rw [← h1, ← h2, inv_smul_smul]
      rw [if_neg hnot]
      show (aug A (twist (X := X) σ)).mkQ (Finsupp.single (a • x₀) (m (a • x₀))) = _
      rw [apply_smul_of_mem_inv A σ hm ha, ← twist_single, mkQ_smul A _ ha]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const]
    have hcard : (Finset.univ.filter (fun x =>
        (Quotient.mk'' x : MulAction.orbitRel.Quotient A X) = Quotient.mk'' x₀)).card =
        Nat.card (MulAction.orbit A x₀) := by
      haveI : Fintype (MulAction.orbit A x₀) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_of_subtype _ (fun x => by rw [Finset.mem_filter, hmem]; simp)).symm
    rw [hcard, ← Nat.cast_smul_eq_nsmul K, horb x₀ h0, zero_smul]

variable (hj : Function.Injective j)

include hj in
theorem psi_surjective [Finite X]
    (horb : ∀ x, x ∉ Set.range j → ((Nat.card (MulAction.orbit A x) : ℕ) : K) = 0) :
    Function.Surjective (psi A σ j hfix) := by
  classical
  haveI := Fintype.ofFinite X
  haveI : Finite F := Finite.of_injective j hj
  haveI := Fintype.ofFinite F
  intro d
  obtain ⟨m, hm, rfl⟩ := del_induction A _ d
  have hcoef : ∀ f, m (j f) ∈ inv A σ := fun f a ha => by
    rw [← apply_smul_of_mem_inv A σ hm ha, hfix f a ha]
  refine ⟨∑ f : F, Finsupp.single f (delMk A σ (m (j f)) (hcoef f)), ?_⟩
  apply Subtype.ext
  rw [map_sum, coe_delMk, Submodule.coe_sum]
  simp only [psi_single, coe_delMk]
  have hm_sum : m = ∑ x : X, Finsupp.single x (m x) := (Finsupp.univ_sum_single m).symm
  conv_rhs => rw [hm_sum, map_sum]
  have hsplit : ∀ x : X, (aug A (twist (X := X) σ)).mkQ (Finsupp.single x (m x)) =
      (if x ∈ Set.range j then (aug A (twist (X := X) σ)).mkQ (Finsupp.single x (m x)) else 0) +
      (if x ∈ Set.range j then 0
        else (aug A (twist (X := X) σ)).mkQ (Finsupp.single x (m x))) := by
    intro x
    split_ifs <;> simp
  have hB : (∑ x : X, if x ∈ Set.range j then 0
      else (aug A (twist (X := X) σ)).mkQ (Finsupp.single x (m x))) = 0 := by
    convert sum_nonfixed_eq_zero A σ j hfix horb hm
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib, hB, add_zero,
    ← Finset.sum_filter]
  have himg : Finset.univ.filter (fun x => x ∈ Set.range j) = Finset.univ.image j := by
    ext x
    simp [Set.mem_range]
  rw [himg, Finset.sum_image (fun a _ b _ h => hj h)]

include hj in
theorem psi_bijective [Finite X]
    (horb : ∀ x, x ∉ Set.range j → ((Nat.card (MulAction.orbit A x) : ℕ) : K) = 0) :
    Function.Bijective (psi A σ j hfix) :=
  ⟨psi_injective A σ j hfix hj, psi_surjective A σ j hfix hj horb⟩

end Surj

/-! ### The orbit hypothesis for `p`-groups in characteristic `p` -/

theorem orbit_card_eq_zero {X : Type*} [MulAction Γ X] [Finite X] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hA : IsPGroup p A) (x : X) (hx : ∃ a ∈ A, a • x ≠ x) :
    ((Nat.card (MulAction.orbit A x) : ℕ) : K) = 0 := by
  obtain ⟨n, hn⟩ := hA.card_orbit x
  rw [hn]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exfalso
    rw [h0, pow_zero] at hn
    obtain ⟨a, ha, hax⟩ := hx
    haveI : Subsingleton (MulAction.orbit A x) := (Nat.card_eq_one_iff_unique.mp hn).1
    have h1 : (⟨(⟨a, ha⟩ : A) • x, MulAction.mem_orbit x _⟩ : MulAction.orbit A x) =
        ⟨x, MulAction.mem_orbit_self x⟩ := Subsingleton.elim _ _
    exact hax (congrArg Subtype.val h1)
  · rw [Nat.cast_pow, CharP.cast_eq_zero K p, zero_pow (Nat.pos_iff_ne_zero.mp hpos)]

end DegreeProfilesReview.Del
