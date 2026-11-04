/-
Stage 5, step 3: degree data for an elementary abelian `p`-group, and the acyclicity of the
non-fixed points for generic coefficients.

Setting: `φ : (ℤ/p)^ι → Γ` a homomorphism (written multiplicatively), `gen φ i = φ (e_i)` the
images of the standard basis, `char K = p`, and `Γ` acting on a set `X`.

`Generic p c`: the coefficients `c : ι → K` are linearly independent over the prime field,
stated explicitly as `∑ c i * (g i : K) = 0 → g = 0` for `g : ι → ℤ/p`.

Construction (`degreeData`).  For `x ∈ X` let `x₀` be a chosen representative of its orbit under
`(ℤ/p)^ι`.  Its stabiliser is an `𝔽_p`-subspace; choose a linear functional `ℓ` vanishing on it,
nonzero unless the stabiliser is everything.  Put

      `π x = ℓ v`  where `φ v • x₀ = x`   (well defined because `ℓ` kills the stabiliser),
      `e i x = ℓ (e_i)`.

Then `π (gen i • x) = π x + e i x`, the `e i` are constant on orbits, and at a point `x` moved by
the group `w x = ∑ c i * e i x ≠ 0`, because `ℓ ≠ 0` and `c` is generic.

**Theorem (`nonfixedAcyclic`).**  If every point outside the image of `j` is moved by the group
and `c` is generic, then the hypothesis `NonfixedAcyclic` of `ShiftedLinear.lean` holds: a vector
of `K[X] ⊗ Y` killed by `z` and vanishing at the points `j f` lies in the range of `z`.

`nonfixed_free`, `ker_eq_range_pow_of_no_fixed_points`: the same in the form of freeness over
`K[z]/(z^p)`; the latter is Lemma 8.3.2 of Hone et al. (induced modules are free over a generic
shifted cyclic subgroup) for the modules `K[X] ⊗ Y`.

No freeness of the non-fixed orbits is assumed: stabilisers may be arbitrary proper subgroups.
Everything here is proved; there is no external hypothesis.
-/
import DegreeProfilesReview.ShiftedFree
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi

namespace DegreeProfilesReview.Shifted

open DegreeProfilesReview.Del Multiplicative

variable {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (φ : Multiplicative (ι → ZMod p) →* Γ)

/-- The images of the standard basis vectors. -/
def gen (i : ι) : Γ := φ (ofAdd (Pi.single i 1))

omit [Fintype ι] in
theorem gen_comm (i k : ι) : gen φ i * gen φ k = gen φ k * gen φ i := by
  unfold gen
  rw [← φ.map_mul, ← φ.map_mul, mul_comm]

omit [Fintype ι] in
theorem gen_pow (i : ι) : gen φ i ^ p = 1 := by
  unfold gen
  rw [← map_pow, ← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero p, ofAdd_zero, map_one]

/-- Linear independence of the coefficients over the prime field, stated explicitly. -/
def Generic (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p] (c : ι → K) : Prop :=
  ∀ g : ι → ZMod p, ∑ i, c i * ZMod.castHom (dvd_refl p) K (g i) = 0 → g = 0

section Orbits

variable {X : Type*} [MulAction Γ X]

omit [Fintype ι] [DecidableEq ι] in
theorem φ_add_smul (v w : ι → ZMod p) (x : X) :
    φ (ofAdd (v + w)) • x = φ (ofAdd v) • φ (ofAdd w) • x := by
  rw [ofAdd_add, map_mul, mul_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem φ_zero_smul (x : X) : φ (ofAdd (0 : ι → ZMod p)) • x = x := by
  rw [ofAdd_zero, map_one, one_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem φ_neg_smul (v : ι → ZMod p) (x : X) :
    φ (ofAdd (-v)) • φ (ofAdd v) • x = x := by
  rw [← φ_add_smul, neg_add_cancel, φ_zero_smul]

/-- The stabiliser, as an additive subgroup. -/
def stabAdd (x : X) : AddSubgroup (ι → ZMod p) where
  carrier := {v | φ (ofAdd v) • x = x}
  zero_mem' := φ_zero_smul φ x
  add_mem' := fun {v w} hv hw => by
    show φ (ofAdd (v + w)) • x = x
    rw [φ_add_smul, (show φ (ofAdd w) • x = x from hw), (show φ (ofAdd v) • x = x from hv)]
  neg_mem' := fun {v} hv => by
    show φ (ofAdd (-v)) • x = x
    have h := φ_neg_smul φ v x
    rwa [(show φ (ofAdd v) • x = x from hv)] at h

/-- The stabiliser, as an `𝔽_p`-subspace. -/
def stab (x : X) : Submodule (ZMod p) (ι → ZMod p) := AddSubgroup.toZModSubmodule p (stabAdd φ x)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_stab {x : X} {v : ι → ZMod p} : v ∈ stab φ x ↔ φ (ofAdd v) • x = x := Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The group is abelian, so stabilisers are constant on orbits. -/
theorem stab_smul (w : ι → ZMod p) (x : X) : stab φ (φ (ofAdd w) • x) = stab φ x := by
  ext v
  rw [mem_stab, mem_stab, ← φ_add_smul, add_comm, φ_add_smul]
  constructor
  · intro h
    have := congrArg (fun y => φ (ofAdd (-w)) • y) h
    simpa only [φ_neg_smul] using this
  · intro h
    rw [h]

omit [Fintype ι] [DecidableEq ι] in
/-- If `φ v • x₀ = φ u • x₀` then `v - u` stabilises `x₀`. -/
theorem sub_mem_stab {x₀ : X} {v u : ι → ZMod p} (h : φ (ofAdd v) • x₀ = φ (ofAdd u) • x₀) :
    v - u ∈ stab φ x₀ := by
  rw [mem_stab, sub_eq_neg_add, φ_add_smul, h, φ_neg_smul]

/-- The orbit relation. -/
def orbSetoid (X : Type*) [MulAction Γ X] : Setoid X where
  r x y := ∃ v : ι → ZMod p, φ (ofAdd v) • x = y
  iseqv :=
    { refl := fun x => ⟨0, φ_zero_smul φ x⟩
      symm := by
        rintro x y ⟨v, rfl⟩
        exact ⟨-v, φ_neg_smul φ v x⟩
      trans := by
        rintro x y z ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨w + v, φ_add_smul φ w v x⟩ }

/-- A chosen representative of the orbit of `x`. -/
noncomputable def rep (x : X) : X := (Quotient.mk (orbSetoid φ X) x).out

omit [Fintype ι] [DecidableEq ι] in
theorem exists_shift (x : X) : ∃ v : ι → ZMod p, φ (ofAdd v) • rep φ x = x :=
  Quotient.mk_out (s := orbSetoid φ X) x

/-- A chosen group element taking the representative to `x`. -/
noncomputable def shift (x : X) : ι → ZMod p := (exists_shift φ x).choose

omit [Fintype ι] [DecidableEq ι] in
theorem shift_spec (x : X) : φ (ofAdd (shift φ x)) • rep φ x = x := (exists_shift φ x).choose_spec

omit [Fintype ι] [DecidableEq ι] in
theorem rep_smul (w : ι → ZMod p) (x : X) : rep φ (φ (ofAdd w) • x) = rep φ x := by
  unfold rep
  congr 1
  apply Quotient.sound
  exact ⟨-w, φ_neg_smul φ w x⟩

omit [Fintype ι] [DecidableEq ι] in
theorem stab_rep (x : X) : stab φ (rep φ x) = stab φ x := by
  conv_rhs => rw [← shift_spec φ x, stab_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_functional (x₀ : X) :
    ∃ ℓ : (ι → ZMod p) →ₗ[ZMod p] ZMod p,
      stab φ x₀ ≤ LinearMap.ker ℓ ∧ (stab φ x₀ ≠ ⊤ → ℓ ≠ 0) := by
  by_cases h : stab φ x₀ = ⊤
  · exact ⟨0, by simp, fun h' => absurd h h'⟩
  · have hlt : stab φ x₀ < ⊤ := lt_top_iff_ne_top.mpr h
    obtain ⟨ℓ, hℓ0, hℓ⟩ := (stab φ x₀).exists_le_ker_of_lt_top hlt
    exact ⟨ℓ, hℓ, fun _ => hℓ0⟩

/-- The chosen functional at an orbit representative. -/
noncomputable def fnl₀ (x₀ : X) : (ι → ZMod p) →ₗ[ZMod p] ZMod p :=
  (exists_functional φ x₀).choose

/-- The chosen functional of the orbit of `x`. -/
noncomputable def fnl (x : X) : (ι → ZMod p) →ₗ[ZMod p] ZMod p := fnl₀ φ (rep φ x)

omit [Fintype ι] [DecidableEq ι] in
theorem fnl_smul (w : ι → ZMod p) (x : X) : fnl φ (φ (ofAdd w) • x) = fnl φ x := by
  unfold fnl
  rw [rep_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem fnl_stab {x : X} {v : ι → ZMod p} (hv : v ∈ stab φ (rep φ x)) : fnl φ x v = 0 :=
  LinearMap.mem_ker.mp ((exists_functional φ (rep φ x)).choose_spec.1 hv)

omit [Fintype ι] [DecidableEq ι] in
theorem fnl_ne_zero {x : X} (hx : ∃ v : ι → ZMod p, φ (ofAdd v) • x ≠ x) : fnl φ x ≠ 0 := by
  apply (exists_functional φ (rep φ x)).choose_spec.2
  rw [stab_rep]
  obtain ⟨v, hv⟩ := hx
  intro h
  apply hv
  have : v ∈ stab φ x := by
    rw [h]
    exact Submodule.mem_top
  exact this

variable (K : Type*) [Field K] [CharP K p]

/-- **Degree data for the action of `(ℤ/p)^ι`.** -/
noncomputable def degreeData : DegreeData K (gen φ) X where
  π x := ZMod.castHom (dvd_refl p) K (fnl φ x (shift φ x))
  e i x := ZMod.castHom (dvd_refl p) K (fnl φ x (Pi.single i 1))
  π_smul := fun i x => by
    rw [← map_add, ← map_add]
    congr 1
    have hfnl : fnl φ (gen φ i • x) = fnl φ x := fnl_smul φ _ x
    rw [hfnl]
    -- both shifts take `rep x` to `gen i • x`
    have h1 : φ (ofAdd (shift φ (gen φ i • x))) • rep φ x = gen φ i • x := by
      have := shift_spec φ (gen φ i • x)
      rwa [show rep φ (gen φ i • x) = rep φ x from rep_smul φ _ x] at this
    have h2 : φ (ofAdd (shift φ x + Pi.single i 1)) • rep φ x = gen φ i • x := by
      rw [add_comm, φ_add_smul, shift_spec]
      rfl
    have h3 := fnl_stab φ (sub_mem_stab φ (h1.trans h2.symm))
    rw [map_sub, sub_eq_zero] at h3
    exact h3
  e_smul := fun i k x => by
    have hfnl : fnl φ (gen φ k • x) = fnl φ x := fnl_smul φ _ x
    rw [hfnl]

variable {K}

/-- At a point moved by the group, `w ≠ 0` for generic coefficients. -/
theorem degreeData_w_ne_zero {c : ι → K} (hc : Generic p c) {x : X}
    (hx : ∃ v : ι → ZMod p, φ (ofAdd v) • x ≠ x) : (degreeData φ K (X := X)).w c x ≠ 0 := by
  intro hw
  apply fnl_ne_zero φ hx
  have hg := hc (fun i => fnl φ x (Pi.single i 1)) hw
  apply LinearMap.pi_ext
  intro i a
  have h1 : (Pi.single i a : ι → ZMod p) = a • (Pi.single i 1 : ι → ZMod p) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [h1, map_smul, LinearMap.zero_apply]
  have h2 : fnl φ x (Pi.single i 1) = 0 := congrFun hg i
  rw [h2, smul_zero]

end Orbits

/-! ### The acyclicity of the non-fixed points -/

section Acyclic

variable {K : Type*} [Field K] [CharP K p] {X : Type*} [MulAction Γ X]
  {Y : Type*} [AddCommGroup Y] [Module K Y] (σ : Representation K Γ Y) {F : Type*} (j : F → X)

/-- **The non-fixed points contribute nothing**, for generic coefficients. -/
theorem nonfixedAcyclic {c : ι → K} (hc : Generic p c)
    (hmoved : ∀ x, x ∉ Set.range j → ∃ v : ι → ZMod p, φ (ofAdd v) • x ≠ x) :
    NonfixedAcyclic (gen φ) c σ j := by
  intro m hm hzero
  apply mem_range_of_degreeData c σ (degreeData φ K) (gen_comm φ) (gen_pow φ) hm
  intro x hx
  apply degreeData_w_ne_zero φ hc
  apply hmoved
  rintro ⟨f, rfl⟩
  exact hx (hzero f)

/-- The same in the stronger form: the non-fixed part is FREE over `K[z]/(z^p)`
(`ker z ⊆ range z^(p-1)` there). -/
theorem nonfixed_free {c : ι → K} (hc : Generic p c)
    (hmoved : ∀ x, x ∉ Set.range j → ∃ v : ι → ZMod p, φ (ofAdd v) • x ≠ x)
    {m : X →₀ Y} (hm : zOp (gen φ) c (twist (X := X) σ) m = 0) (hzero : ∀ f, m (j f) = 0) :
    m ∈ LinearMap.range
      ((zOp (gen φ) c (twist (X := X) σ) : Module.End K (X →₀ Y)) ^ (p - 1)) := by
  apply mem_range_pow_of_degreeData c σ (degreeData φ K) (gen_comm φ) (gen_pow φ) hm
  intro x hx
  apply degreeData_w_ne_zero φ hc
  apply hmoved
  rintro ⟨f, rfl⟩
  exact hx (hzero f)

/-- **Lemma 8.3.2 of Hone et al. for the modules `K[X] ⊗ Y`.**  If the elementary abelian group
has no fixed point on `X` (for instance `X = A/A'` with `A' < A` proper, when `K[X] ⊗ Y` is the
module induced from `A'`), then `K[X] ⊗ Y` is free over `K[z]/(z^p)` for generic `c`:
`ker z = range z^(p-1)`. -/
theorem ker_eq_range_pow_of_no_fixed_points {c : ι → K} (hc : Generic p c)
    (hmoved : ∀ x : X, ∃ v : ι → ZMod p, φ (ofAdd v) • x ≠ x) :
    LinearMap.ker (zOp (gen φ) c (twist (X := X) σ)) =
      LinearMap.range ((zOp (gen φ) c (twist (X := X) σ) : Module.End K (X →₀ Y)) ^ (p - 1)) := by
  apply le_antisymm
  · intro m hm
    exact nonfixed_free φ σ (fun e : Empty => e.elim) hc
      (fun x _ => hmoved x) (LinearMap.mem_ker.mp hm) (fun f => f.elim)
  · rintro _ ⟨m, rfl⟩
    have hpp : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', hpp,
      zOp_pow_char c (twist (X := X) σ) (gen_comm φ) (gen_pow φ), LinearMap.zero_apply]

end Acyclic

end DegreeProfilesReview.Shifted
