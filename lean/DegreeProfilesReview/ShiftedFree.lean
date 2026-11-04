/-
Stage 5, step 2: the non-fixed points contribute nothing to the shifted cyclic functor.

Setting: `char K = p`; `s : ι → Γ` pairwise commuting elements with `(s i)^p = 1`; `Γ` acts on
a set `X` and linearly on `Y`; `z = ∑ c i • (s i - 1)` acts on `M = (X →₀ Y) = K[X] ⊗ Y`.

A *degree datum* (`DegreeData`) consists of functions `π : X → K` and `e : ι → X → K` with

      `π (s i • x) = π x + e i x`,       `e i (s k • x) = e i x`.

Put `w x = ∑ i, c i * e i x`.

**Theorem (`mem_range_of_degreeData`).**  If `z m = 0` and `w x ≠ 0` wherever `m x ≠ 0`, then
`m ∈ range z`.

Proof.  Let `D`, `E i` be pointwise multiplication by `π`, `e i` and `S i` the action of `s i`.
Then `D S_i - S_i D = S_i E_i`, so `D z - z D = W := ∑ c i • S_i E_i`.  The operators `S_i, E_k`
commute pairwise and `S_i^p = 1`, so by the Frobenius identity `W^p = ∑ c_i^p E_i^p`, which is
multiplication by `w^p`.  If `z m = 0` then `W m = - z (D m)`, hence
`w^p · m = W^p m = - z (W^(p-1) D m)`; dividing by the invariant function `w^p` on the support
of `m` gives `m ∈ range z`.  ∎

**Theorem (`mem_range_pow_of_degreeData`).**  Under the same hypotheses `m ∈ range z^(p-1)`.
Proof: with `D' = w^(-p) W^(p-1) D` one has `D' z - z D' = 1` on the part where `w ≠ 0`, hence
`z^k D'^k m = (-1)^k k! m` for `m ∈ ker z`, and `(p-1)! ≠ 0` in `K`.  ∎

In representation-theoretic terms: the part of `K[X] ⊗ Y` over the points with `w ≠ 0` is free
over `K[z]/(z^p)` (`ker z = range z^(p-1)`; `z^p = 0` is `zOp_pow_char`).  This replaces the
citation of Evens, Prop. 8.2.4 behind Lemma 8.3.2 of Hone et al.  Everything here is proved;
there is no external hypothesis.
-/
import DegreeProfilesReview.ShiftedLinear
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Prime.Factorial

namespace DegreeProfilesReview.Shifted

open DegreeProfilesReview.Del

variable {K : Type*} [Field K] {Γ : Type*} [Group Γ] {ι : Type*} [Fintype ι]

/-! ### Pointwise multiplication by a function -/

section Scal

variable {X : Type*} {Y : Type*} [AddCommGroup Y] [Module K Y]

/-- Pointwise multiplication of `m : X →₀ Y` by a function `X → K`. -/
noncomputable def scal (f : X → K) : Module.End K (X →₀ Y) :=
  Finsupp.lsum K fun x => Finsupp.lsingle x ∘ₗ (f x • LinearMap.id)

theorem scal_single (f : X → K) (x : X) (y : Y) :
    scal f (Finsupp.single x y) = Finsupp.single x (f x • y) := by
  simp [scal]

theorem scal_apply (f : X → K) (m : X →₀ Y) (x : X) : (scal f m) x = f x • m x := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' => rw [map_add, Finsupp.add_apply, hm, hm', Finsupp.add_apply, smul_add]
  | single x' y =>
    rw [scal_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : x' = x
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg h, smul_zero]

theorem scal_mul (f g : X → K) : (scal f * scal g : Module.End K (X →₀ Y)) = scal (f * g) := by
  apply LinearMap.ext
  intro m
  ext x
  rw [Module.End.mul_apply, scal_apply, scal_apply, scal_apply, Pi.mul_apply, mul_smul]

theorem scal_pow (f : X → K) (n : ℕ) : (scal f : Module.End K (X →₀ Y)) ^ n = scal (f ^ n) := by
  induction n with
  | zero =>
    apply LinearMap.ext
    intro m
    ext x
    rw [pow_zero, pow_zero, Module.End.one_apply, scal_apply, Pi.one_apply, one_smul]
  | succ n ih => rw [pow_succ, ih, scal_mul, pow_succ]

theorem scal_sum_smul (c : ι → K) (e : ι → X → K) :
    (∑ i, c i • (scal (e i) : Module.End K (X →₀ Y))) = scal (fun x => ∑ i, c i * e i x) := by
  apply LinearMap.ext
  intro m
  ext x
  rw [LinearMap.sum_apply, Finsupp.finset_sum_apply, scal_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.smul_apply, Finsupp.smul_apply, scal_apply, mul_smul]

theorem scal_commute (f g : X → K) : Commute (scal f : Module.End K (X →₀ Y)) (scal g) := by
  show scal f * scal g = scal g * scal f
  rw [scal_mul, scal_mul, mul_comm]

/-- If `f = 1` on the support of `m` then `scal f m = m`. -/
theorem scal_eq_self {f : X → K} {m : X →₀ Y} (h : ∀ x, m x ≠ 0 → f x = 1) : scal f m = m := by
  ext x
  rw [scal_apply]
  by_cases hx : m x = 0
  · rw [hx, smul_zero]
  · rw [h x hx, one_smul]

end Scal

/-! ### The commutation relations -/

section Relations

variable {X : Type*} [MulAction Γ X] {Y : Type*} [AddCommGroup Y] [Module K Y]
  (σ : Representation K Γ Y)

/-- `scal g ∘ γ = γ ∘ scal (g ∘ γ)`. -/
theorem scal_mul_twist (g : X → K) (γ : Γ) :
    (scal g * twist (X := X) σ γ : Module.End K (X →₀ Y)) =
      twist (X := X) σ γ * scal (fun x => g (γ • x)) := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    Module.End.mul_apply, twist_single, scal_single, scal_single, twist_single, map_smul]

/-- An invariant function commutes with the group element. -/
theorem scal_commute_twist {g : X → K} {γ : Γ} (hg : ∀ x, g (γ • x) = g x) :
    Commute (scal g : Module.End K (X →₀ Y)) (twist (X := X) σ γ) := by
  show scal g * twist (X := X) σ γ = twist (X := X) σ γ * scal g
  rw [scal_mul_twist]
  congr 2
  funext x
  exact hg x

theorem twist_commute {γ γ' : Γ} (h : γ * γ' = γ' * γ) :
    Commute (twist (X := X) σ γ) (twist (X := X) σ γ') := by
  show twist (X := X) σ γ * twist (X := X) σ γ' = twist (X := X) σ γ' * twist (X := X) σ γ
  rw [← map_mul, ← map_mul, h]

end Relations

/-! ### Degree data and the theorem -/

/-- Functions `π`, `e i` on `X` with `π (s i • x) = π x + e i x` and `e i` invariant. -/
structure DegreeData (K : Type*) [Field K] {Γ : Type*} [Group Γ] {ι : Type*} (s : ι → Γ)
    (X : Type*) [MulAction Γ X] where
  π : X → K
  e : ι → X → K
  π_smul : ∀ i x, π (s i • x) = π x + e i x
  e_smul : ∀ i k x, e i (s k • x) = e i x

section Main

variable {s : ι → Γ} (c : ι → K) {X : Type*} [MulAction Γ X] {Y : Type*} [AddCommGroup Y]
  [Module K Y] (σ : Representation K Γ Y) (dd : DegreeData K s X)

/-- `w x = ∑ i, c i * e i x`. -/
def DegreeData.w (x : X) : K := ∑ i, c i * dd.e i x

theorem DegreeData.w_smul (k : ι) (x : X) : dd.w c (s k • x) = dd.w c x := by
  unfold DegreeData.w
  apply Finset.sum_congr rfl
  intro i _
  rw [dd.e_smul]

/-- `W = ∑ c i • S_i E_i`. -/
noncomputable def DegreeData.W : Module.End K (X →₀ Y) :=
  ∑ i, c i • (twist (X := X) σ (s i) * scal (dd.e i))

/-- `z` as an element of the endomorphism ring. -/
theorem zOp_eq_sum :
    (zOp s c (twist (X := X) σ) : Module.End K (X →₀ Y)) =
      ∑ i, c i • (twist (X := X) σ (s i) - 1) := rfl

omit [Fintype ι] in
/-- `D S_i = S_i D + S_i E_i`. -/
theorem DegreeData.scal_π_mul_twist (i : ι) :
    (scal dd.π * twist (X := X) σ (s i) : Module.End K (X →₀ Y)) =
      twist (X := X) σ (s i) * scal dd.π + twist (X := X) σ (s i) * scal (dd.e i) := by
  rw [scal_mul_twist, ← mul_add]
  congr 1
  apply LinearMap.ext
  intro m
  ext x
  rw [LinearMap.add_apply, Finsupp.add_apply, scal_apply, scal_apply, scal_apply, dd.π_smul,
    add_smul]

/-- `D z - z D = W`. -/
theorem DegreeData.commutator :
    (scal dd.π * zOp s c (twist (X := X) σ) - zOp s c (twist (X := X) σ) * scal dd.π :
      Module.End K (X →₀ Y)) = dd.W c σ := by
  rw [zOp_eq_sum, DegreeData.W, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : (scal dd.π * (twist (X := X) σ (s i) - 1) - (twist (X := X) σ (s i) - 1) * scal dd.π :
      Module.End K (X →₀ Y)) = twist (X := X) σ (s i) * scal (dd.e i) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, dd.scal_π_mul_twist σ i]
    abel
  rw [mul_smul_comm, smul_mul_assoc, ← h, smul_sub]

variable (hs : ∀ i k, s i * s k = s k * s i)

omit [Fintype ι] in
include hs in
theorem DegreeData.SE_commute (i k : ι) :
    Commute (twist (X := X) σ (s i) * scal (dd.e i) : Module.End K (X →₀ Y))
      (twist (X := X) σ (s k) * scal (dd.e k)) := by
  apply Commute.mul_left
  · apply Commute.mul_right
    · exact twist_commute σ (hs i k)
    · exact (scal_commute_twist σ (fun x => dd.e_smul k i x)).symm
  · apply Commute.mul_right
    · exact scal_commute_twist σ (fun x => dd.e_smul i k x)
    · exact scal_commute _ _

include hs in
/-- `W` commutes with `z`. -/
theorem DegreeData.W_commute_zOp :
    Commute (dd.W c σ) (zOp s c (twist (X := X) σ) : Module.End K (X →₀ Y)) := by
  rw [zOp_eq_sum, DegreeData.W]
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro k _
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sub_right _ (Commute.one_right _)
  apply Commute.mul_left
  · exact twist_commute σ (hs i k)
  · exact scal_commute_twist σ (fun x => dd.e_smul i k x)

/-- An invariant function commutes with `z`. -/
theorem scal_commute_zOp {g : X → K} (hg : ∀ k x, g (s k • x) = g x) :
    Commute (scal g : Module.End K (X →₀ Y)) (zOp s c (twist (X := X) σ)) := by
  rw [zOp_eq_sum]
  apply Commute.sum_right
  intro k _
  apply Commute.smul_right
  apply Commute.sub_right _ (Commute.one_right _)
  exact scal_commute_twist σ (hg k)

variable {p : ℕ} [Fact p.Prime] [CharP K p] (hp : ∀ i, s i ^ p = 1)

/-- Frobenius for a finite commuting family in a ring of characteristic `p`. -/
theorem sum_pow_char_of_commute {R : Type*} [Ring R] [CharP R p] {κ : Type*} (t : Finset κ)
    (T : κ → R) (hT : ∀ i ∈ t, ∀ k ∈ t, Commute (T i) (T k)) :
    (∑ i ∈ t, T i) ^ p = ∑ i ∈ t, T i ^ p := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (Fact.out : p.Prime).ne_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char_of_commute, ih]
    · intro i hi k hk
      exact hT i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk)
    · apply Commute.sum_right
      intro k hk
      exact hT a (Finset.mem_insert_self a t) k (Finset.mem_insert_of_mem hk)

include hs hp in
/-- `W^p` is multiplication by `w^p`. -/
theorem DegreeData.W_pow [Nontrivial (X →₀ Y)] : dd.W c σ ^ p = scal (dd.w c ^ p) := by
  haveI : CharP (Module.End K (X →₀ Y)) p :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K (X →₀ Y))).injective p
  rw [DegreeData.W, sum_pow_char_of_commute]
  · have h1 : ∀ i, (c i • (twist (X := X) σ (s i) * scal (dd.e i)) :
        Module.End K (X →₀ Y)) ^ p = c i ^ p • scal (dd.e i ^ p) := by
      intro i
      rw [smul_pow, ((scal_commute_twist σ (fun x => dd.e_smul i i x)).symm).mul_pow, ← map_pow,
        hp i, map_one, one_mul, scal_pow]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), scal_sum_smul]
    congr 1
    funext x
    rw [Pi.pow_apply, DegreeData.w, sum_pow_char]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Pi.pow_apply]
  · intro i _ k _
    apply Commute.smul_left
    apply Commute.smul_right
    exact dd.SE_commute σ hs i k

include hs hp in
/-- **The part over the points with `w ≠ 0` is acyclic for `z`.** -/
theorem mem_range_of_degreeData {m : X →₀ Y} (hm : zOp s c (twist (X := X) σ) m = 0)
    (hw : ∀ x, m x ≠ 0 → dd.w c x ≠ 0) :
    m ∈ LinearMap.range (zOp s c (twist (X := X) σ)) := by
  rcases subsingleton_or_nontrivial (X →₀ Y) with hsub | hnt
  · rw [Subsingleton.elim m 0]
    exact Submodule.zero_mem _
  set z : Module.End K (X →₀ Y) := zOp s c (twist (X := X) σ) with hz
  -- `W m = - z (D m)`
  have h1 : dd.W c σ m = -(z (scal dd.π m)) := by
    rw [← dd.commutator c σ, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      ← hz, hm, map_zero, zero_sub]
  -- `w^p m = - z (W^(p-1) D m)`
  have h2 : scal (dd.w c ^ p) m = -(z ((dd.W c σ ^ (p - 1)) (scal dd.π m))) := by
    have hpp : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos).symm
    rw [← dd.W_pow c σ hs hp]
    conv_lhs => rw [hpp, pow_succ, Module.End.mul_apply, h1, map_neg]
    congr 1
    have hc : Commute (dd.W c σ ^ (p - 1)) z := (dd.W_commute_zOp c σ hs).pow_left _
    exact LinearMap.congr_fun hc.eq (scal dd.π m)
  -- divide by `w^p`
  set g : X → K := fun x => (dd.w c x ^ p)⁻¹ with hg
  have hginv : ∀ k x, g (s k • x) = g x := fun k x => by
    rw [hg]
    simp only
    rw [dd.w_smul]
  have h3 : scal g (scal (dd.w c ^ p) m) = m := by
    rw [← Module.End.mul_apply, scal_mul]
    apply scal_eq_self
    intro x hx
    rw [Pi.mul_apply, Pi.pow_apply, hg]
    exact inv_mul_cancel₀ (pow_ne_zero _ (hw x hx))
  refine ⟨-(scal g ((dd.W c σ ^ (p - 1)) (scal dd.π m))), ?_⟩
  rw [map_neg]
  have hc : Commute (scal g : Module.End K (X →₀ Y)) z := scal_commute_zOp c σ hginv
  have h4 := LinearMap.congr_fun hc.eq ((dd.W c σ ^ (p - 1)) (scal dd.π m))
  rw [Module.End.mul_apply, Module.End.mul_apply] at h4
  rw [← h4, ← map_neg, ← h2, h3]

/-! ### Freeness: `ker z ⊆ range z^(p-1)` -/

/-- In a ring, if `D z - z D = E` with `E` commuting with `z` and `D`, then
`z D^(k+1) = D^(k+1) z - (k+1) D^k E`. -/
theorem mul_pow_of_commutator {R : Type*} [Ring R] {z D E : R} (h : D * z - z * D = E)
    (hED : Commute E D) (k : ℕ) :
    z * D ^ (k + 1) = D ^ (k + 1) * z - ((k + 1 : ℕ) : R) * (D ^ k * E) := by
  have hzD : z * D = D * z - E := by
    rw [← h]
    abel
  induction k with
  | zero => rw [zero_add, pow_one, pow_zero, Nat.cast_one, one_mul, one_mul, hzD]
  | succ k ih =>
    have h1 : z * D ^ (k + 1 + 1) = (z * D ^ (k + 1)) * D := by rw [pow_succ D (k + 1), mul_assoc]
    have h2 : D ^ k * E * D = D ^ (k + 1) * E := by
      rw [mul_assoc, hED.eq, ← mul_assoc, ← pow_succ]
    have h3 : D ^ (k + 1) * z * D = D ^ (k + 1 + 1) * z - D ^ (k + 1) * E := by
      rw [mul_assoc, hzD, mul_sub, ← mul_assoc, ← pow_succ]
    rw [h1, ih, sub_mul, mul_assoc ((k + 1 : ℕ) : R), h2, h3, Nat.cast_succ (k + 1), add_mul,
      one_mul]
    abel

/-- If `D z - z D = E`, `E` commutes with `D`, `z m = 0` and `E m = m`, then
`z^k D^k m = (-1)^k k! m`. -/
theorem pow_pow_apply_of_commutator {M : Type*} [AddCommGroup M] [Module K M]
    {z D E : Module.End K M} (h : D * z - z * D = E) (hED : Commute E D) {m : M}
    (hz : z m = 0) (hE : E m = m) (k : ℕ) :
    (z ^ k) ((D ^ k) m) = ((-1 : K) ^ k * (k.factorial : K)) • m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : z ((D ^ (k + 1)) m) = -(((k + 1 : ℕ) : K) • (D ^ k) m) := by
      have := LinearMap.congr_fun (mul_pow_of_commutator h hED k) m
      rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.mul_apply, hz, map_zero, zero_sub,
        Module.End.mul_apply, Module.End.mul_apply, hE, Module.End.natCast_apply] at this
      rw [this, Nat.cast_smul_eq_nsmul]
    rw [pow_succ z k, Module.End.mul_apply, h1, map_neg, map_smul, ih, Nat.factorial_succ,
      Nat.cast_mul, pow_succ, smul_smul, ← neg_smul]
    congr 1
    ring

include hs in
/-- An invariant function commutes with `W`. -/
theorem DegreeData.scal_commute_W {g : X → K} (hg : ∀ k x, g (s k • x) = g x) :
    Commute (scal g : Module.End K (X →₀ Y)) (dd.W c σ) := by
  have _ := hs
  rw [DegreeData.W]
  apply Commute.sum_right
  intro i _
  apply Commute.smul_right
  apply Commute.mul_right
  · exact scal_commute_twist σ (hg i)
  · exact scal_commute _ _

include hs hp in
/-- **The part over the points with `w ≠ 0` is free over `K[z]/(z^p)`**, in the form
`ker z ⊆ range z^(p-1)`.  (With `zOp_pow_char` this gives `ker z = range z^(p-1)` on that part.)
This is Lemma 8.3.2 of Hone et al. for the modules `K[X] ⊗ Y`, `X` without fixed points. -/
theorem mem_range_pow_of_degreeData {m : X →₀ Y} (hm : zOp s c (twist (X := X) σ) m = 0)
    (hw : ∀ x, m x ≠ 0 → dd.w c x ≠ 0) :
    m ∈ LinearMap.range ((zOp s c (twist (X := X) σ) : Module.End K (X →₀ Y)) ^ (p - 1)) := by
  rcases subsingleton_or_nontrivial (X →₀ Y) with hsub | hnt
  · rw [Subsingleton.elim m 0]
    exact Submodule.zero_mem _
  set z : Module.End K (X →₀ Y) := zOp s c (twist (X := X) σ) with hz
  set g : X → K := fun x => (dd.w c x ^ p)⁻¹ with hg
  have hginv : ∀ k x, g (s k • x) = g x := fun k x => by
    rw [hg]
    simp only
    rw [dd.w_smul]
  set ind : X → K := g * dd.w c ^ p with hind
  have hindinv : ∀ k x, ind (s k • x) = ind x := fun k x => by
    rw [hind, Pi.mul_apply, Pi.mul_apply, hginv, Pi.pow_apply, Pi.pow_apply, dd.w_smul]
  -- `V = G W^(p-1)`, `D' = V D`, `E = V W = multiplication by ind`
  set V : Module.End K (X →₀ Y) := scal g * dd.W c σ ^ (p - 1) with hV
  have hpp : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos
  have hVW : V * dd.W c σ = scal ind := by
    rw [hV, mul_assoc, ← pow_succ, hpp, dd.W_pow c σ hs hp, scal_mul]
  have hVz : Commute V z :=
    (scal_commute_zOp c σ hginv).mul_left ((dd.W_commute_zOp c σ hs).pow_left _)
  have hcomm : V * scal dd.π * z - z * (V * scal dd.π) = scal ind := by
    have h1 : z * (V * scal dd.π) = V * (z * scal dd.π) := by
      rw [← mul_assoc, ← hVz.eq, mul_assoc]
    rw [h1, mul_assoc, ← mul_sub, hz, dd.commutator c σ, hVW]
  have hED : Commute (scal ind : Module.End K (X →₀ Y)) (V * scal dd.π) := by
    apply Commute.mul_right
    · exact (scal_commute _ _).mul_right ((dd.scal_commute_W c σ hs hindinv).pow_right _)
    · exact scal_commute _ _
  have hEm : scal ind m = m := by
    apply scal_eq_self
    intro x hx
    rw [hind, Pi.mul_apply, Pi.pow_apply, hg]
    exact inv_mul_cancel₀ (pow_ne_zero _ (hw x hx))
  have key := pow_pow_apply_of_commutator hcomm hED hm hEm (p - 1)
  have hfac : ((-1 : K) ^ (p - 1) * ((p - 1).factorial : K)) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    have hpr : p.Prime := Fact.out
    rw [Ne, CharP.cast_eq_zero_iff K p, hpr.dvd_factorial]
    have := hpr.pos
    omega
  refine ⟨((-1 : K) ^ (p - 1) * ((p - 1).factorial : K))⁻¹ •
    ((V * scal dd.π : Module.End K (X →₀ Y)) ^ (p - 1)) m, ?_⟩
  rw [map_smul, key, smul_smul, inv_mul_cancel₀ hfac, one_smul]

end Main

/-! ### `z^p = 0` -/

section Nilpotent

variable {s : ι → Γ} (c : ι → K) {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : Representation K Γ V) {p : ℕ} [Fact p.Prime] [CharP K p]

/-- For pairwise commuting `s i` of order dividing `p`, in characteristic `p`: `z^p = 0`.  So `z`
generates a copy of `K[z]/(z^p)` (a shifted cyclic subgroup), and `ShiftedExactness.lean`
applies to every representation. -/
theorem zOp_pow_char (hs : ∀ i k, s i * s k = s k * s i) (hp : ∀ i, s i ^ p = 1) :
    (zOp s c ρ : Module.End K V) ^ p = 0 := by
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _
  haveI : CharP (Module.End K V) p :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K V)).injective p
  have hz : (zOp s c ρ : Module.End K V) = ∑ i, c i • (ρ (s i) - 1) := rfl
  have hcomm : ∀ i k, Commute (ρ (s i)) (ρ (s k)) := fun i k => by
    show ρ (s i) * ρ (s k) = ρ (s k) * ρ (s i)
    rw [← map_mul, ← map_mul, hs i k]
  rw [hz, sum_pow_char_of_commute]
  · apply Finset.sum_eq_zero
    intro i _
    rw [smul_pow, sub_pow_char_of_commute p (Commute.one_right _), one_pow, ← map_pow, hp i,
      map_one, sub_self, smul_zero]
  · intro i _ k _
    apply Commute.smul_left
    apply Commute.smul_right
    apply Commute.sub_left _ (Commute.one_left _)
    apply Commute.sub_right _ (Commute.one_right _)
    exact hcomm i k

end Nilpotent

end DegreeProfilesReview.Shifted
