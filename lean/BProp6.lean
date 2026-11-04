/-
Agent B, round 4: **Prop. 6 (pattern form), PROVED**, and Theorem A with DCP as the only input.

Setting: `N = n + p^a`, block `B = {n, …, N-1}`, `A = (ℤ/p)^a` acting regularly on `B`
(`blockφ`), `z = Σ c_i (σ_i - 1)` with `c` generic, `1 ≤ k ≤ b < p^a`.

Construction (simpler than the orbit route, same idea).  Let `A` act on SUBSETS of the labels.
Stage 5's `degreeData` gives `π : Finset (Fin N) → K`, `e_i` with `π (σ_i • X) = π X + e_i X`,
`e_i` invariant, and `w X = Σ c_i e_i X ≠ 0` whenever `X` is moved by `A` (genericity; the
functional defining `π` vanishes on the setwise stabiliser `A_X`, which is proper).  For a partial
tuple `t` put `deg t = π (img t)` (`img t` = set of labels used).  It is invariant under row
permutations.  The value `π X` lies in `𝔽_p`; write `degZ t ∈ ZMod p` for it.

  `V_d := {functions on k-patterns supported on deg = d}`.

* `V_0` is row-stable and graded by the pattern domain (both are support conditions).
* Injectivity of `(v_j)_{j<p} ↦ Σ z^j v_j` on `V_d`: with `D = (deg - d)·`, `[D, z] = W`,
  `W = Σ c_i e_i σ_i` commutes with `z` and `W^p = w^p·` is injective on patterns; applying `D` to
  `Σ z^j v_j = 0` gives `W (Σ j z^(j-1) v_j) = 0`, and induction (`j < p` invertible) (`vanish_of_comm`).
* Surjectivity for `d = 0` by counting: injectivity for EVERY `d` gives `p |X_d| ≤ |X|`, and
  `Σ_d |X_d| = |X|`, hence `p |X_0| = |X| = dim PatSp k`.

Main results: `prop6PatHyp_of_generic` (Prop6PatHyp for generic `c`, `b < p^a`),
`topWitnessHypothesis_of_dcp` (Theorem A, CONDITIONAL only on `DCPHyp`).
-/
import BProp6Red

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 ClaudeCP DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ConcreteM5
open scoped Pointwise

/-! ### An abstract vanishing lemma (the commutator trick) -/

section Abstract

variable {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M]

theorem comm_pow_apply (z D W : Module.End K M) (hDz : D * z - z * D = W) (hWz : W * z = z * W)
    {v : M} (hv : D v = 0) (j : ℕ) : D ((z ^ (j + 1)) v) = ((j : K) + 1) • W ((z ^ j) v) := by
  have hstep : ∀ x : M, D (z x) = z (D x) + W x := by
    intro x
    have h := congrArg (fun T : Module.End K M => T x) hDz
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← h]
    abel
  have hWz' : ∀ x : M, W (z x) = z (W x) := fun x => by
    rw [← Module.End.mul_apply, hWz, Module.End.mul_apply]
  induction j with
  | zero =>
    rw [zero_add, pow_one, hstep, hv, map_zero, zero_add]
    simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, hstep, ih, map_smul, ← hWz', pow_succ',
      Module.End.mul_apply]
    simp only [Nat.cast_succ, add_smul, one_smul]

theorem pow_mem_of_stable (z : Module.End K M) (S : Submodule K M) (hzS : ∀ x ∈ S, z x ∈ S)
    (j : ℕ) {x : M} (hx : x ∈ S) : (z ^ j) x ∈ S := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hzS _ ih

/-- **The commutator trick.**  If `[D, z] = W`, `[W, z] = 0`, `W` is injective on a `z`-stable
`S ⊇ V` and `D` kills `V`, then `Σ_{j<m} z^j v_j = 0` (`v_j ∈ V`, `m ≤ p`) forces all `v_j = 0`. -/
theorem vanish_of_comm (p : ℕ) [CharP K p] (z D W : Module.End K M) (hDz : D * z - z * D = W)
    (hWz : W * z = z * W) (S : Submodule K M) (hzS : ∀ x ∈ S, z x ∈ S)
    (hWS : ∀ x ∈ S, W x = 0 → x = 0) (V : Submodule K M) (hVS : V ≤ S)
    (hDV : ∀ v ∈ V, D v = 0) :
    ∀ m, m ≤ p → ∀ v : ℕ → M, (∀ j, v j ∈ V) → ∑ j ∈ range m, (z ^ j) (v j) = 0 →
      ∀ j < m, v j = 0 := by
  intro m
  induction m with
  | zero => intro _ _ _ _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro hm v hv hsum
    -- apply `D`
    have hD : W (∑ j ∈ range m, (z ^ j) (((j : K) + 1) • v (j + 1))) = 0 := by
      have h1 := congrArg D hsum
      rw [map_zero, Finset.sum_range_succ', map_add, map_sum, pow_zero, Module.End.one_apply,
        hDV _ (hv 0), add_zero] at h1
      rw [← h1, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [comm_pow_apply z D W hDz hWz (hDV _ (hv (j + 1))) j, map_smul, map_smul]
    have hS : ∑ j ∈ range m, (z ^ j) (((j : K) + 1) • v (j + 1)) ∈ S :=
      Submodule.sum_mem _ fun j _ =>
        pow_mem_of_stable z S hzS j (hVS (V.smul_mem _ (hv (j + 1))))
    have h0 := hWS _ hS hD
    have hih := ih (by omega) (fun j => ((j : K) + 1) • v (j + 1))
      (fun j => V.smul_mem _ (hv (j + 1))) h0
    have hsucc : ∀ j < m, v (j + 1) = 0 := by
      intro j hj
      have h := hih j hj
      have hne : ((j : K) + 1) ≠ 0 := by
        have : ((j + 1 : ℕ) : K) ≠ 0 := by
          rw [Ne, CharP.cast_eq_zero_iff K p]
          intro hdvd
          have := Nat.le_of_dvd (Nat.succ_pos j) hdvd
          omega
        simpa using this
      exact (smul_eq_zero.mp h).resolve_left hne
    intro j hj
    rcases j with _ | j
    · rw [Finset.sum_range_succ'] at hsum
      rw [Finset.sum_eq_zero (fun i hi => by
        rw [hsucc i (Finset.mem_range.mp hi), map_zero]), zero_add, pow_zero,
        Module.End.one_apply] at hsum
      exact hsum
    · exact hsucc j (by omega)

end Abstract

/-! ### Functions supported on a set -/

section Supp

variable {K : Type} [Field K] {T : Type} [Fintype T] [DecidableEq T]

/-- Functions supported on `{t | P t}`. -/
def suppSp (P : T → Prop) : Submodule K (T → K) where
  carrier := {f | ∀ t, f t ≠ 0 → P t}
  add_mem' {f g} hf hg t h := by
    by_cases h1 : f t = 0
    · exact hg t (by simpa [h1] using h)
    · exact hf t h1
  zero_mem' t h := absurd rfl h
  smul_mem' c f hf t h := hf t (by
    intro h0
    apply h
    show c * f t = 0
    rw [h0, mul_zero])

/-- Restriction to the support set is a linear equivalence. -/
noncomputable def suppEquiv (P : T → Prop) [DecidablePred P] :
    suppSp (K := K) P ≃ₗ[K] ({t // P t} → K) where
  toFun f s := (f : T → K) s.1
  invFun g := ⟨fun t => if h : P t then g ⟨t, h⟩ else 0, fun t ht => by
    by_contra h
    exact ht (dif_neg h)⟩
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by
    apply Subtype.ext
    funext t
    simp only
    split_ifs with h
    · rfl
    · by_contra h'
      exact h (f.2 t (Ne.symm h'))
  right_inv g := by
    funext s
    simp [s.2]

theorem finrank_suppSp (P : T → Prop) [DecidablePred P] :
    Module.finrank K (suppSp (K := K) P) = (univ.filter P).card := by
  rw [(suppEquiv P).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]

end Supp

/-! ### The image set of a tuple -/

section Img

variable {b N : ℕ}

/-- The set of labels used by a partial tuple. -/
def img (t : Fin b → Option (Fin N)) : Finset (Fin N) := univ.filter (fun x => ∃ i, t i = some x)

theorem mem_img {t : Fin b → Option (Fin N)} {x : Fin N} : x ∈ img t ↔ ∃ i, t i = some x := by
  simp [img]

theorem img_map (g : Equiv.Perm (Fin N)) (t : Fin b → Option (Fin N)) :
    img (fun i => (t i).map g) = g • img t := by
  ext x
  rw [mem_img, Finset.mem_smul_finset]
  constructor
  · rintro ⟨i, hi⟩
    cases hti : t i with
    | none => rw [hti] at hi; cases hi
    | some y =>
      rw [hti, Option.map_some, Option.some.injEq] at hi
      exact ⟨y, mem_img.mpr ⟨i, hti⟩, hi⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi⟩ := mem_img.mp hy
    exact ⟨i, by rw [hi]; rfl⟩

theorem img_comp (σ : Equiv.Perm (Fin b)) (t : Fin b → Option (Fin N)) : img (t ∘ σ) = img t := by
  ext x
  rw [mem_img, mem_img]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨σ.symm i, by simpa using hi⟩

theorem img_subset_of_isPat {B : Finset (Fin N)} {k : ℕ} {t : Fin b → Option (Fin N)}
    (h : IsPat B k t) : img t ⊆ B := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_img.mp hx
  exact h.1 i x hi

theorem card_img_le (t : Fin b → Option (Fin N)) : (img t).card ≤ (patDom t).card := by
  classical
  rcases (img t).eq_empty_or_nonempty with h | ⟨x0, _⟩
  · rw [h, Finset.card_empty]
    exact Nat.zero_le _
  · apply Finset.card_le_card_of_surjOn (fun i => (t i).getD x0)
    intro x hx
    obtain ⟨i, hi⟩ := mem_img.mp hx
    refine ⟨i, ?_, ?_⟩
    · show i ∈ patDom t
      rw [mem_patDom, hi]
      simp
    · show (t i).getD x0 = x
      rw [hi]
      rfl

theorem img_nonempty_of_isPat {B : Finset (Fin N)} {k : ℕ} {t : Fin b → Option (Fin N)}
    (h : IsPat B k t) (hk : 1 ≤ k) : (img t).Nonempty := by
  have : (patDom t).Nonempty := by
    rw [← Finset.card_pos, h.2.2]
    omega
  obtain ⟨i, hi⟩ := this
  rw [mem_patDom] at hi
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hi
  exact ⟨x, mem_img.mpr ⟨i, hx⟩⟩

end Img

/-! ### Multiplication operators and the label-action monoid hom -/

section Ops

variable {K : Type} [Field K] {b N : ℕ}

/-- Pointwise multiplication by a function of the tuple. -/
def mulF (h : (Fin b → Option (Fin N)) → K) : Module.End K (Fn K (Fin b) (Fin N)) where
  toFun f t := h t * f t
  map_add' f g := by funext t; simp [mul_add]
  map_smul' c f := by funext t; simp [mul_left_comm]

theorem mulF_apply (h : (Fin b → Option (Fin N)) → K) (f : Fn K (Fin b) (Fin N))
    (t : Fin b → Option (Fin N)) : mulF h f t = h t * f t := rfl

theorem mulF_mul (h h' : (Fin b → Option (Fin N)) → K) :
    (mulF h * mulF h' : Module.End K (Fn K (Fin b) (Fin N))) = mulF (h * h') := by
  apply LinearMap.ext
  intro f
  funext t
  simp [mulF_apply, mul_assoc]

theorem mulF_pow (h : (Fin b → Option (Fin N)) → K) (m : ℕ) :
    (mulF h : Module.End K (Fn K (Fin b) (Fin N))) ^ m = mulF (h ^ m) := by
  induction m with
  | zero =>
    apply LinearMap.ext
    intro f
    funext t
    simp [mulF_apply]
  | succ m ih => rw [pow_succ, ih, mulF_mul, pow_succ]

theorem mulF_add (h h' : (Fin b → Option (Fin N)) → K) :
    (mulF h + mulF h' : Module.End K (Fn K (Fin b) (Fin N))) = mulF (h + h') := by
  apply LinearMap.ext
  intro f
  funext t
  simp [mulF_apply, add_mul]

theorem mulF_smul (c : K) (h : (Fin b → Option (Fin N)) → K) :
    (c • mulF h : Module.End K (Fn K (Fin b) (Fin N))) = mulF (c • h) := by
  apply LinearMap.ext
  intro f
  funext t
  simp [mulF_apply, mul_assoc]

theorem mulF_sum {κ : Type} (s : Finset κ) (h : κ → (Fin b → Option (Fin N)) → K) :
    (∑ i ∈ s, mulF (h i) : Module.End K (Fn K (Fin b) (Fin N))) = mulF (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply LinearMap.ext
    intro f
    funext t
    simp [mulF_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, mulF_add]

/-- `labAct` as a monoid hom. -/
def labMon : Equiv.Perm (Fin N) →* Module.End K (Fn K (Fin b) (Fin N)) where
  toFun g := labAct g
  map_one' := labAct_one
  map_mul' g h := labAct_mul g h

/-- `labAct g` commutes with multiplication by a `g`-invariant function. -/
theorem labAct_mulF (g : Equiv.Perm (Fin N)) (h : (Fin b → Option (Fin N)) → K)
    (hh : ∀ t, h (fun i => (t i).map g.symm) = h t) :
    (labAct g * mulF h : Module.End K (Fn K (Fin b) (Fin N))) = mulF h * labAct g := by
  apply LinearMap.ext
  intro f
  funext t
  simp only [Module.End.mul_apply, labAct_apply, mulF_apply, hh]

end Ops

/-! ### The concrete degree -/

section Degree

variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [CharP K p] {a n b : ℕ}

/-- `S_N → Perm (Fin N)` as a monoid hom. -/
def finPermHom (N : ℕ) : Sfin N →* Equiv.Perm (Fin N) where
  toFun := finPerm
  map_one' := finPerm_one
  map_mul' := finPerm_mul

/-- The block group acting on `Fin N`. -/
noncomputable def φB (a n : ℕ) : ElemAb p a →* Equiv.Perm (Fin (n + p ^ a)) :=
  (finPermHom (n + p ^ a)).comp (blockφ p a n)

theorem gen_φB (i : Fin a) : gen (φB p a n) i = finPerm (σgen p a n i) := rfl

/-- The degree data on subsets (Stage 5). -/
noncomputable abbrev ddB (K : Type) [Field K] [CharP K p] (a n : ℕ) :
    DegreeData K (gen (φB p a n)) (Finset (Fin (n + p ^ a))) :=
  degreeData (φB p a n) K

/-- The degree of a tuple, in `ZMod p`. -/
noncomputable def degZ (t : Fin b → Option (Fin (n + p ^ a))) : ZMod p :=
  fnl (φB p a n) (img t) (shift (φB p a n) (img t))

theorem ddB_π (X : Finset (Fin (n + p ^ a))) :
    (ddB p K a n).π X = ZMod.castHom (dvd_refl p) K (fnl (φB p a n) X (shift (φB p a n) X)) := rfl

theorem ddB_π_img (t : Fin b → Option (Fin (n + p ^ a))) :
    (ddB p K a n).π (img t) = ZMod.castHom (dvd_refl p) K (degZ p t) := rfl

theorem degZ_comp (σ : Equiv.Perm (Fin b)) (t : Fin b → Option (Fin (n + p ^ a))) :
    degZ p (t ∘ σ) = degZ p t := by
  unfold degZ
  rw [img_comp]

theorem π_inv_smul (i : Fin a) (X : Finset (Fin (n + p ^ a))) :
    (ddB p K a n).π ((gen (φB p a n) i)⁻¹ • X) = (ddB p K a n).π X - (ddB p K a n).e i X := by
  have h1 := (ddB p K a n).π_smul i ((gen (φB p a n) i)⁻¹ • X)
  have h2 := (ddB p K a n).e_smul i i ((gen (φB p a n) i)⁻¹ • X)
  rw [smul_inv_smul] at h1 h2
  rw [h1, ← h2]
  ring

theorem e_inv_smul (i k : Fin a) (X : Finset (Fin (n + p ^ a))) :
    (ddB p K a n).e i ((gen (φB p a n) k)⁻¹ • X) = (ddB p K a n).e i X := by
  have h2 := (ddB p K a n).e_smul i k ((gen (φB p a n) k)⁻¹ • X)
  rw [smul_inv_smul] at h2
  exact h2.symm

theorem img_labAct (g : Equiv.Perm (Fin (n + p ^ a))) (t : Fin b → Option (Fin (n + p ^ a))) :
    img (fun i => (t i).map g.symm) = g⁻¹ • img t := by
  rw [img_map]
  rfl

/-- Block labels. -/
theorem card_Bk : (Bk n (n + p ^ a)).card = p ^ a := by
  have : Bk n (n + p ^ a) = (univ : Finset (Fin (p ^ a))).map (Fin.natAddEmb n) := by
    ext x
    simp only [Bk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.natAddEmb_apply]
    constructor
    · intro hx
      refine ⟨⟨x.val - n, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [Fin.natAdd, Fin.val_mk]
      omega
    · rintro ⟨y, rfl⟩
      simp [Fin.natAdd]
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- A nonempty proper subset of the block is moved by `A`. -/
theorem moved_of_subset {X : Finset (Fin (n + p ^ a))} (hX : X ⊆ Bk n (n + p ^ a))
    (hne : X.Nonempty) (hlt : X.card < p ^ a) :
    ∃ v : Fin a → ZMod p, φB p a n (Multiplicative.ofAdd v) • X ≠ X := by
  obtain ⟨x, hx⟩ := hne
  have hlt' : X.card < (Bk n (n + p ^ a)).card := by rw [card_Bk]; exact hlt
  obtain ⟨y, hy, hyX⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
  have hxB := hX hx
  simp only [Bk, Finset.mem_filter, Finset.mem_univ, true_and] at hxB hy
  obtain ⟨g, hg, hgxy⟩ := (elemAbBlock p a n).trans x.val y.val hxB x.2 hy y.2
  obtain ⟨v, hv⟩ := exists_of_mem p a n hg
  refine ⟨Multiplicative.toAdd v, fun h => hyX ?_⟩
  rw [← h, Finset.mem_smul_finset]
  refine ⟨x, hx, ?_⟩
  apply Fin.ext
  show (finPerm (blockφ p a n v) x).val = y.val
  rw [finPerm_val, hv, hgxy]

end Degree

/-! ### The operators `D`, `W` and the commutator identity -/

section Main

variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [CharP K p] {a n b : ℕ} (c : Fin a → K)

/-- The generator `σ_i` acting on labels. -/
noncomputable abbrev Lg (i : Fin a) : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))) :=
  labAct (gen (φB p a n) i)

/-- `e_i` as a function of the tuple. -/
noncomputable def Ef (i : Fin a) (t : Fin b → Option (Fin (n + p ^ a))) : K :=
  (ddB p K a n).e i (img t)

/-- `deg - d` as a function of the tuple. -/
noncomputable def degF (d : ZMod p) (t : Fin b → Option (Fin (n + p ^ a))) : K :=
  (ddB p K a n).π (img t) - ZMod.castHom (dvd_refl p) K d

/-- `w` as a function of the tuple. -/
noncomputable def wF (t : Fin b → Option (Fin (n + p ^ a))) : K := (ddB p K a n).w c (img t)

/-- `W = Σ c_i e_i σ_i`. -/
noncomputable def Wop : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))) :=
  ∑ i, c i • (mulF (Ef p (K := K) i) * Lg p i)

theorem Z_eq' : rhoFn (ι := Fin b) (zEltP p a n c) = ∑ i, c i • (Lg p (K := K) i - 1) := by
  rw [Z_eq]
  rfl

theorem Ef_inv (i k : Fin a) (t : Fin b → Option (Fin (n + p ^ a))) :
    Ef p (K := K) i (fun j => (t j).map (gen (φB p a n) k).symm) = Ef p i t := by
  unfold Ef
  rw [img_labAct, e_inv_smul]

theorem commL (d : ZMod p) (i : Fin a) :
    (mulF (degF p (b := b) (K := K) d) * Lg p i - Lg p i * mulF (degF p d) :
      Module.End K (Fn K (Fin b) (Fin (n + p ^ a)))) = mulF (Ef p i) * Lg p i := by
  apply LinearMap.ext
  intro f
  funext t
  simp only [LinearMap.sub_apply, Module.End.mul_apply, labAct_apply, mulF_apply, Pi.sub_apply]
  unfold degF Ef
  rw [img_labAct, π_inv_smul]
  ring

theorem commZ (d : ZMod p) :
    (mulF (degF p (b := b) (K := K) d) * rhoFn (zEltP p a n c) -
      rhoFn (zEltP p a n c) * mulF (degF p d) :
      Module.End K (Fn K (Fin b) (Fin (n + p ^ a)))) = Wop p c := by
  rw [Z_eq', Wop, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  rw [show ∀ x y : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))), c i • x - c i • y = c i • (x - y)
    from fun x y => (smul_sub _ _ _).symm]
  congr 1
  rw [← commL p d i, mul_sub, sub_mul, mul_one, one_mul]
  abel

theorem Lg_comm (i k : Fin a) :
    Commute (Lg p (K := K) (b := b) (n := n) i) (Lg p k) := by
  show labAct _ * labAct _ = labAct _ * labAct _
  rw [← labAct_mul, ← labAct_mul, gen_comm]

theorem Lg_mulF_comm (i k : Fin a) :
    Commute (Lg p (K := K) (b := b) (n := n) k) (mulF (Ef p i)) :=
  labAct_mulF _ _ (fun t => Ef_inv p i k t)

theorem SE_comm (i k : Fin a) :
    Commute (mulF (Ef p (K := K) (b := b) (n := n) i) * Lg p i) (mulF (Ef p k) * Lg p k) := by
  apply Commute.mul_left
  · apply Commute.mul_right
    · exact (mulF_mul _ _).trans ((congrArg mulF (mul_comm _ _)).trans (mulF_mul _ _).symm)
    · exact (Lg_mulF_comm p i k).symm
  · apply Commute.mul_right
    · exact Lg_mulF_comm p k i
    · exact Lg_comm p i k

theorem W_comm_Z :
    (Wop p c * rhoFn (zEltP p a n c) : Module.End K (Fn K (Fin b) (Fin (n + p ^ a)))) =
      rhoFn (zEltP p a n c) * Wop p c := by
  rw [Z_eq']
  apply Commute.eq
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro k _
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sub_right _ (Commute.one_right _)
  apply Commute.mul_left
  · exact (Lg_mulF_comm p i k).symm
  · exact Lg_comm p i k

theorem Lg_pow (i : Fin a) : (Lg p (K := K) (b := b) (n := n) i) ^ p = 1 := by
  show (labMon (gen (φB p a n) i)) ^ p = 1
  rw [← map_pow, gen_pow, map_one]

/-- `W^p = w^p ·`. -/
theorem W_pow : (Wop p c : Module.End K (Fn K (Fin b) (Fin (n + p ^ a)))) ^ p =
    mulF (wF p c ^ p) := by
  haveI : CharP (Module.End K (Fn K (Fin b) (Fin (n + p ^ a)))) p :=
    charP_of_injective_algebraMap (algebraMap K _).injective p
  rw [Wop, sum_pow_char_of_commute (p := p)]
  · have h1 : ∀ i, (c i • (mulF (Ef p i) * Lg p i) :
        Module.End K (Fn K (Fin b) (Fin (n + p ^ a)))) ^ p = mulF (c i ^ p • Ef p i ^ p) := by
      intro i
      rw [smul_pow, (Lg_mulF_comm p i i).symm.mul_pow, Lg_pow, mul_one, mulF_pow, mulF_smul]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), mulF_sum]
    congr 1
    funext t
    rw [Finset.sum_apply, Pi.pow_apply, wF, DegreeData.w, sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Pi.pow_apply, smul_eq_mul, mul_pow]
    rfl
  · intro i _ k _
    apply Commute.smul_left
    apply Commute.smul_right
    exact SE_comm p i k

end Main

/-! ### Prop. 6: the complement `V_0` -/

section Prop6

variable {K : Type} [Field K]

theorem PatSp_eq_supp {b N : ℕ} (n k : ℕ) :
    (PatSp (b := b) (N := N) n k : Submodule K (Fn K (Fin b) (Fin N))) =
      suppSp (IsPat (Bk n N) k) := rfl

theorem isPat_of_map {b N n k : ℕ} {π : Equiv.Perm (Fin N)} (hπ : FixesLr n π)
    {t : Fin b → Option (Fin N)} (h : IsPat (Bk n N) k (fun i => (t i).map π.symm)) :
    IsPat (Bk n N) k t := by
  refine ⟨fun i x hx => ?_, fun i j x hi hj => ?_, ?_⟩
  · have h1 := h.1 i (π.symm x) (by show (t i).map π.symm = _; rw [hx]; rfl)
    have h2 := (hπ.mem_Bk_iff (π.symm x)).mpr h1
    rwa [Equiv.apply_symm_apply] at h2
  · exact h.2.1 i j (π.symm x) (by show (t i).map π.symm = _; rw [hi]; rfl)
      (by show (t j).map π.symm = _; rw [hj]; rfl)
  · have : patDom (fun i => (t i).map π.symm) = patDom t := by
      ext i
      simp [patDom]
    rw [← this]
    exact h.2.2

theorem PatSp_labAct_mem {b N n k : ℕ} {π : Equiv.Perm (Fin N)} (hπ : FixesLr n π)
    {F : Fn K (Fin b) (Fin N)} (hF : F ∈ PatSp (K := K) n k) : labAct π F ∈ PatSp (K := K) n k :=
  fun _ ht => isPat_of_map hπ (hF _ ht)

variable (p : ℕ) [Fact p.Prime] [CharP K p] {a n b : ℕ} (c : Fin a → K)

theorem Z_PatSp {k : ℕ} {F : Fn K (Fin b) (Fin (n + p ^ a))} (hF : F ∈ PatSp (K := K) n k) :
    rhoFn (zEltP p a n c) F ∈ PatSp (K := K) n k :=
  Z_mem p (PatSp n k) (fun _ hπ _ hF' => PatSp_labAct_mem hπ hF') hF

theorem wF_ne_zero (hc : Generic p c) {k : ℕ} (hk : 1 ≤ k) (hkq : k < p ^ a)
    {t : Fin b → Option (Fin (n + p ^ a))} (ht : IsPat (Bk n (n + p ^ a)) k t) :
    wF p c t ≠ 0 := by
  apply degreeData_w_ne_zero (φB p a n) hc
  apply moved_of_subset p (img_subset_of_isPat ht) (img_nonempty_of_isPat ht hk)
  calc (img t).card ≤ (patDom t).card := card_img_le t
    _ = k := ht.2.2
    _ < p ^ a := hkq

theorem W_inj (hc : Generic p c) {k : ℕ} (hk : 1 ≤ k) (hkq : k < p ^ a) :
    ∀ x ∈ PatSp (K := K) (b := b) (N := n + p ^ a) n k, Wop p (n := n) c x = 0 → x = 0 := by
  intro x hx hW
  have h : (Wop p c ^ p) x = mulF (wF p c ^ p) x := by rw [W_pow]
  have hWm : ∀ m, 1 ≤ m → (Wop p c ^ m) x = 0 := by
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply, hW, map_zero]
  have hWp : (Wop p c ^ p) x = 0 := hWm p (Fact.out : p.Prime).pos
  funext t
  by_contra hne
  have h2 := congrFun (h.symm.trans hWp) t
  rw [mulF_apply, Pi.pow_apply] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact wF_ne_zero p c hc hk hkq (hx t hne) (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h3)
  · exact hne h3

/-- Functions on `k`-patterns supported on `deg = d`. -/
noncomputable def Vd (k : ℕ) (d : ZMod p) : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))) :=
  suppSp (fun t => IsPat (Bk n (n + p ^ a)) k t ∧ degZ p t = d)

theorem Vd_le (k : ℕ) (d : ZMod p) : Vd p (K := K) (b := b) (n := n) (a := a) k d ≤ PatSp n k :=
  fun _ hf t ht => (hf t ht).1

theorem D_Vd (k : ℕ) (d : ZMod p) :
    ∀ v ∈ Vd p (K := K) (b := b) (n := n) (a := a) k d, mulF (degF p d) v = 0 := by
  intro v hv
  funext t
  rw [mulF_apply]
  by_cases h : v t = 0
  · rw [h, mul_zero]
    rfl
  · have hd := (hv t h).2
    rw [degF, ddB_π_img, hd, sub_self, zero_mul]
    rfl

theorem zSum_inj_Vd (hc : Generic p c) {k : ℕ} (hk : 1 ≤ k) (hkq : k < p ^ a) (d : ZMod p) :
    Function.Injective (zSum (p - 1 + 1) (rhoFn (zEltP p a n c))
      (Vd p (K := K) (b := b) (n := n) (a := a) k d)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have hvan := vanish_of_comm (M := Fn K (Fin b) (Fin (n + p ^ a))) p (rhoFn (zEltP p a n c))
    (mulF (degF p d)) (Wop p c)
    (commZ p c d) (W_comm_Z p c) (PatSp n k) (fun x hx => Z_PatSp p c hx) (W_inj p c hc hk hkq)
    (Vd p k d) (Vd_le p (b := b) k d) (D_Vd p (b := b) k d)
  let v : ℕ → Fn K (Fin b) (Fin (n + p ^ a)) := fun j =>
    if h : j < p - 1 + 1 then (u ⟨j, h⟩ : Fn K (Fin b) (Fin (n + p ^ a))) else 0
  have hv : ∀ j, v j ∈ Vd p (K := K) (b := b) (n := n) (a := a) k d := by
    intro j
    simp only [v]
    split_ifs
    · exact (u _).2
    · exact zero_mem _
  have hsum : ∑ j ∈ range (p - 1 + 1), (rhoFn (zEltP p a n c) ^ j) (v j) = 0 := by
    rw [← hu, zSum_apply, ← Fin.sum_univ_eq_sum_range (fun j => (rhoFn (zEltP p a n c) ^ j) (v j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [v, i.2]
  have hz := hvan (p - 1 + 1) (by have := (Fact.out : p.Prime).pos; omega) v hv hsum
  funext i
  apply Subtype.ext
  have h := hz i i.2
  simp only [v, dif_pos i.2] at h
  exact h

theorem range_le_PatSp {k : ℕ} (d : ZMod p) :
    LinearMap.range (zSum (p - 1 + 1) (rhoFn (zEltP p a n c))
      (Vd p (K := K) (b := b) (n := n) (a := a) k d)) ≤ PatSp n k := by
  rintro _ ⟨u, rfl⟩
  rw [zSum_apply]
  exact Submodule.sum_mem _ fun i _ =>
    pow_mem_of_stable _ _ (fun x hx => Z_PatSp p c hx) _ (Vd_le p k d (u i).2)

theorem finrank_zSum_dom (k : ℕ) (d : ZMod p) :
    Module.finrank K (Fin (p - 1 + 1) → Vd p (K := K) (b := b) (n := n) (a := a) k d) =
      p * (univ.filter (fun t : Fin b → Option (Fin (n + p ^ a)) =>
        IsPat (Bk n (n + p ^ a)) k t ∧ degZ p t = d)).card := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Vd, finrank_suppSp]
  congr 1
  have := (Fact.out : p.Prime).pos
  omega

theorem mul_card_le (hc : Generic p c) {k : ℕ} (hk : 1 ≤ k) (hkq : k < p ^ a) (d : ZMod p) :
    p * (univ.filter (fun t : Fin b → Option (Fin (n + p ^ a)) =>
        IsPat (Bk n (n + p ^ a)) k t ∧ degZ p t = d)).card ≤
      (univ.filter (IsPat (ι := Fin b) (Bk n (n + p ^ a)) k)).card := by
  have h1 := LinearMap.finrank_range_of_inj
    (zSum_inj_Vd p (K := K) (b := b) (n := n) c hc hk hkq d)
  have h2 := Submodule.finrank_mono (range_le_PatSp p (K := K) (b := b) (n := n) c (k := k) d)
  rw [h1, finrank_zSum_dom, PatSp_eq_supp, finrank_suppSp] at h2
  exact h2

theorem card_fibres (k : ℕ) :
    (univ.filter (IsPat (ι := Fin b) (Bk n (n + p ^ a)) k)).card =
      ∑ d : ZMod p, (univ.filter (fun t : Fin b → Option (Fin (n + p ^ a)) =>
        IsPat (Bk n (n + p ^ a)) k t ∧ degZ p t = d)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := degZ p) (t := univ) (fun _ _ => Finset.mem_coe.mpr
    (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.filter_filter]

theorem count_fibres {q S : ℕ} (hq : 0 < q) [NeZero q] (f : ZMod q → ℕ) (hsum : ∑ d, f d = S)
    (hle : ∀ d, q * f d ≤ S) : q * f 0 = S := by
  have h1 : ∑ d, q * f d = q * S := by rw [← Finset.mul_sum, hsum]
  have h2 : ∑ d, q * f d = q * f 0 + ∑ d ∈ univ.erase 0, q * f d :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have h3 : ∑ d ∈ univ.erase 0, q * f d ≤ ∑ d ∈ univ.erase (0 : ZMod q), S :=
    Finset.sum_le_sum fun d _ => hle d
  have h4 : ∑ d ∈ univ.erase (0 : ZMod q), S = (q - 1) * S := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card, smul_eq_mul]
  have h5 : (q - 1) * S + S = q * S := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h6 := hle 0
  omega

/-- **Prop. 6, pattern form — PROVED** (generic `c`, `b < p^a`). -/
theorem prop6PatHyp_of_generic (hc : Generic p c) (hb : b < p ^ a) :
    Prop6PatHyp p (K := K) (n := n) c b := by
  intro k hk hkb
  have hkq : k < p ^ a := lt_of_le_of_lt hkb hb
  refine ⟨Vd p k 0, ?_, ?_, ?_, zSum_inj_Vd p c hc hk hkq 0⟩
  · intro σ v hv t ht
    rw [rowAct_apply] at ht
    obtain ⟨h1, h2⟩ := hv _ ht
    refine ⟨?_, ?_⟩
    · have h3 := isPat_comp σ h1
      have h4 : (t ∘ σ) ∘ σ.symm = t := by
        funext i
        simp
      rwa [h4] at h3
    · rwa [degZ_comp] at h2
  · intro D v hv t ht
    rw [resD_apply] at ht
    split_ifs at ht with hD
    · exact hv t ht
    · exact absurd rfl ht
  · apply Submodule.eq_of_le_of_finrank_eq (range_le_PatSp p c 0)
    rw [LinearMap.finrank_range_of_inj (zSum_inj_Vd p c hc hk hkq 0), finrank_zSum_dom,
      PatSp_eq_supp, finrank_suppSp]
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    exact count_fibres (Fact.out : p.Prime).pos _ (card_fibres p k).symm
      (fun d => mul_card_le p c hc hk hkq d)

end Prop6

/-! ### Theorem A with DCP as the only hypothesis -/

section TheoremA

variable (p : ℕ) [Fact p.Prime]

/-- **Theorem A, conditional ONLY on DCP_b** (Prop. 8 / Bowman–Doty–Martin). -/
theorem topWitnessHypothesis_of_dcp (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ r a n : ℕ, r < p ^ a → 2 * r - 1 ≤ n → ∀ b, 1 ≤ b → b ≤ r →
      DCPHyp (K := L) b (n + p ^ a)) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  topWitnessHypothesis_of_prop6Pat_dcp p L fun r a n hr hn c hc b hb hbr =>
    ⟨prop6PatHyp_of_generic p c hc (lt_of_le_of_lt hbr hr), H r a n hr hn b hb hbr⟩

/-- The same with DCP stated for all `N ≥ 2b + 1` (all that Theorem A uses). -/
theorem topWitnessHypothesis_of_dcp' (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ b N : ℕ, 1 ≤ b → 2 * b + 1 ≤ N → DCPHyp (K := L) b N) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  topWitnessHypothesis_of_dcp p L fun r a n hr hn b hb hbr => H b (n + p ^ a) hb (by omega)

end TheoremA

end BExact
