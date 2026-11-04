/-
Stage 2, step 5a: the basis systems and relabelling-invariant matrices of a uniform template,
and the identification of their rank-`t` realisations with the ACTUAL linear maps between
polynomial spaces at universe size `t`.

For a template `T`, a degree `d` and a universe size `t` (variables `σ = T.Var.Rk t`):

| system                        | rank-`t` basis of                       | support |
|-------------------------------|-----------------------------------------|---------|
| `Var.mon d`                   | `W = P_{≤ d}`                           | `k d`   |
| `Var.mon (d-1)`               | `L = P_{≤ d-1}`                         | `k(d-1)`|
| `Var.prod (Var.mon (d-1))`    | `X ⊗ L`                                 | `k d`   |
| `unit`                        | `K`                                     | `0`     |
| `axSys d`                     | axioms of degree `≤ d`                  | `s`     |
| `certSys d`                   | NS certificates `(μ, i)`, total `≤ d`   | `kd + s`|

and five invariant matrices into `Var.mon d`: inclusion, multiplication, axiom coefficients,
the constant `1`, and the NS certificate map.  For each, the theorem `…_realise` states that
the matrix realised at rank `t`, read in the monomial basis, is the corresponding actual map.
Everything in this file is proved; there is no external hypothesis.
-/
import DegreeProfilesReview.Templates
import DegreeProfilesReview.ConcreteDatum
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.Pi

open MvPolynomial TensorProduct

namespace DegreeProfilesReview.Uniform

open BasisSystem DegreeProfilesReview.PC DegreeProfilesReview.Concrete

/-! ### Monomial exponents under an injective change of variables -/

section MapDomain

variable {α β : Type*} {f : α → β}

theorem mapDomain_apply_of_notMem_range (m : α →₀ ℕ) {b : β} (hb : b ∉ Set.range f) :
    Finsupp.mapDomain f m b = 0 :=
  Finsupp.mapDomain_notin_range m b hb

theorem mapDomain_le_iff (hf : Function.Injective f) (μ y : α →₀ ℕ) :
    Finsupp.mapDomain f μ ≤ Finsupp.mapDomain f y ↔ μ ≤ y := by
  constructor
  · intro h a
    have := h (f a)
    rwa [Finsupp.mapDomain_apply hf, Finsupp.mapDomain_apply hf] at this
  · intro h b
    by_cases hb : b ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hb
      rw [Finsupp.mapDomain_apply hf, Finsupp.mapDomain_apply hf]
      exact h a
    · rw [mapDomain_apply_of_notMem_range μ hb, mapDomain_apply_of_notMem_range y hb]

theorem mapDomain_tsub (hf : Function.Injective f) (y μ : α →₀ ℕ) :
    Finsupp.mapDomain f (y - μ) = Finsupp.mapDomain f y - Finsupp.mapDomain f μ := by
  ext b
  rw [Finsupp.tsub_apply]
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    rw [Finsupp.mapDomain_apply hf, Finsupp.mapDomain_apply hf, Finsupp.mapDomain_apply hf,
      Finsupp.tsub_apply]
  · rw [mapDomain_apply_of_notMem_range _ hb, mapDomain_apply_of_notMem_range _ hb,
      mapDomain_apply_of_notMem_range _ hb]

theorem mapDomain_eq_zero_iff (hf : Function.Injective f) (m : α →₀ ℕ) :
    Finsupp.mapDomain f m = 0 ↔ m = 0 := by
  constructor
  · intro h
    apply Finsupp.mapDomain_injective hf
    rw [h, Finsupp.mapDomain_zero]
  · rintro rfl
    exact Finsupp.mapDomain_zero

end MapDomain

/-! ### The monomial basis of `P_{≤ d}` -/

section MonBasis

variable (σ : Type) (K : Type) [Field K] (d : ℕ)

/-- The monomial basis of `P_{≤ d}`, as a linear equivalence `K[monomials of degree ≤ d] ≃ P_{≤d}`. -/
noncomputable def monBasis : ({m : σ →₀ ℕ // mdeg m ≤ d} →₀ K) ≃ₗ[K] Pd σ K d :=
  (Finsupp.supportedEquivFinsupp {m : σ →₀ ℕ | mdeg m ≤ d}).symm

variable {σ K d}

theorem monBasis_symm_apply (P : Pd σ K d) (y : {m : σ →₀ ℕ // mdeg m ≤ d}) :
    (monBasis σ K d).symm P y = coeff y.1 (P : MvPolynomial σ K) := rfl

theorem monBasis_single (y : {m : σ →₀ ℕ // mdeg m ≤ d}) :
    ((monBasis σ K d (Finsupp.single y 1) : Pd σ K d) : MvPolynomial σ K) = monomial y.1 1 :=
  Finsupp.supportedEquivFinsupp_symm_single _ y 1

/-- A linear map into `P_{≤ d}` is the realisation of a matrix as soon as its coefficients on
basis vectors are the matrix entries. -/
theorem monBasis_comp_eq {ι : Type} (A : (ι →₀ K) →ₗ[K] ({m : σ →₀ ℕ // mdeg m ≤ d} →₀ K))
    (f : (ι →₀ K) →ₗ[K] Pd σ K d)
    (h : ∀ (x : ι) (y : {m : σ →₀ ℕ // mdeg m ≤ d}),
      coeff y.1 ((f (Finsupp.single x 1) : Pd σ K d) : MvPolynomial σ K) =
        A (Finsupp.single x 1) y) :
    (monBasis σ K d).toLinearMap ∘ₗ A = f := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  show monBasis σ K d (A (Finsupp.single x 1)) = f (Finsupp.single x 1)
  apply (monBasis σ K d).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  ext y
  rw [monBasis_symm_apply, h]

end MonBasis

namespace Template

variable {K : Type} [Field K] (T : Template K) (d : ℕ)

/-! ### The basis systems -/

/-- Axiom indices of degree at most `d`. -/
noncomputable def axSys : BasisSystem :=
  T.Ax.sub (fun i => T.axDeg i ≤ d) fun g i => by
    show T.axDeg (g • i) ≤ d ↔ T.axDeg i ≤ d
    rw [T.axDeg_smul]

/-- NS certificates: pairs (monomial `μ`, axiom index `i`) with `deg μ + deg i ≤ d`. -/
noncomputable def certSys : BasisSystem :=
  ((T.Var.mon d).prod T.Ax).sub (fun u => mdeg u.1.1 + T.axDeg u.2 ≤ d) fun g u => by
    show mdeg (T.Var.monSMul g u.1.1) + T.axDeg (g • u.2) ≤ d ↔ mdeg u.1.1 + T.axDeg u.2 ≤ d
    rw [mdeg_monSMul, T.axDeg_smul]

/-- The systems of `thm:PC` and `lem:presentation` all have support at most `k d + s`. -/
theorem mon_bounded' : (T.Var.mon d).Bounded (T.k * d + T.s) :=
  (mon_bounded T.var_bounded d).mono (Nat.le_add_right _ _)

theorem low_bounded : (T.Var.mon (d - 1)).Bounded (T.k * d + T.s) :=
  (mon_bounded T.var_bounded (d - 1)).mono
    (le_trans (Nat.mul_le_mul_left _ (Nat.sub_le d 1)) (Nat.le_add_right _ _))

theorem var_bounded' (hd : 1 ≤ d) : T.Var.Bounded (T.k * d + T.s) :=
  T.var_bounded.mono (le_trans (Nat.le_mul_of_pos_right _ hd) (Nat.le_add_right _ _))

theorem mul_bounded (hd : 1 ≤ d) : (T.Var.prod (T.Var.mon (d - 1))).Bounded (T.k * d + T.s) := by
  refine (prod_bounded T.var_bounded (mon_bounded T.var_bounded (d - 1))).mono ?_
  have : T.k + T.k * (d - 1) = T.k * d := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  omega

theorem ax_bounded' : (T.axSys d).Bounded (T.k * d + T.s) :=
  (sub_bounded T.ax_bounded _ _).mono (Nat.le_add_left _ _)

theorem cert_bounded : (T.certSys d).Bounded (T.k * d + T.s) :=
  sub_bounded (prod_bounded (mon_bounded T.var_bounded d) T.ax_bounded) _ _

/-! ### The invariant matrices -/

open Classical in
/-- Inclusion `P_{≤ d-1} ⊆ P_{≤ d}`. -/
noncomputable def inclM : InvMatrix K (T.Var.mon (d - 1)) (T.Var.mon d) where
  entry := fun y x => if y.1 = x.1 then 1 else 0
  inv := fun g y x => by
    show (if T.Var.monSMul g y.1 = T.Var.monSMul g x.1 then (1 : K) else 0) = _
    exact if_congr (T.Var.monSMul_injective g).eq_iff rfl rfl

open Classical in
theorem inclM_entry (y : (T.Var.mon d).Obj) (x : (T.Var.mon (d - 1)).Obj) :
    (T.inclM d).entry y x = if y.1 = x.1 then 1 else 0 := rfl

open Classical in
/-- Multiplication `x ⊗ m ↦ x m`. -/
noncomputable def mulM : InvMatrix K (T.Var.prod (T.Var.mon (d - 1))) (T.Var.mon d) where
  entry := fun y (u : T.Var.Obj × (T.Var.mon (d - 1)).Obj) =>
    if y.1 = Finsupp.single u.1 1 + u.2.1 then 1 else 0
  inv := fun g y (u : T.Var.Obj × (T.Var.mon (d - 1)).Obj) => by
    show (if T.Var.monSMul g y.1 = Finsupp.single (g • u.1) 1 + T.Var.monSMul g u.2.1
      then (1 : K) else 0) = _
    have : Finsupp.single (g • u.1) 1 + T.Var.monSMul g u.2.1 =
        T.Var.monSMul g (Finsupp.single u.1 1 + u.2.1) := by
      rw [monSMul_add]
      congr 1
      exact (Finsupp.mapDomain_single).symm
    rw [this]
    exact if_congr (T.Var.monSMul_injective g).eq_iff rfl rfl

open Classical in
theorem mulM_entry (y : (T.Var.mon d).Obj) (u : T.Var.Obj × (T.Var.mon (d - 1)).Obj) :
    (T.mulM d).entry y u = if y.1 = Finsupp.single u.1 1 + u.2.1 then 1 else 0 := rfl

/-- Axiom coefficients. -/
noncomputable def axM : InvMatrix K (T.axSys d) (T.Var.mon d) where
  entry := fun y i => T.coeff i.1 y.1
  inv := fun g y i => T.coeff_inv g i.1 y.1

open Classical in
/-- The constant polynomial `1`. -/
noncomputable def constM : InvMatrix K BasisSystem.unit (T.Var.mon d) where
  entry := fun y _ => if y.1 = 0 then 1 else 0
  inv := fun g y _ => by
    show (if T.Var.monSMul g y.1 = 0 then (1 : K) else 0) = _
    exact if_congr (mapDomain_eq_zero_iff (T.Var.smul_injective g) y.1) rfl rfl

open Classical in
theorem constM_entry (y : (T.Var.mon d).Obj) (u : BasisSystem.unit.Obj) :
    (T.constM d).entry y u = if y.1 = 0 then 1 else 0 := rfl

open Classical in
/-- The NS certificate map `(μ, i) ↦ μ f_i`: the coefficient of `y` is the coefficient of
`y - μ` in `f_i` when `μ` divides `y`, and zero otherwise. -/
noncomputable def certM : InvMatrix K (T.certSys d) (T.Var.mon d) where
  entry := fun y c => if c.1.1.1 ≤ y.1 then T.coeff c.1.2 (y.1 - c.1.1.1) else 0
  inv := fun g y c => by
    show (if T.Var.monSMul g c.1.1.1 ≤ T.Var.monSMul g y.1 then
      T.coeff (g • c.1.2) (T.Var.monSMul g y.1 - T.Var.monSMul g c.1.1.1) else 0) = _
    refine if_congr (mapDomain_le_iff (T.Var.smul_injective g) _ _) ?_ rfl
    have := T.coeff_inv g c.1.2 (y.1 - c.1.1.1)
    unfold monSMul at this ⊢
    rw [← mapDomain_tsub (T.Var.smul_injective g), this]

open Classical in
theorem certM_entry (y : (T.Var.mon d).Obj) (c : (T.certSys d).Obj) :
    (T.certM d).entry y c =
      if c.1.1.1 ≤ y.1 then T.coeff c.1.2 (y.1 - c.1.1.1) else 0 := rfl

/-! ### The actual maps at universe size `t`, and the realisation theorems -/

section Realise

variable (t : ℕ)

/-- The axioms of degree `≤ d` at size `t`, as a linear map into `P_{≤ d}`. -/
noncomputable def axMap : ((T.axSys d).Rk t →₀ K) →ₗ[K] Pd (T.Var.Rk t) K d :=
  Finsupp.linearCombination K fun (i : {x : T.Ax.Rk t // T.axDeg (T.Ax.up t x) ≤ d}) =>
    (⟨T.poly t i.1, by
      rw [mem_restrictTotalDegree]
      exact le_trans (T.totalDegree_poly_le t i.1) i.2⟩ : Pd (T.Var.Rk t) K d)

theorem totalDegree_cert_le (μ : T.Var.Rk t →₀ ℕ) (i : T.Ax.Rk t) :
    (monomial μ (1 : K) * T.poly t i).totalDegree ≤ mdeg μ + T.axDeg (T.Ax.up t i) :=
  le_trans (totalDegree_mul _ _)
    (add_le_add (totalDegree_monomial_le μ 1) (T.totalDegree_poly_le t i))

/-- The NS certificate map at size `t`: `(μ, i) ↦ μ f_i`, into `P_{≤ d}`. -/
noncomputable def certMap : ((T.certSys d).Rk t →₀ K) →ₗ[K] Pd (T.Var.Rk t) K d :=
  Finsupp.linearCombination K
    fun (c : {x : (T.Var.mon d).Rk t × T.Ax.Rk t //
        mdeg (T.Var.monUp t x.1.1) + T.axDeg (T.Ax.up t x.2) ≤ d}) =>
      (⟨monomial c.1.1.1 (1 : K) * T.poly t c.1.2, by
        rw [mem_restrictTotalDegree]
        have := c.2
        rw [mdeg_monUp] at this
        exact le_trans (T.totalDegree_cert_le t c.1.1.1 c.1.2) this⟩ : Pd (T.Var.Rk t) K d)

/-- The basis of the trivial module. -/
noncomputable def unitEquiv : (BasisSystem.unit.Rk t →₀ K) ≃ₗ[K] K :=
  Finsupp.LinearEquiv.finsuppUnique K K Unit

theorem inclM_realise :
    (monBasis (T.Var.Rk t) K d).toLinearMap ∘ₗ (T.inclM d).realise t =
      inclLow (T.Var.Rk t) K d ∘ₗ (monBasis (T.Var.Rk t) K (d - 1)).toLinearMap := by
  apply monBasis_comp_eq
  intro x y
  have e : (((inclLow (T.Var.Rk t) K d ∘ₗ (monBasis (T.Var.Rk t) K (d - 1)).toLinearMap)
      (Finsupp.single x 1) : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) =
      monomial x.1 1 := monBasis_single x
  classical
  refine Eq.trans (congrArg (MvPolynomial.coeff y.1) e)
    (Eq.trans ?_ (InvMatrix.realise_single_apply (T.inclM d) t x y).symm)
  rw [coeff_monomial, inclM_entry]
  refine if_congr ?_ rfl rfl
  show x.1 = y.1 ↔ T.Var.monUp t y.1 = T.Var.monUp t x.1
  rw [(T.Var.monUp_injective t).eq_iff, eq_comm]

theorem mulM_realise (hd : 1 ≤ d) :
    (monBasis (T.Var.Rk t) K d).toLinearMap ∘ₗ (T.mulM d).realise t =
      mulLow (T.Var.Rk t) K hd ∘ₗ
        LinearMap.lTensor (VarSpace (T.Var.Rk t) K)
          (monBasis (T.Var.Rk t) K (d - 1)).toLinearMap ∘ₗ
        (finsuppTensorFinsupp' K (T.Var.Rk t)
          {m : T.Var.Rk t →₀ ℕ // mdeg m ≤ d - 1}).symm.toLinearMap := by
  apply monBasis_comp_eq
  rintro ⟨v, m⟩ y
  have e : (((mulLow (T.Var.Rk t) K hd ∘ₗ
      LinearMap.lTensor (VarSpace (T.Var.Rk t) K)
        (monBasis (T.Var.Rk t) K (d - 1)).toLinearMap ∘ₗ
      (finsuppTensorFinsupp' K (T.Var.Rk t)
        {m : T.Var.Rk t →₀ ℕ // mdeg m ≤ d - 1}).symm.toLinearMap)
      (Finsupp.single (v, m) 1) : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) =
      monomial (Finsupp.single v 1 + m.1) 1 := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      finsuppTensorFinsupp'_symm_single_eq_single_one_tmul, LinearMap.lTensor_tmul]
    show muRestrict (Pd (T.Var.Rk t) K (d - 1))
      (Finsupp.single v 1 ⊗ₜ[K] monBasis (T.Var.Rk t) K (d - 1) (Finsupp.single m 1)) = _
    rw [muRestrict_tmul, varMul_single, monBasis_single, X, monomial_mul, one_mul]
  classical
  refine Eq.trans (congrArg (MvPolynomial.coeff y.1) e)
    (Eq.trans ?_ (InvMatrix.realise_single_apply (T.mulM d) t (v, m) y).symm)
  rw [coeff_monomial, mulM_entry]
  refine if_congr ?_ rfl rfl
  show Finsupp.single v 1 + m.1 = y.1 ↔
    T.Var.monUp t y.1 = Finsupp.single (T.Var.up t v) 1 + T.Var.monUp t m.1
  rw [← monUp_single, ← monUp_add, (T.Var.monUp_injective t).eq_iff, eq_comm]

theorem axM_realise :
    (monBasis (T.Var.Rk t) K d).toLinearMap ∘ₗ (T.axM d).realise t = T.axMap d t := by
  apply monBasis_comp_eq
  intro i y
  refine Eq.trans ?_ (InvMatrix.realise_single_apply (T.axM d) t i y).symm
  unfold axMap
  rw [Finsupp.linearCombination_single, one_smul]
  rfl

theorem constM_realise :
    (monBasis (T.Var.Rk t) K d).toLinearMap ∘ₗ (T.constM d).realise t =
      constMap (T.Var.Rk t) K d ∘ₗ (unitEquiv (K := K) t).toLinearMap := by
  apply monBasis_comp_eq
  intro u y
  have e : (((constMap (T.Var.Rk t) K d ∘ₗ (unitEquiv (K := K) t).toLinearMap)
      (Finsupp.single u 1) : Pd (T.Var.Rk t) K d) : MvPolynomial (T.Var.Rk t) K) = 1 := by
    have : unitEquiv (K := K) t (Finsupp.single u 1) = 1 := by
      show Finsupp.LinearEquiv.finsuppUnique K K Unit (Finsupp.single (u : Unit) (1 : K)) = 1
      rw [Finsupp.LinearEquiv.finsuppUnique_apply]
      exact Finsupp.single_eq_same
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, this, constMap,
      LinearMap.toSpanSingleton_apply, one_smul]
  classical
  refine Eq.trans (congrArg (MvPolynomial.coeff y.1) e)
    (Eq.trans ?_ (InvMatrix.realise_single_apply (T.constM d) t u y).symm)
  rw [coeff_one, constM_entry]
  refine if_congr ?_ rfl rfl
  show 0 = y.1 ↔ T.Var.monUp t y.1 = 0
  unfold monUp
  rw [mapDomain_eq_zero_iff (T.Var.up_inj t), eq_comm]

theorem certM_realise :
    (monBasis (T.Var.Rk t) K d).toLinearMap ∘ₗ (T.certM d).realise t = T.certMap d t := by
  apply monBasis_comp_eq
  intro c y
  refine Eq.trans ?_ (InvMatrix.realise_single_apply (T.certM d) t c y).symm
  rw [certM_entry]
  unfold certMap
  rw [Finsupp.linearCombination_single, one_smul]
  show MvPolynomial.coeff y.1 (monomial c.1.1.1 (1 : K) * T.poly t c.1.2) =
    if T.Var.monUp t c.1.1.1 ≤ T.Var.monUp t y.1 then
      T.coeff (T.Ax.up t c.1.2) (T.Var.monUp t y.1 - T.Var.monUp t c.1.1.1) else 0
  classical
  rw [coeff_monomial_mul', one_mul, coeff_poly]
  unfold monUp
  refine if_congr (mapDomain_le_iff (T.Var.up_inj t) _ _).symm ?_ rfl
  rw [mapDomain_tsub (T.Var.up_inj t)]

/-- Beyond `n₀`, the image of the axiom map is the span of the instance axioms of degree
`≤ d` (degree stability is used here). -/
theorem range_axMap {t : ℕ} (ht : T.n0 ≤ t) :
    (LinearMap.range (T.axMap d t)).map (Pd (T.Var.Rk t) K d).subtype = V0 (T.inst t) d := by
  unfold axMap V0
  rw [Finsupp.range_linearCombination, Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨i.1, rfl⟩, le_trans (T.totalDegree_poly_le t i.1) i.2⟩
  · rintro ⟨⟨i, rfl⟩, hdeg⟩
    rw [T.totalDegree_poly ht] at hdeg
    exact ⟨_, ⟨⟨i, hdeg⟩, rfl⟩, rfl⟩

/-- Beyond `n₀`, the image of the certificate map is the NS span of the instance. -/
theorem range_certMap {t : ℕ} (ht : T.n0 ≤ t) :
    (LinearMap.range (T.certMap d t)).map (Pd (T.Var.Rk t) K d).subtype =
      NS.NSspan (T.inst t) d := by
  unfold certMap NS.NSspan
  rw [Finsupp.range_linearCombination, Submodule.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨c.1.1.1, T.poly t c.1.2, ⟨c.1.2, rfl⟩, ?_, rfl⟩
    rw [T.totalDegree_poly ht]
    have : mdeg (T.Var.monUp t c.1.1.1) + T.axDeg (T.Ax.up t c.1.2) ≤ d := c.2
    rw [mdeg_monUp] at this
    exact this
  · rintro ⟨m, _, ⟨i, rfl⟩, hdeg, rfl⟩
    rw [T.totalDegree_poly ht] at hdeg
    have hm : mdeg m ≤ d := le_trans (Nat.le_add_right _ _) hdeg
    have hc : mdeg (T.Var.monUp t m) + T.axDeg (T.Ax.up t i) ≤ d := by
      rw [mdeg_monUp]; exact hdeg
    exact ⟨_, ⟨⟨(⟨m, hm⟩, i), hc⟩, rfl⟩, rfl⟩

end Realise

end Template

end DegreeProfilesReview.Uniform
