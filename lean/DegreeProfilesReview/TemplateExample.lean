/-
Stage 2, regression: the definition of a uniform template is not vacuous and its instances are
the intended polynomial systems.

`points` is the basis system of single labels (`Obj = ℕ`, rank `t` part `Fin t`).  The template
`sumOne` has variables `x_j` (one for each label), a single axiom index, and coefficient
function "`-1` on the empty monomial, `1` on every monomial of degree one".  Its instance at
universe size `t` is proved to be the one-element system

      { x_0 + x_1 + ⋯ + x_{t-1} - 1 }

in the polynomial ring `R[x_0, …, x_{t-1}]`: the axiom has a single index of empty support but
mentions every label, which is the situation the template formalism is designed for.

The file also records that the manuscript's index sets are basis systems: `tuples a` (ordered
`a`-tuples of labels, repetitions allowed, support `≤ a`) and `sigma` (finitely many types).
Restriction to an equality pattern is `BasisSystem.sub`.
-/
import DegreeProfilesReview.Templates
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi

open MvPolynomial

namespace DegreeProfilesReview.Uniform

open BasisSystem

/-- Single labels. -/
def points : BasisSystem where
  Obj := ℕ
  supp := fun i => {i}
  supp_smul := fun g i => by
    rw [Finset.image_singleton]
    rfl
  fixed := fun g i h => h i (Finset.mem_singleton_self i)
  Rk := fun t => Fin t
  up := fun _ x => x.val
  up_inj := fun _ => Fin.val_injective
  range_up := fun t u => by
    rw [Finset.singleton_subset_iff, Finset.mem_range]
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun h => ⟨⟨u, h⟩, rfl⟩⟩

theorem points_bounded : points.Bounded 1 := fun i => by
  show ({i} : Finset ℕ).card ≤ 1
  rw [Finset.card_singleton]

theorem eq_single_of_mdeg_eq_one {α : Type*} {m : α →₀ ℕ} (h : mdeg m = 1) :
    ∃ j, m = Finsupp.single j 1 := by
  have hcard : m.support.card ≤ 1 := h ▸ card_support_le_mdeg m
  have hne : m.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    have : m = 0 := Finsupp.support_eq_empty.mp h0
    rw [this] at h
    simp [mdeg] at h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hne))
  obtain ⟨_, hm⟩ := (Finsupp.support_eq_singleton).mp hj
  refine ⟨j, ?_⟩
  have h1 : mdeg m = m j := by
    unfold mdeg Finsupp.sum
    rw [hj, Finset.sum_singleton]
  rw [hm, ← h1, h]

theorem mdeg_single {α : Type*} (j : α) (e : ℕ) : mdeg (Finsupp.single j e) = e := by
  unfold mdeg
  rw [Finsupp.sum_single_index]
  rfl

open Classical in
/-- The template with the single axiom `x_0 + ⋯ + x_{t-1} - 1`. -/
noncomputable def sumOne (R : Type) [Field R] : Template R where
  Var := points
  Ax := BasisSystem.unit
  k := 1
  s := 0
  D := 1
  n0 := 1
  hk := le_refl 1
  hn0 := le_refl 1
  hn0' := le_refl 1
  var_bounded := points_bounded
  ax_bounded := BasisSystem.unit_bounded 0
  coeff := fun _ m => if m = 0 then -1 else if mdeg m = 1 then 1 else 0
  coeff_inv := fun g _ m => by
    have h0 : points.monSMul g m = 0 ↔ m = 0 := by
      constructor
      · intro h
        apply points.monSMul_injective g
        rw [h]
        exact (Finsupp.mapDomain_zero).symm
      · rintro rfl
        exact Finsupp.mapDomain_zero
    rw [mdeg_monSMul]
    exact if_congr h0 rfl rfl
  coeff_deg := fun _ m h => by
    by_cases h0 : m = 0
    · subst h0
      simp [mdeg]
    · by_cases h1 : mdeg m = 1
      · exact le_of_eq h1
      · rw [if_neg h0, if_neg h1] at h
        exact absurd rfl h

/-- The polynomial `x_0 + ⋯ + x_{t-1} - 1`. -/
noncomputable def sumOnePoly (R : Type) [Field R] (t : ℕ) : MvPolynomial (Fin t) R :=
  (∑ j : Fin t, X j) - 1

/-- The instance of `sumOne` at size `t` is `x_0 + ⋯ + x_{t-1} - 1`. -/
theorem sumOne_poly (R : Type) [Field R] (t : ℕ) (i : (sumOne R).Ax.Rk t) :
    (sumOne R).poly t i = sumOnePoly R t := by
  classical
  apply MvPolynomial.ext
  intro m
  unfold sumOnePoly
  rw [Template.coeff_poly, coeff_sub, coeff_sum, coeff_one]
  show (if points.monUp t m = 0 then (-1 : R) else if mdeg (points.monUp t m) = 1 then 1 else 0)
    = _
  rw [mdeg_monUp]
  have hup : points.monUp t m = 0 ↔ m = 0 := by
    constructor
    · intro h
      apply points.monUp_injective t
      rw [h]
      exact (Finsupp.mapDomain_zero).symm
    · rintro rfl
      exact Finsupp.mapDomain_zero
  by_cases h0 : m = 0
  · subst h0
    rw [if_pos (hup.mpr rfl), if_pos rfl]
    have : ∀ j : Fin t, coeff (0 : Fin t →₀ ℕ) (X j : MvPolynomial (Fin t) R) = 0 := by
      intro j
      rw [coeff_X', if_neg]
      intro h
      have := congrArg (fun f => f j) h
      simp at this
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_const_zero, zero_sub]
  · have e0 : (if (0 : Fin t →₀ ℕ) = m then (1 : R) else 0) = 0 := if_neg fun h => h0 h.symm
    rw [if_neg (fun h => h0 (hup.mp h)), e0, sub_zero]
    by_cases h1 : mdeg m = 1
    · obtain ⟨j0, rfl⟩ := eq_single_of_mdeg_eq_one (α := Fin t) h1
      rw [if_pos h1]
      have : ∀ j : Fin t, coeff (Finsupp.single j0 1) (X j : MvPolynomial (Fin t) R) =
          if j = j0 then 1 else 0 := by
        intro j
        rw [coeff_X']
        refine if_congr ?_ rfl rfl
        constructor
        · intro h
          exact (Finsupp.single_left_injective one_ne_zero) h
        · rintro rfl; rfl
      rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_ite_eq' Finset.univ j0]
      simp
    · rw [if_neg h1]
      symm
      apply Finset.sum_eq_zero
      intro j _
      rw [coeff_X', if_neg]
      rintro rfl
      exact h1 (mdeg_single j 1)

/-- The instance at size `t` is the one-element system `{x_0 + ⋯ + x_{t-1} - 1}`. -/
theorem sumOne_inst (R : Type) [Field R] (t : ℕ) :
    (sumOne R).inst t = {sumOnePoly R t} := by
  unfold Template.inst
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    exact sumOne_poly R t i
  · rintro rfl
    exact ⟨(), sumOne_poly R t ()⟩

/-! ### The manuscript's index sets as basis systems -/

/-- Ordered `a`-tuples of labels (repetitions allowed). -/
def tuples (a : ℕ) : BasisSystem where
  Obj := Fin a → ℕ
  act :=
    { smul := fun g f => fun i => g (f i)
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  supp := fun f => Finset.univ.image f
  supp_smul := fun g f => by
    show Finset.univ.image (fun i => g (f i)) = (Finset.univ.image f).image g
    rw [Finset.image_image]
    rfl
  fixed := fun g f h => by
    funext i
    exact h (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
  Rk := fun t => Fin a → Fin t
  up := fun _ x => fun i => (x i).val
  up_inj := fun _ x y h => by
    funext i
    exact Fin.val_injective (congrFun h i)
  range_up := fun t f => by
    constructor
    · rintro ⟨x, rfl⟩
      intro l hl
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      exact Finset.mem_range.mpr (x i).2
    · intro h
      exact ⟨fun i => ⟨f i, Finset.mem_range.mp
        (h (Finset.mem_image_of_mem f (Finset.mem_univ i)))⟩, rfl⟩

theorem tuples_bounded (a : ℕ) : (tuples a).Bounded a := fun f => by
  show (Finset.univ.image f).card ≤ a
  exact le_trans Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin])

/-- Finitely many types. -/
def sigma {ι : Type} [Finite ι] (𝒰 : ι → BasisSystem) : BasisSystem where
  Obj := Σ i, (𝒰 i).Obj
  act :=
    { smul := fun g u => ⟨u.1, g • u.2⟩
      one_smul := fun u => by
        show (⟨u.1, (1 : Equiv.Perm ℕ) • u.2⟩ : Σ i, (𝒰 i).Obj) = u
        rw [one_smul]
      mul_smul := fun g h u => by
        show (⟨u.1, (g * h) • u.2⟩ : Σ i, (𝒰 i).Obj) = ⟨u.1, g • h • u.2⟩
        rw [mul_smul] }
  supp := fun u => (𝒰 u.1).supp u.2
  supp_smul := fun g u => (𝒰 u.1).supp_smul g u.2
  fixed := fun g u h => by
    show (⟨u.1, g • u.2⟩ : Σ i, (𝒰 i).Obj) = u
    rw [(𝒰 u.1).fixed g u.2 h]
  Rk := fun t => Σ i, (𝒰 i).Rk t
  up := fun t x => ⟨x.1, (𝒰 x.1).up t x.2⟩
  up_inj := fun t x y h => by
    obtain ⟨i, x⟩ := x
    obtain ⟨j, y⟩ := y
    have h' : (⟨i, (𝒰 i).up t x⟩ : Σ i, (𝒰 i).Obj) = ⟨j, (𝒰 j).up t y⟩ := h
    obtain ⟨hij, h2⟩ := Sigma.mk.inj_iff.mp h'
    subst hij
    rw [(𝒰 i).up_inj t (eq_of_heq h2)]
  range_up := fun t u => by
    obtain ⟨i, u⟩ := u
    show _ ↔ (𝒰 i).supp u ⊆ Finset.range t
    rw [← (𝒰 i).range_up]
    constructor
    · rintro ⟨⟨j, x⟩, hx⟩
      have hx' : (⟨j, (𝒰 j).up t x⟩ : Σ i, (𝒰 i).Obj) = ⟨i, u⟩ := hx
      obtain ⟨hji, h2⟩ := Sigma.mk.inj_iff.mp hx'
      subst hji
      exact ⟨x, eq_of_heq h2⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨i, x⟩, rfl⟩

theorem sigma_bounded {ι : Type} [Finite ι] {𝒰 : ι → BasisSystem} {r : ℕ}
    (h : ∀ i, (𝒰 i).Bounded r) : (sigma 𝒰).Bounded r := fun u => h u.1 u.2

end DegreeProfilesReview.Uniform
