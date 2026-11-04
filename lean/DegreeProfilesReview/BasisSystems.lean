/-
Stage 2, step 1a: relabelling-invariant basis systems and invariant ("stable") matrices.

Labels are natural numbers; the relabelling group is `Equiv.Perm ℕ`.  A *basis system* is a
set of labelled objects with a finite support function such that

* the support is equivariant,
* a relabelling fixing the support pointwise fixes the object,
* for every universe size `t` a finite type `Rk t` is given together with an injection `up t`
  into the objects whose image is EXACTLY the set of objects supported in `{0, …, t-1}`.

These are the manuscript's "finite permutation bases built from fixed types of labelled
objects" (§3): tuples, monomials, pairs of these.  The rank-`t` permutation module is
`Rk t →₀ K`.  An *invariant matrix* between two systems is a relabelling-invariant entry
function; its rank-`t` realisation is the manuscript's "stable matrix": the entries do not
depend on `t` and depend only on the equality pattern of the labels.

Combinators: one-point system, products, invariant subsystems, monomials of bounded degree.
No hypothesis is used in this file.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Linarith

namespace DegreeProfilesReview.Uniform

/-- A relabelling-invariant family of finite bases. -/
structure BasisSystem where
  /-- All labelled objects (labels in `ℕ`). -/
  Obj : Type
  [act : MulAction (Equiv.Perm ℕ) Obj]
  /-- The finite set of labels occurring in an object. -/
  supp : Obj → Finset ℕ
  supp_smul : ∀ (g : Equiv.Perm ℕ) (u : Obj), supp (g • u) = (supp u).image g
  fixed : ∀ (g : Equiv.Perm ℕ) (u : Obj), (∀ x ∈ supp u, g x = x) → g • u = u
  /-- The basis at universe size `t`. -/
  Rk : ℕ → Type
  [fin : ∀ t, Finite (Rk t)]
  up : ∀ t, Rk t → Obj
  up_inj : ∀ t, Function.Injective (up t)
  range_up : ∀ t u, (∃ x, up t x = u) ↔ supp u ⊆ Finset.range t

attribute [instance] BasisSystem.act BasisSystem.fin

namespace BasisSystem

/-- Every object uses at most `r` labels. -/
def Bounded (𝒰 : BasisSystem) (r : ℕ) : Prop := ∀ u : 𝒰.Obj, (𝒰.supp u).card ≤ r

theorem Bounded.mono {𝒰 : BasisSystem} {r r' : ℕ} (h : 𝒰.Bounded r) (hr : r ≤ r') :
    𝒰.Bounded r' := fun u => le_trans (h u) hr

theorem supp_up (𝒰 : BasisSystem) (t : ℕ) (x : 𝒰.Rk t) :
    𝒰.supp (𝒰.up t x) ⊆ Finset.range t :=
  (𝒰.range_up t _).mp ⟨x, rfl⟩

/-! ### The one-point system -/

/-- The one-point system (basis of the trivial module `K`). -/
def unit : BasisSystem where
  Obj := Unit
  act := { smul := fun _ u => u, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
  supp := fun _ => ∅
  supp_smul := fun _ _ => by simp
  fixed := fun _ _ _ => rfl
  Rk := fun _ => Unit
  up := fun _ x => x
  up_inj := fun _ _ _ h => h
  range_up := fun _ u => ⟨fun _ => Finset.empty_subset _, fun _ => ⟨u, rfl⟩⟩

theorem unit_bounded (r : ℕ) : unit.Bounded r := fun _ => by simp [unit]

/-! ### Products -/

/-- Pairs of objects; the support is the union. -/
def prod (𝒰 𝒱 : BasisSystem) : BasisSystem where
  Obj := 𝒰.Obj × 𝒱.Obj
  supp := fun u => 𝒰.supp u.1 ∪ 𝒱.supp u.2
  supp_smul := fun g u => by
    show 𝒰.supp (g • u.1) ∪ 𝒱.supp (g • u.2) = _
    rw [𝒰.supp_smul, 𝒱.supp_smul, Finset.image_union]
  fixed := fun g u h => by
    apply Prod.ext
    · exact 𝒰.fixed g u.1 fun x hx => h x (Finset.mem_union_left _ hx)
    · exact 𝒱.fixed g u.2 fun x hx => h x (Finset.mem_union_right _ hx)
  Rk := fun t => 𝒰.Rk t × 𝒱.Rk t
  up := fun t x => (𝒰.up t x.1, 𝒱.up t x.2)
  up_inj := fun t x y h => by
    apply Prod.ext
    · exact 𝒰.up_inj t (congrArg Prod.fst h)
    · exact 𝒱.up_inj t (congrArg Prod.snd h)
  range_up := fun t u => by
    rw [Finset.union_subset_iff, ← 𝒰.range_up, ← 𝒱.range_up]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x.1, rfl⟩, ⟨x.2, rfl⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨(x, y), Prod.ext hx hy⟩

theorem prod_bounded {𝒰 𝒱 : BasisSystem} {a b : ℕ} (hU : 𝒰.Bounded a) (hV : 𝒱.Bounded b) :
    (𝒰.prod 𝒱).Bounded (a + b) := fun (u : 𝒰.Obj × 𝒱.Obj) =>
  le_trans (Finset.card_union_le _ _) (add_le_add (hU u.1) (hV u.2))

/-! ### Invariant subsystems -/

/-- The subsystem of objects satisfying a relabelling-invariant predicate. -/
def sub (𝒰 : BasisSystem) (P : 𝒰.Obj → Prop) (hP : ∀ (g : Equiv.Perm ℕ) u, P (g • u) ↔ P u) :
    BasisSystem where
  Obj := {u : 𝒰.Obj // P u}
  act :=
    { smul := fun g u => ⟨g • u.1, (hP g u.1).mpr u.2⟩
      one_smul := fun u => Subtype.ext (one_smul _ u.1)
      mul_smul := fun g h u => Subtype.ext (mul_smul g h u.1) }
  supp := fun u => 𝒰.supp u.1
  supp_smul := fun g u => 𝒰.supp_smul g u.1
  fixed := fun g u h => Subtype.ext (𝒰.fixed g u.1 h)
  Rk := fun t => {x : 𝒰.Rk t // P (𝒰.up t x)}
  up := fun t x => ⟨𝒰.up t x.1, x.2⟩
  up_inj := fun t x y h => Subtype.ext (𝒰.up_inj t (congrArg Subtype.val h))
  range_up := fun t u => by
    rw [← 𝒰.range_up]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, by rw [hx]; exact u.2⟩, Subtype.ext hx⟩

theorem sub_bounded {𝒰 : BasisSystem} {r : ℕ} (h : 𝒰.Bounded r) (P : 𝒰.Obj → Prop)
    (hP : ∀ (g : Equiv.Perm ℕ) u, P (g • u) ↔ P u) : (𝒰.sub P hP).Bounded r :=
  fun u => h u.1

/-! ### Monomials -/

/-- Degree of an exponent vector. -/
def mdeg {α : Type*} (m : α →₀ ℕ) : ℕ := m.sum fun _ e => e

theorem mdeg_mapDomain {α β : Type*} (f : α → β) (m : α →₀ ℕ) :
    mdeg (Finsupp.mapDomain f m) = mdeg m := by
  unfold mdeg
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

theorem le_mdeg {α : Type*} (m : α →₀ ℕ) (a : α) : m a ≤ mdeg m := by
  by_cases h : m a = 0
  · rw [h]; exact Nat.zero_le _
  · exact Finset.single_le_sum (f := fun a => m a) (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr h)

theorem finite_mdeg_le (α : Type*) [Finite α] (d : ℕ) : Finite {m : α →₀ ℕ // mdeg m ≤ d} := by
  have h1 : Set.Finite {m : α →₀ ℕ | ∀ a, m a ≤ d} :=
    ((Set.Finite.pi' fun _ => Set.finite_le_nat d).preimage DFunLike.coe_injective.injOn)
  have h2 : Set.Finite {m : α →₀ ℕ | mdeg m ≤ d} :=
    h1.subset fun m hm a => le_trans (le_mdeg m a) hm
  exact h2.to_subtype

/-- Relabelling a monomial. -/
noncomputable def monSMul (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) (m : 𝒰.Obj →₀ ℕ) :
    𝒰.Obj →₀ ℕ :=
  Finsupp.mapDomain (fun u => g • u) m

/-- Labels occurring in a monomial. -/
def monSupp (𝒰 : BasisSystem) (m : 𝒰.Obj →₀ ℕ) : Finset ℕ := m.support.biUnion 𝒰.supp

theorem monSMul_one (𝒰 : BasisSystem) (m : 𝒰.Obj →₀ ℕ) : 𝒰.monSMul 1 m = m := by
  unfold monSMul
  have : (fun u : 𝒰.Obj => (1 : Equiv.Perm ℕ) • u) = id := funext fun u => one_smul _ u
  rw [this, Finsupp.mapDomain_id]

theorem monSMul_mul (𝒰 : BasisSystem) (g h : Equiv.Perm ℕ) (m : 𝒰.Obj →₀ ℕ) :
    𝒰.monSMul (g * h) m = 𝒰.monSMul g (𝒰.monSMul h m) := by
  unfold monSMul
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext u
  exact mul_smul g h u

theorem smul_injective (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) :
    Function.Injective (fun u : 𝒰.Obj => g • u) :=
  MulAction.injective g

theorem monSMul_add (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) (m m' : 𝒰.Obj →₀ ℕ) :
    𝒰.monSMul g (m + m') = 𝒰.monSMul g m + 𝒰.monSMul g m' :=
  Finsupp.mapDomain_add

theorem monSMul_injective (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) :
    Function.Injective (𝒰.monSMul g) :=
  Finsupp.mapDomain_injective (𝒰.smul_injective g)

theorem mdeg_monSMul (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) (m : 𝒰.Obj →₀ ℕ) :
    mdeg (𝒰.monSMul g m) = mdeg m :=
  mdeg_mapDomain _ m

theorem monSupp_monSMul (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) (m : 𝒰.Obj →₀ ℕ) :
    𝒰.monSupp (𝒰.monSMul g m) = (𝒰.monSupp m).image g := by
  classical
  unfold monSupp monSMul
  rw [Finsupp.mapDomain_support_of_injective (𝒰.smul_injective g), Finset.image_biUnion,
    Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro a _
  exact 𝒰.supp_smul g a

theorem monSMul_fixed (𝒰 : BasisSystem) (g : Equiv.Perm ℕ) (m : 𝒰.Obj →₀ ℕ)
    (h : ∀ x ∈ 𝒰.monSupp m, g x = x) : 𝒰.monSMul g m = m := by
  unfold monSMul
  have : Finsupp.mapDomain (fun u : 𝒰.Obj => g • u) m = Finsupp.mapDomain id m := by
    apply Finsupp.mapDomain_congr
    intro a ha
    apply 𝒰.fixed g a
    intro x hx
    exact h x (Finset.mem_biUnion.mpr ⟨a, ha, hx⟩)
  rw [this, Finsupp.mapDomain_id]

/-- Lift a rank-`t` monomial to a monomial in all objects. -/
noncomputable def monUp (𝒰 : BasisSystem) (t : ℕ) (m : 𝒰.Rk t →₀ ℕ) : 𝒰.Obj →₀ ℕ :=
  Finsupp.mapDomain (𝒰.up t) m

theorem monUp_injective (𝒰 : BasisSystem) (t : ℕ) : Function.Injective (𝒰.monUp t) :=
  Finsupp.mapDomain_injective (𝒰.up_inj t)

theorem mdeg_monUp (𝒰 : BasisSystem) (t : ℕ) (m : 𝒰.Rk t →₀ ℕ) : mdeg (𝒰.monUp t m) = mdeg m :=
  mdeg_mapDomain _ m

theorem monUp_add (𝒰 : BasisSystem) (t : ℕ) (m m' : 𝒰.Rk t →₀ ℕ) :
    𝒰.monUp t (m + m') = 𝒰.monUp t m + 𝒰.monUp t m' :=
  Finsupp.mapDomain_add

theorem monUp_single (𝒰 : BasisSystem) (t : ℕ) (x : 𝒰.Rk t) (e : ℕ) :
    𝒰.monUp t (Finsupp.single x e) = Finsupp.single (𝒰.up t x) e :=
  Finsupp.mapDomain_single

/-- A monomial in all objects comes from rank `t` iff its labels lie in `{0,…,t-1}`. -/
theorem range_monUp (𝒰 : BasisSystem) (t : ℕ) (m : 𝒰.Obj →₀ ℕ) :
    (∃ m', 𝒰.monUp t m' = m) ↔ 𝒰.monSupp m ⊆ Finset.range t := by
  classical
  constructor
  · rintro ⟨m', rfl⟩
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    have hsub := Finsupp.mapDomain_support (f := 𝒰.up t) (s := m') ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hsub
    exact 𝒰.supp_up t y hxa
  · intro h
    have hrange : (↑m.support : Set 𝒰.Obj) ⊆ Set.range (𝒰.up t) := by
      intro a ha
      apply (𝒰.range_up t a).mpr
      intro x hx
      exact h (Finset.mem_biUnion.mpr ⟨a, ha, hx⟩)
    exact ⟨Finsupp.comapDomain (𝒰.up t) m (𝒰.up_inj t).injOn,
      Finsupp.mapDomain_comapDomain _ (𝒰.up_inj t) m hrange⟩

/-- Monomials of degree at most `d` in the objects of `𝒰`. -/
noncomputable def mon (𝒰 : BasisSystem) (d : ℕ) : BasisSystem where
  Obj := {m : 𝒰.Obj →₀ ℕ // mdeg m ≤ d}
  act :=
    { smul := fun g m => ⟨𝒰.monSMul g m.1, by rw [mdeg_monSMul]; exact m.2⟩
      one_smul := fun m => Subtype.ext (𝒰.monSMul_one m.1)
      mul_smul := fun g h m => Subtype.ext (𝒰.monSMul_mul g h m.1) }
  supp := fun m => 𝒰.monSupp m.1
  supp_smul := fun g m => 𝒰.monSupp_monSMul g m.1
  fixed := fun g m h => Subtype.ext (𝒰.monSMul_fixed g m.1 h)
  Rk := fun t => {m : 𝒰.Rk t →₀ ℕ // mdeg m ≤ d}
  fin := fun t => finite_mdeg_le (𝒰.Rk t) d
  up := fun t m => ⟨𝒰.monUp t m.1, by rw [mdeg_monUp]; exact m.2⟩
  up_inj := fun t x y h => Subtype.ext (𝒰.monUp_injective t (congrArg Subtype.val h))
  range_up := fun t m => by
    rw [← 𝒰.range_monUp]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨m', hm'⟩
      exact ⟨⟨m', by rw [← mdeg_monUp, hm']; exact m.2⟩, Subtype.ext hm'⟩

theorem card_support_le_mdeg {α : Type*} (m : α →₀ ℕ) : m.support.card ≤ mdeg m := by
  unfold mdeg Finsupp.sum
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro a ha
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ha)

theorem card_monSupp_le {𝒰 : BasisSystem} {k : ℕ} (hk : 𝒰.Bounded k) (m : 𝒰.Obj →₀ ℕ) :
    (𝒰.monSupp m).card ≤ k * mdeg m := by
  unfold monSupp
  calc (m.support.biUnion 𝒰.supp).card ≤ ∑ a ∈ m.support, (𝒰.supp a).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ m.support, k := Finset.sum_le_sum fun a _ => hk a
    _ = m.support.card * k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ mdeg m * k := Nat.mul_le_mul_right k (card_support_le_mdeg m)
    _ = k * mdeg m := Nat.mul_comm _ _

theorem mon_bounded {𝒰 : BasisSystem} {k : ℕ} (hk : 𝒰.Bounded k) (d : ℕ) :
    (𝒰.mon d).Bounded (k * d) := fun m =>
  le_trans (card_monSupp_le hk m.1) (Nat.mul_le_mul_left k m.2)

end BasisSystem

/-! ### Invariant matrices -/

/-- A relabelling-invariant matrix from `𝒰` to `𝒱` with entries in `K`. -/
structure InvMatrix (K : Type) (𝒰 𝒱 : BasisSystem) where
  entry : 𝒱.Obj → 𝒰.Obj → K
  inv : ∀ (g : Equiv.Perm ℕ) v u, entry (g • v) (g • u) = entry v u

namespace InvMatrix

variable {K : Type} [Semiring K] {𝒰 𝒱 : BasisSystem}

/-- The rank-`t` realisation: the matrix with the same entries on the rank-`t` bases. -/
noncomputable def realise (a : InvMatrix K 𝒰 𝒱) (t : ℕ) : (𝒰.Rk t →₀ K) →ₗ[K] (𝒱.Rk t →₀ K) :=
  Finsupp.linearCombination K fun x =>
    Finsupp.equivFunOnFinite.symm fun y => a.entry (𝒱.up t y) (𝒰.up t x)

theorem realise_single_apply (a : InvMatrix K 𝒰 𝒱) (t : ℕ) (x : 𝒰.Rk t) (y : 𝒱.Rk t) :
    a.realise t (Finsupp.single x 1) y = a.entry (𝒱.up t y) (𝒰.up t x) := by
  unfold realise
  rw [Finsupp.linearCombination_single, one_smul]
  rfl

end InvMatrix

/-! ### Moving labels -/

/-- Given finite sets `A ⊆ {0,…,n-1}` and `B` with `|A ∪ B| ≤ n`, some relabelling fixes `A`
pointwise and moves `B` into `{0,…,n-1}`. -/
theorem exists_perm_fix_move (A : Finset ℕ) (n : ℕ) (hA : A ⊆ Finset.range n) :
    ∀ (c : ℕ) (B : Finset ℕ), (B.filter fun b => n ≤ b).card = c → (A ∪ B).card ≤ n →
      ∃ σ : Equiv.Perm ℕ, (∀ a ∈ A, σ a = a) ∧ ∀ b ∈ B, σ b < n := by
  intro c
  induction c with
  | zero =>
    intro B hc _
    refine ⟨1, fun _ _ => rfl, fun b hb => ?_⟩
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
    have := hc hb
    simpa using this
  | succ c ih =>
    intro B hc hcard
    have hne : (B.filter fun b => n ≤ b).Nonempty := by
      rw [← Finset.card_pos, hc]; exact Nat.succ_pos _
    obtain ⟨b, hb⟩ := hne
    rw [Finset.mem_filter] at hb
    obtain ⟨hbB, hbn⟩ := hb
    -- a free label below `n`
    have hfree : ∃ x, x ∈ Finset.range n ∧ x ∉ A ∪ B := by
      by_contra hno
      push_neg at hno
      have hsub : insert b (Finset.range n) ⊆ A ∪ B := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_union_right _ hbB
        · exact hno x hx
      have h1 := Finset.card_le_card hsub
      have hbnot : b ∉ Finset.range n := by simp; exact hbn
      rw [Finset.card_insert_of_notMem hbnot, Finset.card_range] at h1
      omega
    obtain ⟨x, hxn, hxAB⟩ := hfree
    rw [Finset.mem_range] at hxn
    have hxA : x ∉ A := fun h => hxAB (Finset.mem_union_left _ h)
    have hxB : x ∉ B := fun h => hxAB (Finset.mem_union_right _ h)
    set B' := insert x (B.erase b) with hB'
    have hfilter : (B'.filter fun y => n ≤ y) = (B.filter fun y => n ≤ y).erase b := by
      ext y
      simp only [hB', Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · omega
        · exact ⟨h1.1, h1.2, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨Or.inr ⟨h1, h2⟩, h3⟩
    have hc' : (B'.filter fun y => n ≤ y).card = c := by
      rw [hfilter, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hbB, hbn⟩), hc]
      rfl
    have hcard' : (A ∪ B').card ≤ n := by
      have hbA : b ∉ A := fun h => by
        have := Finset.mem_range.mp (hA h); omega
      have hsub : A ∪ B' ⊆ insert x ((A ∪ B).erase b) := by
        intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · have : y ≠ b := fun e => hbA (e ▸ h)
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨this, Finset.mem_union_left _ h⟩)
        · rcases Finset.mem_insert.mp h with rfl | h
          · exact Finset.mem_insert_self _ _
          · obtain ⟨h1, h2⟩ := Finset.mem_erase.mp h
            exact Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨h1, Finset.mem_union_right _ h2⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le x ((A ∪ B).erase b)
      have h3 := Finset.card_erase_of_mem (Finset.mem_union_right A hbB)
      have h4 : 0 < (A ∪ B).card := Finset.card_pos.mpr ⟨b, Finset.mem_union_right _ hbB⟩
      omega
    obtain ⟨σ', hσA, hσB⟩ := ih B' hc' hcard'
    refine ⟨σ' * Equiv.swap b x, ?_, ?_⟩
    · intro a ha
      have h1 : a ≠ b := fun e => by
        have := Finset.mem_range.mp (hA ha); omega
      have h2 : a ≠ x := fun e => hxA (e ▸ ha)
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact hσA a ha
    · intro y hy
      rw [Equiv.Perm.mul_apply]
      by_cases hyb : y = b
      · subst hyb
        rw [Equiv.swap_apply_left]
        exact hσB x (Finset.mem_insert_self _ _)
      · have hyx : y ≠ x := fun e => hxB (e ▸ hy)
        rw [Equiv.swap_apply_of_ne_of_ne hyb hyx]
        exact hσB y (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hyb, hy⟩))

theorem exists_perm_fix_move' (A B : Finset ℕ) (n : ℕ) (hA : A ⊆ Finset.range n)
    (hcard : (A ∪ B).card ≤ n) :
    ∃ σ : Equiv.Perm ℕ, (∀ a ∈ A, σ a = a) ∧ ∀ b ∈ B, σ b < n :=
  exists_perm_fix_move A n hA _ B rfl hcard

end DegreeProfilesReview.Uniform
