/-
Stage 3: the intended block group exists.

For a prime `p`, `q = p^a` and any `n`, `elemAbBlock p a n` is the REGULAR ELEMENTARY ABELIAN
group `(ℤ/p)^a`, acting by translation on the deleted block `{n, …, n+q-1}` (identified with
`(ℤ/p)^a` by a fixed bijection) and trivially on all other labels.  It is a `BlockGroup`:
it fixes the labels `< n`, is transitive on the block, and is a `p`-group.

This is the group `A` of the source (Hone et al., §8.3: a transitive elementary abelian
`p`-subgroup of `S_{p^a}`) and of the manuscript's repair.  Hence the deletion functor
`Φhat (elemAbBlock p a n) K` is completely explicit.  No external hypothesis.
-/
import DegreeProfilesReview.ConcreteM5
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Action.End

namespace DegreeProfilesReview.ConcreteM5

open DegreeProfilesReview.SymRep

section ElemAb

variable (p a n : ℕ) [Fact p.Prime]

/-- `(ℤ/p)^a`, written multiplicatively. -/
abbrev ElemAb : Type := Multiplicative (Fin a → ZMod p)

theorem card_elemAb : Nat.card (ElemAb p a) = p ^ a := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

/-- The deleted block as a subtype of the labels. -/
abbrev Block (n q : ℕ) : Type := {k : ℕ // n ≤ k ∧ k < n + q}

/-- `Fin q ≃ {n, …, n+q-1}`. -/
def finBlockEquiv (n q : ℕ) : Fin q ≃ Block n q where
  toFun i := ⟨n + i.1, Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _⟩
  invFun k := ⟨k.1 - n, by have := k.2; omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv k := by
    apply Subtype.ext
    have := k.2
    simp only
    omega

/-- A fixed identification of `(ℤ/p)^a` with the block. -/
noncomputable def blockEquiv : ElemAb p a ≃ Block n (p ^ a) :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin])).trans
    (finBlockEquiv n (p ^ a))

/-- Translation on the block, extended by the identity. -/
noncomputable def blockHom : ElemAb p a →* Equiv.Perm ℕ :=
  (Equiv.Perm.extendDomainHom (blockEquiv p a n)).comp
    (MulAction.toPermHom (ElemAb p a) (ElemAb p a))

theorem blockHom_apply_not_block (v : ElemAb p a) {k : ℕ} (hk : ¬ (n ≤ k ∧ k < n + p ^ a)) :
    blockHom p a n v k = k :=
  Equiv.Perm.extendDomain_apply_not_subtype (MulAction.toPerm v) (blockEquiv p a n) hk

theorem blockHom_apply_block (v : ElemAb p a) {k : ℕ} (hk : n ≤ k ∧ k < n + p ^ a) :
    blockHom p a n v k = (blockEquiv p a n (v * (blockEquiv p a n).symm ⟨k, hk⟩)).1 :=
  Equiv.Perm.extendDomain_apply_subtype (MulAction.toPerm v) (blockEquiv p a n) hk

theorem blockHom_mem_Sfin (v : ElemAb p a) : blockHom p a n v ∈ Sfin (n + p ^ a) :=
  fun k hk => blockHom_apply_not_block p a n v (by omega)

/-- **The regular elementary abelian block group.** -/
noncomputable def elemAbBlock : BlockGroup p n (p ^ a) where
  A := (blockHom p a n).range.subgroupOf (Sfin (n + p ^ a))
  fixes_low := by
    rintro g hg k hk
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨v, hv⟩ := hg
    rw [← hv]
    exact blockHom_apply_not_block p a n v (by omega)
  trans := by
    intro x y hx hx' hy hy'
    let vx := (blockEquiv p a n).symm ⟨x, hx, hx'⟩
    let vy := (blockEquiv p a n).symm ⟨y, hy, hy'⟩
    refine ⟨⟨blockHom p a n (vy * vx⁻¹), blockHom_mem_Sfin p a n _⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact ⟨vy * vx⁻¹, rfl⟩
    · show blockHom p a n (vy * vx⁻¹) x = y
      rw [blockHom_apply_block p a n _ ⟨hx, hx'⟩]
      show (blockEquiv p a n (vy * vx⁻¹ * vx)).1 = y
      rw [inv_mul_cancel_right, Equiv.apply_symm_apply]
  pgroup := by
    have h1 : IsPGroup p (ElemAb p a) := IsPGroup.of_card (card_elemAb p a)
    have h2 : IsPGroup p (blockHom p a n).range :=
      h1.of_surjective (blockHom p a n).rangeRestrict (blockHom p a n).rangeRestrict_surjective
    exact h2.comap_of_injective (Sfin (n + p ^ a)).subtype (Subgroup.subtype_injective _)

end ElemAb

end DegreeProfilesReview.ConcreteM5
