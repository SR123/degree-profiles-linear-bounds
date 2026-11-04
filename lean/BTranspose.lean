/-
Agent B, round 3 (26 Sep 2026).  The transposition step of Cor. 6 of `work/TPRIME_PROOF.md`,
abstract form: (P1) and T′_soc for the ADJOINT operator `u'` give (P2) and T′_top for `u`.

Setting: `M` finite-dimensional with a symmetric nondegenerate bilinear form `B` (`W^⊥⊥ = W` is taken from the dual space,
`Subspace.dualAnnihilator_dualCoannihilator_eq`, and `B.toDual`) (in the
application: the dot product on `Fn`, `u' = uᵀ = (zᵀ)^(p-1)`); `P` (= `P_b(N)`) with a
self-adjoint idempotent `E` onto it (restriction to injective total tuples); `V' ≤ P`, `Soc ≤ P`
with `V' ⊥ Soc`, `Soc = V'^⊥ ∩ P` (`hSocChar`) and `V' = Soc^⊥ ∩ P` (`hLstar`).
* `P2_of_transpose`: (P1) for `u'` ⇒ (P2) for `u`  (`uV ∩ V' ⊆ uV'`), via `W^⊥⊥ = W`.
* `Ttop_of_transpose`: T′_soc for `u'` (a map `w'`) ⇒ T′_top for `u`, with `w_T = E ∘ w'ᵀ`,
  equivariant modulo `V'` for every `g` whose adjoint preserves `Soc` and commutes with `w'`.
Unconditional.
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

namespace BExact

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **(P2) from (P1) for the adjoint.** -/
theorem P2_of_transpose (B : LinearMap.BilinForm K M) (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (P V' Soc : Submodule K M) (E : Module.End K M)
    (hE1 : ∀ x ∈ P, E x = x) (hEP : ∀ x, E x ∈ P) (hEadj : ∀ x y, B (E x) y = B x (E y))
    (hV'P : V' ≤ P) (hSocChar : ∀ x ∈ P, (∀ v ∈ V', B v x = 0) → x ∈ Soc)
    (hperp : ∀ v ∈ V', ∀ s ∈ Soc, B v s = 0)
    (u u' : Module.End K M) (hadj : ∀ x y, B (u x) y = B x (u' y))
    (huP : ∀ x ∈ P, u x ∈ P) (hu'P : ∀ x ∈ P, u' x ∈ P)
    (hP1' : ∀ y ∈ P, u' y ∈ Soc → ∃ s ∈ Soc, u' y = u' s) :
    ∀ v ∈ P, u v ∈ V' → ∃ v' ∈ V', u v = u v' := by
  intro v hv huv
  set W := V'.map u
  have key : ∀ y, (∀ w ∈ W, B y w = 0) → B y (u v) = 0 := by
    intro y hy
    -- replace `y` by its `P`-part
    set y₁ := E y
    have hy₁ : ∀ v' ∈ V', B (u v') y₁ = 0 := by
      intro v' hv'
      have h := hy (u v') (Submodule.mem_map_of_mem hv')
      show B (u v') (E y) = 0
      rw [← hEadj, hE1 _ (huP _ (hV'P hv')), hsymm]
      exact h
    have hu'y₁ : u' y₁ ∈ Soc := hSocChar _ (hu'P _ (hEP y)) (fun v' hv' => by
      rw [← hadj]
      exact hy₁ v' hv')
    obtain ⟨s, hs, hus⟩ := hP1' y₁ (hEP y) hu'y₁
    have h1 : B y (u v) = B (u v) y₁ := by
      rw [hsymm]
      show B (u v) y = B (u v) (E y)
      rw [← hEadj, hE1 _ (huP _ hv)]
    have h2 : B (u v) y₁ = B (u v) s + B (u v) (y₁ - s) := by
      rw [map_sub, add_sub_cancel]
    rw [h1, h2, hperp _ huv s hs, zero_add, hadj, map_sub, hus, sub_self, map_zero]
  have hmem : u v ∈ W.dualAnnihilator.dualCoannihilator := by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have h := key ((B.toDual hnd).symm φ) (fun w hw => by
      rw [LinearMap.BilinForm.apply_toDual_symm_apply]
      exact hφ w hw)
    rwa [LinearMap.BilinForm.apply_toDual_symm_apply] at h
  rw [Subspace.dualAnnihilator_dualCoannihilator_eq] at hmem
  obtain ⟨v', hv', he⟩ := Submodule.mem_map.mp hmem
  exact ⟨v', hv', he.symm⟩

/-- **T′_top from T′_soc for the adjoint.** -/
theorem Ttop_of_transpose (B : LinearMap.BilinForm K M) (hnd : B.Nondegenerate)
    (P V' Soc : Submodule K M) (E : Module.End K M)
    (hE1 : ∀ x ∈ P, E x = x) (hEP : ∀ x, E x ∈ P) (hEadj : ∀ x y, B (E x) y = B x (E y))
    (hSocP : Soc ≤ P) (hLstar : ∀ x ∈ P, (∀ s ∈ Soc, B x s = 0) → x ∈ V')
    (hperp : ∀ v ∈ V', ∀ s ∈ Soc, B v s = 0)
    (u u' : Module.End K M) (hadj : ∀ x y, B (u x) y = B x (u' y))
    (huP : ∀ x ∈ P, u x ∈ P) (hu'P : ∀ x ∈ P, u' x ∈ P)
    (w' : Module.End K M) (hw'S : ∀ s ∈ Soc, w' s ∈ Soc)
    (hw'u : ∀ s ∈ Soc, u' (w' (u' s)) = u' s)
    (G : Set (Module.End K M)) (hGP : ∀ g ∈ G, ∀ x ∈ P, g x ∈ P)
    (hGadj : ∀ g ∈ G, ∃ g' : Module.End K M, (∀ x y, B (g x) y = B x (g' y)) ∧
      (∀ s ∈ Soc, g' s ∈ Soc) ∧ ∀ s ∈ Soc, g' (w' s) = w' (g' s)) :
    ∃ wT : Module.End K M, (∀ x, wT x ∈ P) ∧ (∀ v ∈ V', wT v ∈ V') ∧
      (∀ v ∈ P, u (wT (u v)) - u v ∈ V') ∧ (∀ g ∈ G, ∀ v ∈ P, g (wT v) - wT (g v) ∈ V') := by
  set wt := B.leftAdjointOfNondegenerate hnd w'
  have hwt : ∀ x y, B (wt x) y = B x (w' y) :=
    LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate B hnd w'
  refine ⟨E * wt, fun x => hEP _, fun v hv => ?_, fun v hv => ?_, fun g hg v hv => ?_⟩
  · refine hLstar _ (hEP _) fun s hs => ?_
    show B (E (wt v)) s = 0
    rw [hEadj, hE1 s (hSocP hs), hwt]
    exact hperp v hv _ (hw'S s hs)
  · refine hLstar _ (P.sub_mem (huP _ (hEP _)) (huP _ hv)) fun s hs => ?_
    show B (u (E (wt (u v))) - u v) s = 0
    rw [map_sub, LinearMap.sub_apply, hadj (E (wt (u v))) s, hEadj, hE1 _ (hu'P _ (hSocP hs)), hwt,
      hadj v (w' (u' s)), hw'u s hs, hadj v s, sub_self]
  · obtain ⟨g', hg'adj, hg'S, hg'w⟩ := hGadj g hg
    refine hLstar _ (P.sub_mem (hGP g hg _ (hEP _)) (hEP _)) fun s hs => ?_
    show B (g (E (wt v)) - E (wt (g v))) s = 0
    rw [map_sub, LinearMap.sub_apply, hg'adj, hEadj, hE1 _ (hSocP (hg'S s hs)), hwt, hEadj,
      hE1 _ (hSocP hs), hwt, hg'adj, hg'w s hs, sub_self]

/-- `V' = Soc^⊥ ∩ P` from `Soc = V'^⊥ ∩ P` (double perp, via the dual space). -/
theorem Lstar_of_SocChar (B : LinearMap.BilinForm K M) (hsymm : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) (P V' Soc : Submodule K M) (E : Module.End K M)
    (hE1 : ∀ x ∈ P, E x = x) (hEP : ∀ x, E x ∈ P) (hEadj : ∀ x y, B (E x) y = B x (E y))
    (hV'P : V' ≤ P) (hSocChar : ∀ x ∈ P, (∀ v ∈ V', B v x = 0) → x ∈ Soc) :
    ∀ x ∈ P, (∀ s ∈ Soc, B x s = 0) → x ∈ V' := by
  intro x hx hxS
  have hmem : x ∈ V'.dualAnnihilator.dualCoannihilator := by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    set y := (B.toDual hnd).symm φ
    have hy : ∀ v ∈ V', B y v = 0 := fun v hv => by
      rw [LinearMap.BilinForm.apply_toDual_symm_apply]
      exact hφ v hv
    have hEy : E y ∈ Soc := hSocChar _ (hEP y) fun v hv => by
      rw [← hEadj, hE1 v (hV'P hv), hsymm]
      exact hy v hv
    rw [← LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) φ x, hsymm, ← hE1 x hx,
      hEadj]
    exact hxS _ hEy
  rwa [Subspace.dualAnnihilator_dualCoannihilator_eq] at hmem

end BExact
