/-
Agent R, round 6 (26 Sep 2026).  **Theorem A (FORCE)** of R_referee/work/HALF_PROOF.md in the
form of the round-6 interface `ForceInterface.ForceExists`: for every commutative ring `K` and
every `M`, the selection `w ↦ lexFirst w univ` (the lexicographically first longest increasing
set of columns) consists of longest increasing sets, and FORCE holds for it at every level
`c ≤ M`.  Proof: Theorem GP (`RForce.gp`) on the full board with no conditions.
-/
import RForceGP

set_option autoImplicit false

namespace RForce

open Finset ClaudeDCP BLemmaL

/-- The lexicographically first longest increasing set is a longest increasing set. -/
theorem isLIS_lexFirst {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (w : Equiv.Perm α) : ForceInterface.IsLIS w (lexFirst w univ) :=
  ⟨lexFirst_incOn w univ, fun J hJ => by
    rw [lexFirst_card]
    exact le_lisOn (Finset.subset_univ J) hJ⟩

/-- **Theorem A (FORCE)**, interface form. -/
theorem forceExists (K : Type*) [CommRing K] (M : ℕ) : ForceInterface.ForceExists K M := by
  refine ⟨fun w => lexFirst w univ, isLIS_lexFirst, fun c hc => ?_⟩
  intro F hZ hvan ρ hρ hcard
  have hM : (univ : Finset (Fin M)).card = M := by simp
  refine gp (α := Fin M) (K := K) M univ univ hM hM c (M - c) (by omega)
    (fun _ _ => False) (fun _ _ => False) F hZ ?_ ?_ ρ hρ hcard
  · intro w _ hL _
    apply hvan w
    rw [lexFirst_card, hL, Fintype.card_fin]
    omega
  · intro ρ _ _ hq
    rcases hq with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ <;> exact h.elim

end RForce
