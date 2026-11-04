/-
Agent B, round 6 (26 Sep 2026).  **Theorem B (realisation)** of R's forcing proof
(R_referee/work/HALF_PROOF.md §6), on the interface `ForceInterface.lean` (copied verbatim from
shared/interface; md5 in work/lean_logs/copied_round6.md5).

Statement: if a selection `sel` of increasing column sets has FORCE at every level `c ≤ b`, then
every `F ∈ Z_b` of the full board is the rook function of an element of `K[S_α]`.

Proof (HALF_PROOF.md §6, with the lexicographic order of `BLemmaL` in place of R's `Φ`):
* **solve**: on `T = {w : |sel w| + b ≥ |α|}` prescribe `g w = F(ρ_w)` if `|sel w| + b = |α|` and
  `g w = 0` otherwise (`ρ_w = rookOff w (sel w)`); `lemmaL_solve_gen` (unitriangular system over any
  commutative ring) gives `a` with `realFn a ρ_w = g w` for all `w ∈ T`;
* **lower levels**: by induction on `k < b`, `realFn a` vanishes on all `k`-rooks: its line sums at
  level `k` are its values at level `k - 1` (D's `zb_realFn`, R's Lemma 2.1), so it lies in `Z_k`,
  and it vanishes on the `ρ_w` of level `k`; FORCE at level `k` finishes;
* **top level**: `realFn a - F ∈ Z_b` vanishes on the `ρ_w` of level `b`; FORCE at level `b`.

Only the `IncOn` half of `IsLIS` is used.

Main results:
* `realisation_of_force` (any finite linear order `α`, `b ≤ |α|`);
* **`realisationFromForce`** : `ForceInterface.RealisationFromForce K M` for every commutative
  ring `K` and every `M` (UNCONDITIONAL).
-/
import ForceInterface

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BRealise

open Finset ClaudeDCP BLemmaL ForceInterface

variable {K : Type*} [CommRing K]

/-- Every coefficient function is supported on permutations fitting the full board. -/
theorem fitsAll_univ {α : Type*} [Fintype α] [DecidableEq α] (c : Equiv.Perm α → K) :
    FitsAll (univ : Finset α) univ c :=
  fun _ _ y => by simp

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- **Theorem B (realisation), general form.**  If `sel w` is an increasing set of `w` for every
`w` and `sel` has FORCE at every level `c ≤ b`, where `b ≤ |α|`, then every `F ∈ Z_b` of the full
board `α × α` is realisable. -/
theorem realisation_of_force (sel : Equiv.Perm α → Finset α) (hsel : ∀ w, IncOn w (sel w))
    (b : ℕ) (hforce : ∀ c, c ≤ b → ForceAt K sel c)
    (F : Finset (α × α) → K) (hF : ZB (univ : Finset α) univ b F) :
    Real (univ : Finset α) univ b F := by
  classical
  -- the family `T` of permutations whose selected increasing set has size `≥ |α| - b`
  let T := {w : Equiv.Perm α // Fintype.card α ≤ (sel w).card + b}
  -- the prescribed values
  let g : T → K := fun w =>
    if (sel w.1).card + b = Fintype.card α then F (rookOff w.1 (sel w.1)) else 0
  obtain ⟨a, -, ha⟩ := lemmaL_solve_gen (K := K) (v := fun w : T => w.1)
    (I := fun w : T => sel w.1) Subtype.val_injective (fun w => hsel w.1) g
  have hval : ∀ w, Fintype.card α ≤ (sel w).card + b →
      realFn a (rookOff w (sel w)) =
        if (sel w).card + b = Fintype.card α then F (rookOff w (sel w)) else 0 :=
    fun w hw => ha ⟨w, hw⟩
  -- Step 2: the lower levels vanish
  have hlow : ∀ k, k < b → ∀ ρ, OnBoard (univ : Finset α) univ ρ → ρ.card = k →
      realFn a ρ = 0 := by
    intro k
    induction k with
    | zero =>
      intro hk ρ hρ hcard
      refine hforce 0 (Nat.zero_le _) (realFn a)
        (zb_realFn (fitsAll_univ a) fun _ _ h => absurd h (Nat.succ_ne_zero _)) ?_ ρ hρ hcard
      intro w hw
      rw [hval w (by omega)]
      exact if_neg (by omega)
    | succ k ih =>
      intro hk ρ hρ hcard
      refine hforce (k + 1) hk.le (realFn a)
        (zb_realFn (fitsAll_univ a) fun σ hσ h => ih (by omega) σ hσ (by omega)) ?_ ρ hρ hcard
      intro w hw
      rw [hval w (by omega)]
      exact if_neg (by omega)
  -- Step 3: the top level
  refine ⟨a, fitsAll_univ a, fun ρ hρ hcard => ?_⟩
  have hG : ZB (univ : Finset α) univ b (fun σ => realFn a σ - F σ) :=
    zb_sub (zb_realFn (fitsAll_univ a) fun σ hσ h => hlow σ.card (by omega) σ hσ rfl) hF
  have h0 := hforce b le_rfl (fun σ => realFn a σ - F σ) hG (fun w hw => by
    show realFn a (rookOff w (sel w)) - F (rookOff w (sel w)) = 0
    rw [hval w (by omega), if_pos hw, sub_self]) ρ hρ hcard
  exact (sub_eq_zero.mp h0).symm

variable (K) in
/-- **Theorem B on the interface** (UNCONDITIONAL): `RealisationFromForce K M` for every
commutative ring `K` and every `M`. -/
theorem realisationFromForce (M : ℕ) : RealisationFromForce K M := by
  intro sel hsel b hforce F hF
  by_cases hb : b ≤ M
  · exact realisation_of_force sel (fun w => (hsel w).1) b
      (fun c hc => hforce c hc (hc.trans hb)) F hF
  · refine ⟨0, fitsAll_univ 0, fun ρ hρ hcard => ?_⟩
    have h1 := card_le_of_onBoard hρ
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega

/-- The consequence used downstream: with a FORCE selection (`ForceExists`), every element of
`Z_b` of the full board `Fin M × Fin M` is realisable (DCP_b(M) on the full board). -/
theorem real_of_forceExists {M : ℕ} (H : ForceExists K M) (b : ℕ)
    (F : Finset (Fin M × Fin M) → K) (hF : ZB (univ : Finset (Fin M)) univ b F) :
    Real (univ : Finset (Fin M)) univ b F := by
  obtain ⟨sel, hsel, hforce⟩ := H
  exact realisationFromForce K M sel hsel b (fun c _ hcM => hforce c hcM) F hF

end BRealise
