/-
Coordinator, 26 Sep 2026.  The interface between the two halves of the forcing proof of DCP
(R_referee/work/HALF_PROOF.md): Theorem A (FORCE, for the lexicographically first LIS) and
Theorem B (realisation, for ANY choice of longest increasing sets).

* Agent R proves   `force_exists`  : for every M a selection of LIS's with FORCE at all levels.
* Agent B proves   `dcpSq_of_force`: FORCE at levels ≤ b for a selection of LIS's gives realisation.
Both are stated here only as `Prop`s (definitions); nothing is assumed.
-/
import BLemmaL

set_option autoImplicit false

namespace ForceInterface
open Finset ClaudeDCP BLemmaL

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- `I` is a longest increasing (column) set of `w`, in the sense of `BLemmaL.IncOn`. -/
def IsLIS (w : Equiv.Perm α) (I : Finset α) : Prop :=
  IncOn w I ∧ ∀ J : Finset α, IncOn w J → J.card ≤ I.card

/-- **FORCE at level `c` for a selection `sel`**: an element of `Z_c` of the full board which
vanishes on every rook `ρ_w = rookOff w (sel w)` with `|sel w| + c = |α|` vanishes on all `c`-rooks. -/
def ForceAt (K : Type*) [CommRing K] (sel : Equiv.Perm α → Finset α) (c : ℕ) : Prop :=
  ∀ F : Finset (α × α) → K, ZB (univ : Finset α) univ c F →
    (∀ w : Equiv.Perm α, (sel w).card + c = Fintype.card α → F (rookOff w (sel w)) = 0) →
    ∀ ρ : Finset (α × α), OnBoard (univ : Finset α) univ ρ → ρ.card = c → F ρ = 0

/-- Target of Agent R (Theorem A of HALF_PROOF.md), for the square board `Fin M × Fin M`. -/
def ForceExists (K : Type*) [CommRing K] (M : ℕ) : Prop :=
  ∃ sel : Equiv.Perm (Fin M) → Finset (Fin M),
    (∀ w, IsLIS w (sel w)) ∧ ∀ c, c ≤ M → ForceAt K sel c

/-- Target of Agent B (Theorem B of HALF_PROOF.md): FORCE at every level `c ≤ b` for some LIS
selection implies realisability of every `F ∈ Z_b` on the full board. -/
def RealisationFromForce (K : Type*) [CommRing K] (M : ℕ) : Prop :=
  ∀ (sel : Equiv.Perm (Fin M) → Finset (Fin M)), (∀ w, IsLIS w (sel w)) →
    ∀ b : ℕ, (∀ c, c ≤ b → c ≤ M → ForceAt K sel c) →
      ∀ F : Finset (Fin M × Fin M) → K, ZB (univ : Finset (Fin M)) univ b F →
        Real (univ : Finset (Fin M)) univ b F

end ForceInterface
