/-
Agent D, round 4 (26 Sep 2026).  The canonical form of the open statement.

`HALFSq K b M` : on the full board `Fin M × Fin M`, every `F ∈ Z_b` that vanishes on all rooks
meeting a given row `x0` is the rook function of an element of `K[S_M]`.

`half_of_halfSq` : `HALFSq K b M` implies `HALF α K b M` for every finite label type `α` (every
`M × M` sub-board), by relabelling along bijections `Fin M ≃ R`, `Fin M ≃ C`.
-/
import DCPRook
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ClaudeDCP

open Finset Function

variable (K : Type*) [CommRing K]

/-- **The OPEN statement, canonical form** (needed only for `b + 2 ≤ M ≤ 2b - 1`, so `b ≥ 3`):
every element of `Z_b` of the full board `Fin M × Fin M` vanishing on the rooks that meet a row
`x0` is realisable by `K[S_M]`. -/
def HALFSq (b M : ℕ) : Prop :=
  ∀ x0 : Fin M, ∀ F : Finset (Fin M × Fin M) → K, ZB (univ : Finset (Fin M)) univ b F →
    (∀ ρ, OnBoard (univ : Finset (Fin M)) univ ρ → ρ.card = b → x0 ∈ rowsOf ρ → F ρ = 0) →
    Real (univ : Finset (Fin M)) univ b F

variable {K}
variable {α : Type*} [Fintype α] [DecidableEq α]

section Relabel

variable {M : ℕ} (fR fC : Fin M → α)

/-- The cell map `(i, j) ↦ (fR i, fC j)`. -/
def cellMap (p : Fin M × Fin M) : α × α := (fR p.1, fC p.2)

variable {fR fC}

theorem cellMap_injective (hR : Injective fR) (hC : Injective fC) : Injective (cellMap fR fC) :=
  fun p q h => Prod.ext (hR (Prod.mk.inj h).1) (hC (Prod.mk.inj h).2)

theorem rowsOf_image (ρ : Finset (Fin M × Fin M)) :
    rowsOf (ρ.image (cellMap fR fC)) = (rowsOf ρ).image fR := by
  unfold rowsOf
  rw [Finset.image_image, Finset.image_image]
  rfl

theorem colsOf_image (ρ : Finset (Fin M × Fin M)) :
    colsOf (ρ.image (cellMap fR fC)) = (colsOf ρ).image fC := by
  unfold colsOf
  rw [Finset.image_image, Finset.image_image]
  rfl

theorem onBoard_image {R C : Finset α} (hR : Injective fR) (hC : Injective fC)
    (hfR : ∀ i, fR i ∈ R) (hfC : ∀ j, fC j ∈ C) {ρ : Finset (Fin M × Fin M)}
    (hρ : IsRook ρ) : OnBoard R C (ρ.image (cellMap fR fC)) := by
  refine ⟨fun p hp q hq h => ?_, fun p hp => ?_⟩
  · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    congr 1
    refine hρ p' hp' q' hq' ?_
    rcases h with h | h
    · exact Or.inl (hR h)
    · exact Or.inr (hC h)
  · obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨hfR _, hfC _⟩

theorem image_insert_cell (ρ : Finset (Fin M × Fin M)) (x y : Fin M) :
    (insert (x, y) ρ).image (cellMap fR fC) = insert (fR x, fC y) (ρ.image (cellMap fR fC)) := by
  rw [Finset.image_insert]
  rfl

end Relabel

/-- Push a coefficient function forward along a map between permutation groups. -/
def pushH {β : Type*} [Fintype β] [DecidableEq β] (f : Equiv.Perm β → Equiv.Perm α)
    (c : Equiv.Perm β → K) : Equiv.Perm α → K :=
  fun w => ∑ v ∈ univ.filter (fun v => f v = w), c v

theorem realFn_pushH {β : Type*} [Fintype β] [DecidableEq β] (f : Equiv.Perm β → Equiv.Perm α)
    (c : Equiv.Perm β → K) (ρ : Finset (α × α)) :
    realFn (pushH f c) ρ = ∑ v, c v * chi (f v) ρ := by
  unfold realFn pushH
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise univ f (fun v => c v * chi (f v) ρ)]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hv).2]

/-- **Relabelling**: the canonical statement gives `HALF` on every sub-board. -/
theorem half_of_halfSq {b M : ℕ} (h : HALFSq K b M) : HALF α K b M := by
  intro R C hR hC x0 hx0 F hZ hvan
  -- bijections `Fin M ≃ R`, `Fin M ≃ C`
  have eR : Fin M ≃ {x // x ∈ R} := Fintype.equivOfCardEq (by simp [hR])
  have eC : Fin M ≃ {x // x ∈ C} := Fintype.equivOfCardEq (by simp [hC])
  set fR : Fin M → α := fun i => (eR i).1 with hfRdef
  set fC : Fin M → α := fun j => (eC j).1 with hfCdef
  have hfR : Injective fR := fun i j e => eR.injective (Subtype.ext e)
  have hfC : Injective fC := fun i j e => eC.injective (Subtype.ext e)
  have hfRm : ∀ i, fR i ∈ R := fun i => (eR i).2
  have hfCm : ∀ j, fC j ∈ C := fun j => (eC j).2
  have hfRs : ∀ x ∈ R, ∃ i, fR i = x := fun x hx => ⟨eR.symm ⟨x, hx⟩, by simp [hfRdef]⟩
  have hfCs : ∀ y ∈ C, ∃ j, fC j = y := fun y hy => ⟨eC.symm ⟨y, hy⟩, by simp [hfCdef]⟩
  set m := cellMap fR fC with hmdef
  have hm : Injective m := cellMap_injective hfR hfC
  -- pull back rooks of the board
  have hpull : ∀ σ : Finset (α × α), σ ⊆ R ×ˢ C →
      ∃ σ' : Finset (Fin M × Fin M), σ'.image m = σ := by
    intro σ hσ
    refine ⟨univ.filter (fun p => m p ∈ σ), ?_⟩
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hq
      obtain ⟨i, hi⟩ := hfRs q.1 (Finset.mem_product.mp (hσ hq)).1
      obtain ⟨j, hj⟩ := hfCs q.2 (Finset.mem_product.mp (hσ hq)).2
      have : m (i, j) = q := by rw [hmdef]; exact Prod.ext hi hj
      exact ⟨(i, j), by rw [this]; exact hq, this⟩
  have hrook_of : ∀ ρ : Finset (Fin M × Fin M), IsRook (ρ.image m) → IsRook ρ := by
    intro ρ hρ p hp q hq hpq
    refine hm (hρ _ (Finset.mem_image_of_mem m hp) _ (Finset.mem_image_of_mem m hq) ?_)
    rcases hpq with e | e
    · exact Or.inl (by simp [hmdef, cellMap, e])
    · exact Or.inr (by simp [hmdef, cellMap, e])
  have hcard : ∀ ρ : Finset (Fin M × Fin M), (ρ.image m).card = ρ.card :=
    fun ρ => Finset.card_image_of_injective ρ hm
  -- the relabelled function
  set F' : Finset (Fin M × Fin M) → K := fun ρ => F (ρ.image m) with hF'def
  have hsdiffC : ∀ ρ : Finset (Fin M × Fin M),
      ((univ : Finset (Fin M)) \ colsOf ρ).image fC = C \ colsOf (ρ.image m) := by
    intro ρ
    ext y
    rw [Finset.mem_image, Finset.mem_sdiff, hmdef, colsOf_image, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨hfCm j, ?_⟩
      rintro ⟨j', hj', e⟩
      exact (Finset.mem_sdiff.mp hj).2 (hfC e ▸ hj')
    · rintro ⟨hy, hyn⟩
      obtain ⟨j, rfl⟩ := hfCs y hy
      exact ⟨j, Finset.mem_sdiff.mpr ⟨mem_univ _, fun hj => hyn ⟨j, hj, rfl⟩⟩, rfl⟩
  have hsdiffR : ∀ ρ : Finset (Fin M × Fin M),
      ((univ : Finset (Fin M)) \ rowsOf ρ).image fR = R \ rowsOf (ρ.image m) := by
    intro ρ
    ext x
    rw [Finset.mem_image, Finset.mem_sdiff, hmdef, rowsOf_image, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨hfRm i, ?_⟩
      rintro ⟨i', hi', e⟩
      exact (Finset.mem_sdiff.mp hi).2 (hfR e ▸ hi')
    · rintro ⟨hx, hxn⟩
      obtain ⟨i, rfl⟩ := hfRs x hx
      exact ⟨i, Finset.mem_sdiff.mpr ⟨mem_univ _, fun hi => hxn ⟨i, hi, rfl⟩⟩, rfl⟩
  have hZ' : ZB (univ : Finset (Fin M)) univ b F' := by
    refine ⟨fun ρ hρ hc x _ hxr => ?_, fun ρ hρ hc y _ hyc => ?_⟩
    · have hon : OnBoard R C (ρ.image m) := onBoard_image hfR hfC hfRm hfCm hρ.1
      have hxr' : fR x ∉ rowsOf (ρ.image m) := by
        rw [hmdef, rowsOf_image]
        intro hx
        obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hx
        exact hxr (hfR e ▸ hi)
      have := hZ.1 _ hon (by rw [hcard, hc]) (fR x) (hfRm x) hxr'
      rw [← hsdiffC, Finset.sum_image (fun a _ b _ e => hfC e)] at this
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hF'def]
      rw [hmdef, image_insert_cell]
    · have hon : OnBoard R C (ρ.image m) := onBoard_image hfR hfC hfRm hfCm hρ.1
      have hyc' : fC y ∉ colsOf (ρ.image m) := by
        rw [hmdef, colsOf_image]
        intro hy
        obtain ⟨j, hj, e⟩ := Finset.mem_image.mp hy
        exact hyc (hfC e ▸ hj)
      have := hZ.2 _ hon (by rw [hcard, hc]) (fC y) (hfCm y) hyc'
      rw [← hsdiffR, Finset.sum_image (fun a _ b _ e => hfR e)] at this
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hF'def]
      rw [hmdef, image_insert_cell]
  obtain ⟨i0, hi0⟩ := hfRs x0 hx0
  have hvan' : ∀ ρ, OnBoard (univ : Finset (Fin M)) univ ρ → ρ.card = b → i0 ∈ rowsOf ρ →
      F' ρ = 0 := by
    intro ρ hρ hc hi
    refine hvan _ (onBoard_image hfR hfC hfRm hfCm hρ.1) (by rw [hcard, hc]) ?_
    rw [hmdef, rowsOf_image, ← hi0]
    exact Finset.mem_image_of_mem fR hi
  obtain ⟨c', -, hc'⟩ := h i0 F' hZ' hvan'
  -- lift permutations of `Fin M` to permutations of `α` fitting `(R, C)`
  let L : Equiv.Perm (Fin M) → Equiv.Perm α := fun w =>
    (eC.symm.trans (w.trans eR)).extendSubtype
  have hLapp : ∀ w j, L w (fC j) = fR (w j) := by
    intro w j
    show ((eC.symm.trans (w.trans eR)).extendSubtype) (eC j).1 = (eR (w j)).1
    rw [Equiv.extendSubtype_apply_of_mem _ _ (eC j).2]
    simp
  have hLfit : ∀ w, Fits R C (L w) := by
    intro w y
    constructor
    · intro hy
      by_contra hyC
      exact Equiv.extendSubtype_not_mem _ y hyC hy
    · intro hy
      exact Equiv.extendSubtype_mem _ y hy
  have hfit : FitsAll R C (pushH L c') := by
    intro w hw
    obtain ⟨v, hv, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    rw [← (Finset.mem_filter.mp hv).2]
    exact hLfit v
  refine ⟨pushH L c', hfit, fun σ hσ hc => ?_⟩
  obtain ⟨σ', rfl⟩ := hpull σ hσ.2
  have hσ' : OnBoard (univ : Finset (Fin M)) univ σ' :=
    ⟨hrook_of σ' hσ.1, fun p _ => Finset.mem_product.mpr ⟨mem_univ _, mem_univ _⟩⟩
  rw [realFn_pushH]
  have := hc' σ' hσ' (by rw [← hcard, hc])
  simp only [hF'def] at this
  rw [this, realFn]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  unfold chi
  have key : (∀ p ∈ σ'.image m, L w p.2 = p.1) ↔ (∀ p ∈ σ', w p.2 = p.1) := by
    constructor
    · intro h p hp
      have := h (m p) (Finset.mem_image_of_mem m hp)
      rw [hmdef] at this
      simp only [cellMap, hLapp] at this
      exact hfR this
    · intro h p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      rw [hmdef]
      simp only [cellMap, hLapp, h q hq]
  by_cases hk : ∀ p ∈ σ', w p.2 = p.1
  · rw [if_pos hk, if_pos (key.mpr hk)]
  · rw [if_neg hk, if_neg (fun h' => hk (key.mp h'))]

end ClaudeDCP
