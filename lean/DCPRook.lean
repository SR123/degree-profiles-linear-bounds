/-
Agent D, round 4 (26 Sep 2026).  The elementary part of the DCP induction, in rook language
(work/BDM_PLAN.md §§1, 3).

Setting: labels `α` (finite), the board `α × α` (first coordinate = row = output label, second =
column = input label), sub-boards `R × C` with `R C : Finset α`, and functions
`F : Finset (α × α) → K` on rook placements (only their values on rooks of the board matter).

* `OnBoard R C ρ`  : `ρ` is a rook placement inside `R × C`.
* `RowLines R C b F`, `ColLines R C b F` : every row (column) line through a `(b-1)`-rook of the
  board sums to zero; `ZB R C b F` : both (this is `Z_b` of the board, i.e.
  `Hom_{K S_b}(Top, Soc)` in rook form).
* `chi w ρ = [ρ ⊆ graph w]`, `realFn c = Σ_w c w • chi w` (the rook function of
  `Σ_w c_w w ∈ K S_α`), `Fits R C w` (`w` maps `C` onto `R`).
* `Real R C b F` : `F` agrees on the `b`-rooks of the board with some `realFn c`, `c` supported on
  permutations fitting the board.  `DCPR α K b N` : every `F ∈ Z_b` of every `N × N` sub-board is
  realisable (DCP_b(N) in rook form).
* `HALF α K b N` (the OPEN statement in the window `b + 2 ≤ N ≤ 2b - 1`): elements of `Z_b` that
  vanish on every rook meeting a fixed row are realisable.
* `ColSplit K R C k` : rook form of B's Lemma D on the column side (proved from `BExact.lemmaD`
  in `DCPBridge`).

Main results:
* `sum_col_realFn`, `sum_row_realFn` (F1), `realFn_eq_zero_below`, `zb_realFn` (F3);
* `ext_eq` (extension lemma (E), explicit form), `row_peel` ((P)), `col_peel` ((C));
* `dcpr_zero`, `dcpr_of_lt`, `half_small`, `dcpr_of_half`, `dcpr_step`;
* `dcpr_all` : `ColSplit` for all `2k+1 ≤ |C|` and `HALF` in the window give DCP_b(N) for all N;
  `dcpr_le_two` : for `b ≤ 2` no `HALF` is needed.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ClaudeDCP

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Rooks -/

/-- A rook placement: no two cells share a row or a column. -/
def IsRook (ρ : Finset (α × α)) : Prop :=
  ∀ p ∈ ρ, ∀ q ∈ ρ, (p.1 = q.1 ∨ p.2 = q.2) → p = q

/-- The rows used by `ρ`. -/
def rowsOf (ρ : Finset (α × α)) : Finset α := ρ.image Prod.fst

/-- The columns used by `ρ`. -/
def colsOf (ρ : Finset (α × α)) : Finset α := ρ.image Prod.snd

/-- `ρ` is a rook placement on the board `R × C`. -/
def OnBoard (R C : Finset α) (ρ : Finset (α × α)) : Prop := IsRook ρ ∧ ρ ⊆ R ×ˢ C

theorem mem_rowsOf {ρ : Finset (α × α)} {x : α} : x ∈ rowsOf ρ ↔ ∃ y, (x, y) ∈ ρ := by
  unfold rowsOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), hy, rfl⟩

theorem mem_colsOf {ρ : Finset (α × α)} {y : α} : y ∈ colsOf ρ ↔ ∃ x, (x, y) ∈ ρ := by
  unfold colsOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, hp⟩
  · rintro ⟨x, hx⟩
    exact ⟨(x, y), hx, rfl⟩

theorem rowsOf_mem {ρ : Finset (α × α)} {p : α × α} (hp : p ∈ ρ) : p.1 ∈ rowsOf ρ :=
  mem_rowsOf.mpr ⟨p.2, hp⟩

theorem colsOf_mem {ρ : Finset (α × α)} {p : α × α} (hp : p ∈ ρ) : p.2 ∈ colsOf ρ :=
  mem_colsOf.mpr ⟨p.1, hp⟩

theorem OnBoard.mono {R C R' C' : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ)
    (hR : R ⊆ R') (hC : C ⊆ C') : OnBoard R' C' ρ :=
  ⟨h.1, fun p hp => Finset.mem_product.mpr
    ⟨hR (Finset.mem_product.mp (h.2 hp)).1, hC (Finset.mem_product.mp (h.2 hp)).2⟩⟩

theorem OnBoard.row_mem {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) {p : α × α}
    (hp : p ∈ ρ) : p.1 ∈ R := (Finset.mem_product.mp (h.2 hp)).1

theorem OnBoard.col_mem {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) {p : α × α}
    (hp : p ∈ ρ) : p.2 ∈ C := (Finset.mem_product.mp (h.2 hp)).2

theorem OnBoard.erase {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) (p : α × α) :
    OnBoard R C (ρ.erase p) :=
  ⟨fun q hq r hr => h.1 q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr),
    fun q hq => h.2 (Finset.mem_of_mem_erase hq)⟩

theorem OnBoard.insert {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) {x y : α}
    (hx : x ∈ R) (hxr : x ∉ rowsOf ρ) (hy : y ∈ C) (hyc : y ∉ colsOf ρ) :
    OnBoard R C (insert (x, y) ρ) := by
  refine ⟨fun p hp q hq hpq => ?_, fun p hp => ?_⟩
  · rcases Finset.mem_insert.mp hp with rfl | hp' <;> rcases Finset.mem_insert.mp hq with rfl | hq'
    · rfl
    · rcases hpq with h1 | h1
      · exact absurd (by rw [show x = q.1 from h1]; exact rowsOf_mem hq') hxr
      · exact absurd (by rw [show y = q.2 from h1]; exact colsOf_mem hq') hyc
    · rcases hpq with h1 | h1
      · exact absurd (by rw [← show p.1 = x from h1]; exact rowsOf_mem hp') hxr
      · exact absurd (by rw [← show p.2 = y from h1]; exact colsOf_mem hp') hyc
    · exact h.1 p hp' q hq' hpq
  · rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact Finset.mem_product.mpr ⟨hx, hy⟩
    · exact h.2 hp'

theorem card_insert_cell {ρ : Finset (α × α)} {x y : α} (hxr : x ∉ rowsOf ρ) :
    (insert (x, y) ρ).card = ρ.card + 1 :=
  Finset.card_insert_of_notMem (fun h => hxr (rowsOf_mem h))

theorem rowsOf_insert (ρ : Finset (α × α)) (p : α × α) :
    rowsOf (insert p ρ) = insert p.1 (rowsOf ρ) := by
  unfold rowsOf
  rw [Finset.image_insert]

theorem colsOf_insert (ρ : Finset (α × α)) (p : α × α) :
    colsOf (insert p ρ) = insert p.2 (colsOf ρ) := by
  unfold colsOf
  rw [Finset.image_insert]

/-- In a rook, the other cells avoid the row and the column of a cell. -/
theorem not_mem_rowsOf_erase {ρ : Finset (α × α)} (hρ : IsRook ρ) {p : α × α} (hp : p ∈ ρ) :
    p.1 ∉ rowsOf (ρ.erase p) := by
  intro h
  obtain ⟨y, hy⟩ := mem_rowsOf.mp h
  have h1 := hρ _ (Finset.mem_of_mem_erase hy) p hp (Or.inl rfl)
  exact (Finset.ne_of_mem_erase hy) h1

theorem not_mem_colsOf_erase {ρ : Finset (α × α)} (hρ : IsRook ρ) {p : α × α} (hp : p ∈ ρ) :
    p.2 ∉ colsOf (ρ.erase p) := by
  intro h
  obtain ⟨x, hx⟩ := mem_colsOf.mp h
  have h1 := hρ _ (Finset.mem_of_mem_erase hx) p hp (Or.inr rfl)
  exact (Finset.ne_of_mem_erase hx) h1

theorem card_erase_add_one {ρ : Finset (α × α)} {p : α × α} (hp : p ∈ ρ) :
    (ρ.erase p).card + 1 = ρ.card := Finset.card_erase_add_one hp

theorem rook_eq_of_row {ρ : Finset (α × α)} (hρ : IsRook ρ) {x y y' : α} (h : (x, y) ∈ ρ)
    (h' : (x, y') ∈ ρ) : y = y' := by
  have := hρ _ h _ h' (Or.inl rfl)
  exact (Prod.mk.inj this).2

theorem rook_eq_of_col {ρ : Finset (α × α)} (hρ : IsRook ρ) {x x' y : α} (h : (x, y) ∈ ρ)
    (h' : (x', y) ∈ ρ) : x = x' := by
  have := hρ _ h _ h' (Or.inr rfl)
  exact (Prod.mk.inj this).1

theorem card_rowsOf {ρ : Finset (α × α)} (hρ : IsRook ρ) : (rowsOf ρ).card = ρ.card :=
  Finset.card_image_of_injOn fun p hp q hq h => hρ p hp q hq (Or.inl h)

theorem card_colsOf {ρ : Finset (α × α)} (hρ : IsRook ρ) : (colsOf ρ).card = ρ.card :=
  Finset.card_image_of_injOn fun p hp q hq h => hρ p hp q hq (Or.inr h)

theorem rowsOf_subset {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) :
    rowsOf ρ ⊆ R := fun x hx => by
  obtain ⟨y, hy⟩ := mem_rowsOf.mp hx
  exact h.row_mem hy

theorem colsOf_subset {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) :
    colsOf ρ ⊆ C := fun y hy => by
  obtain ⟨x, hx⟩ := mem_colsOf.mp hy
  exact h.col_mem hx

theorem card_le_of_onBoard {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) :
    ρ.card ≤ R.card := by
  rw [← card_rowsOf h.1]
  exact Finset.card_le_card (rowsOf_subset h)

theorem card_le_of_onBoard' {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) :
    ρ.card ≤ C.card := by
  rw [← card_colsOf h.1]
  exact Finset.card_le_card (colsOf_subset h)

/-- A cell outside a sub-board `R' × C'` of `R × C`. -/
theorem exists_out {R C R' C' : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ)
    (hn : ¬ ρ ⊆ R' ×ˢ C') : ∃ p ∈ ρ, p.1 ∉ R' ∨ p.2 ∉ C' := by
  by_contra hc
  push_neg at hc
  exact hn fun p hp => Finset.mem_product.mpr (hc p hp)

/-- Removing a cell `(x0, y0)` of a rook on `(insert x0 R) × (insert y0 C)` lands in `R × C`. -/
theorem erase_sub {R C : Finset α} {x0 y0 : α} {ρ : Finset (α × α)}
    (h : OnBoard (insert x0 R) (insert y0 C) ρ) (hp : (x0, y0) ∈ ρ) :
    ρ.erase (x0, y0) ⊆ R ×ˢ C := by
  intro q hq
  have hq' := Finset.mem_of_mem_erase hq
  have hne := Finset.ne_of_mem_erase hq
  have hq1 : q.1 ≠ x0 := fun e => hne (h.1 q hq' _ hp (Or.inl e))
  have hq2 : q.2 ≠ y0 := fun e => hne (h.1 q hq' _ hp (Or.inr e))
  have hR := h.row_mem hq'
  have hC := h.col_mem hq'
  rw [Finset.mem_insert] at hR hC
  exact Finset.mem_product.mpr ⟨hR.resolve_left hq1, hC.resolve_left hq2⟩

/-- A rook of `(insert x0 R) × (insert y0 C)` avoiding row `x0` and column `y0` lies in `R × C`. -/
theorem sub_of_avoid {R C : Finset α} {x0 y0 : α} {ρ : Finset (α × α)}
    (h : OnBoard (insert x0 R) (insert y0 C) ρ) (hx : x0 ∉ rowsOf ρ) (hy : y0 ∉ colsOf ρ) :
    ρ ⊆ R ×ˢ C := by
  intro q hq
  have hR := h.row_mem hq
  have hC := h.col_mem hq
  rw [Finset.mem_insert] at hR hC
  exact Finset.mem_product.mpr
    ⟨hR.resolve_left fun e => hx (e ▸ rowsOf_mem hq),
      hC.resolve_left fun e => hy (e ▸ colsOf_mem hq)⟩

theorem OnBoard.erase_col {R C : Finset α} {σ : Finset (α × α)} (h : OnBoard R C σ) {y0 : α}
    (hy : y0 ∉ colsOf σ) : OnBoard R (C.erase y0) σ :=
  ⟨h.1, fun q hq => Finset.mem_product.mpr ⟨h.row_mem hq,
    Finset.mem_erase.mpr ⟨fun e => hy (e ▸ colsOf_mem hq), h.col_mem hq⟩⟩⟩

theorem OnBoard.erase_row {R C : Finset α} {σ : Finset (α × α)} (h : OnBoard R C σ) {x0 : α}
    (hx : x0 ∉ rowsOf σ) : OnBoard (R.erase x0) C σ :=
  ⟨h.1, fun q hq => Finset.mem_product.mpr
    ⟨Finset.mem_erase.mpr ⟨fun e => hx (e ▸ rowsOf_mem hq), h.row_mem hq⟩, h.col_mem hq⟩⟩

/-! ### Lines, zero-balanced functions, realisers -/

variable {K : Type*} [CommRing K]

/-- Every row line through a `(b-1)`-rook of the board sums to zero. -/
def RowLines (R C : Finset α) (b : ℕ) (F : Finset (α × α) → K) : Prop :=
  ∀ ρ, OnBoard R C ρ → ρ.card + 1 = b → ∀ x ∈ R, x ∉ rowsOf ρ →
    ∑ y ∈ C \ colsOf ρ, F (insert (x, y) ρ) = 0

/-- Every column line through a `(b-1)`-rook of the board sums to zero. -/
def ColLines (R C : Finset α) (b : ℕ) (F : Finset (α × α) → K) : Prop :=
  ∀ ρ, OnBoard R C ρ → ρ.card + 1 = b → ∀ y ∈ C, y ∉ colsOf ρ →
    ∑ x ∈ R \ rowsOf ρ, F (insert (x, y) ρ) = 0

/-- `Z_b` of the board `R × C`. -/
def ZB (R C : Finset α) (b : ℕ) (F : Finset (α × α) → K) : Prop :=
  RowLines R C b F ∧ ColLines R C b F

/-- `[ρ ⊆ graph w]`, `graph w = {(w y, y)}`. -/
def chi (w : Equiv.Perm α) (ρ : Finset (α × α)) : K :=
  if ∀ p ∈ ρ, w p.2 = p.1 then 1 else 0

/-- The rook function of `Σ_w c_w w`. -/
def realFn (c : Equiv.Perm α → K) (ρ : Finset (α × α)) : K := ∑ w, c w * chi w ρ

/-- `w` maps `C` onto `R`. -/
def Fits (R C : Finset α) (w : Equiv.Perm α) : Prop := ∀ y, w y ∈ R ↔ y ∈ C

/-- `c` is supported on permutations fitting the board. -/
def FitsAll (R C : Finset α) (c : Equiv.Perm α → K) : Prop := ∀ w, c w ≠ 0 → Fits R C w

/-- `F` is realisable at level `b` on the board `R × C`. -/
def Real (R C : Finset α) (b : ℕ) (F : Finset (α × α) → K) : Prop :=
  ∃ c : Equiv.Perm α → K, FitsAll R C c ∧ ∀ ρ, OnBoard R C ρ → ρ.card = b → F ρ = realFn c ρ

variable (α K) in
/-- **DCP_b(N) in rook form**: `Z_b` of every `N × N` sub-board is realisable. -/
def DCPR (b N : ℕ) : Prop :=
  ∀ R C : Finset α, R.card = N → C.card = N → ∀ F : Finset (α × α) → K, ZB R C b F →
    Real R C b F

variable (α K) in
/-- **The OPEN statement HALF_b(N)** (needed only in the window `b + 2 ≤ N ≤ 2b - 1`): every
element of `Z_b(N)` vanishing on all rooks that meet a given row is realisable. -/
def HALF (b N : ℕ) : Prop :=
  ∀ R C : Finset α, R.card = N → C.card = N → ∀ x0 ∈ R, ∀ F : Finset (α × α) → K, ZB R C b F →
    (∀ ρ, OnBoard R C ρ → ρ.card = b → x0 ∈ rowsOf ρ → F ρ = 0) → Real R C b F

variable (K) in
/-- **Rook form of Lemma D on the column side** at level `k` for the board `R × C`: linear maps
`Pi y` (`y ∈ C`), local on the board, which on functions with vanishing row lines give a
decomposition `Σ_y Pi y F = F` into pieces vanishing on column `y`, keeping the line conditions
and the vanishing on any row. -/
def ColSplit (R C : Finset α) (k : ℕ) : Prop :=
  ∃ Pi : α → (Finset (α × α) → K) →ₗ[K] (Finset (α × α) → K),
    (∀ F : Finset (α × α) → K, (∀ ρ, OnBoard R C ρ → ρ.card = k → F ρ = 0) →
      ∀ y ρ, OnBoard R C ρ → ρ.card = k → Pi y F ρ = 0) ∧
    ∀ F : Finset (α × α) → K, RowLines R C k F →
      (∀ ρ, OnBoard R C ρ → ρ.card = k → ∑ y ∈ C, Pi y F ρ = F ρ) ∧
      (∀ y ∈ C, RowLines R C k (Pi y F)) ∧
      (∀ y ∈ C, ColLines R C k F → ColLines R C k (Pi y F)) ∧
      (∀ y ∈ C, ∀ ρ, OnBoard R C ρ → ρ.card = k → y ∈ colsOf ρ → Pi y F ρ = 0) ∧
      (∀ y ∈ C, ∀ x, (∀ ρ, OnBoard R C ρ → ρ.card = k → x ∈ rowsOf ρ → F ρ = 0) →
        ∀ ρ, OnBoard R C ρ → ρ.card = k → x ∈ rowsOf ρ → Pi y F ρ = 0)

/-! ### (F1): line sums of permutation rook functions -/

theorem chi_insert (w : Equiv.Perm α) (x y : α) (ρ : Finset (α × α)) :
    chi (K := K) w (insert (x, y) ρ) = if w y = x then chi w ρ else 0 := by
  unfold chi
  simp only [Finset.forall_mem_insert]
  by_cases h : w y = x <;> simp [h]

theorem chi_empty (w : Equiv.Perm α) : chi (K := K) w ∅ = 1 := by
  simp [chi]

theorem sum_col_chi {R C : Finset α} {w : Equiv.Perm α} (hw : Fits R C w) {ρ : Finset (α × α)}
    {y : α} (hy : y ∈ C) (hyc : y ∉ colsOf ρ) :
    ∑ x ∈ R \ rowsOf ρ, chi (K := K) w (insert (x, y) ρ) = chi w ρ := by
  simp_rw [chi_insert]
  rw [Finset.sum_ite_eq]
  by_cases hc : ∀ p ∈ ρ, w p.2 = p.1
  · have hmem : w y ∈ R \ rowsOf ρ := by
      refine Finset.mem_sdiff.mpr ⟨(hw y).mpr hy, fun h => hyc ?_⟩
      obtain ⟨y', hy'⟩ := mem_rowsOf.mp h
      have h1 : w y' = w y := hc _ hy'
      rw [w.injective h1] at hy'
      exact colsOf_mem hy'
    rw [if_pos hmem]
  · have h0 : chi (K := K) w ρ = 0 := if_neg hc
    rw [h0]
    simp

theorem sum_row_chi {R C : Finset α} {w : Equiv.Perm α} (hw : Fits R C w) {ρ : Finset (α × α)}
    {x : α} (hx : x ∈ R) (hxr : x ∉ rowsOf ρ) :
    ∑ y ∈ C \ colsOf ρ, chi (K := K) w (insert (x, y) ρ) = chi w ρ := by
  simp_rw [chi_insert, Equiv.apply_eq_iff_eq_symm_apply]
  rw [Finset.sum_ite_eq']
  by_cases hc : ∀ p ∈ ρ, w p.2 = p.1
  · have hmem : w.symm x ∈ C \ colsOf ρ := by
      refine Finset.mem_sdiff.mpr ⟨(hw _).mp (by simpa using hx), fun h => hxr ?_⟩
      obtain ⟨x', hx'⟩ := mem_colsOf.mp h
      have h1 : w (w.symm x) = x' := hc _ hx'
      rw [Equiv.apply_symm_apply] at h1
      rw [h1]
      exact rowsOf_mem hx'
    rw [if_pos hmem]
  · have h0 : chi (K := K) w ρ = 0 := if_neg hc
    rw [h0]
    simp

theorem sum_col_realFn {R C : Finset α} {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    {ρ : Finset (α × α)} {y : α} (hy : y ∈ C) (hyc : y ∉ colsOf ρ) :
    ∑ x ∈ R \ rowsOf ρ, realFn c (insert (x, y) ρ) = realFn c ρ := by
  unfold realFn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.mul_sum]
  by_cases h0 : c w = 0
  · simp [h0]
  · rw [sum_col_chi (hc w h0) hy hyc]

theorem sum_row_realFn {R C : Finset α} {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    {ρ : Finset (α × α)} {x : α} (hx : x ∈ R) (hxr : x ∉ rowsOf ρ) :
    ∑ y ∈ C \ colsOf ρ, realFn c (insert (x, y) ρ) = realFn c ρ := by
  unfold realFn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.mul_sum]
  by_cases h0 : c w = 0
  · simp [h0]
  · rw [sum_row_chi (hc w h0) hx hxr]

/-! ### Linearity of realisers -/

theorem realFn_add (c d : Equiv.Perm α → K) (ρ : Finset (α × α)) :
    realFn (c + d) ρ = realFn c ρ + realFn d ρ := by
  simp only [realFn, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem realFn_sum {β : Type*} (s : Finset β) (c : β → Equiv.Perm α → K) (ρ : Finset (α × α)) :
    realFn (∑ i ∈ s, c i) ρ = ∑ i ∈ s, realFn (c i) ρ := by
  simp only [realFn, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem realFn_zero (ρ : Finset (α × α)) : realFn (0 : Equiv.Perm α → K) ρ = 0 := by
  simp [realFn]

theorem fitsAll_zero (R C : Finset α) : FitsAll R C (0 : Equiv.Perm α → K) :=
  fun w h => absurd rfl h

theorem fitsAll_add {R C : Finset α} {c d : Equiv.Perm α → K} (hc : FitsAll R C c)
    (hd : FitsAll R C d) : FitsAll R C (c + d) := by
  intro w hw
  by_cases h : c w = 0
  · refine hd w fun h' => hw ?_
    simp [h, h']
  · exact hc w h

theorem fitsAll_sum {β : Type*} (s : Finset β) {R C : Finset α} {c : β → Equiv.Perm α → K}
    (hc : ∀ i ∈ s, FitsAll R C (c i)) : FitsAll R C (∑ i ∈ s, c i) := by
  intro w hw
  rw [Finset.sum_apply] at hw
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  exact hc i hi w hne

/-! ### (F3) and lower levels -/

/-- If `F ∈ Z_b` (column lines suffice) is realised by `c` at level `b`, then `realFn c`
vanishes on the `(b-1)`-rooks of the board that have a free column. -/
theorem realFn_eq_zero_below {R C : Finset α} {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    {b : ℕ} {F : Finset (α × α) → K} (hF : ∀ ρ, OnBoard R C ρ → ρ.card = b → F ρ = realFn c ρ)
    (hZ : ColLines R C b F) {ρ : Finset (α × α)} (hρ : OnBoard R C ρ) (hcard : ρ.card + 1 = b)
    (hC : ρ.card < C.card) : realFn c ρ = 0 := by
  have hlt : (colsOf ρ).card < C.card := by rw [card_colsOf hρ.1]; exact hC
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [← sum_col_realFn hc hy hyc, ← hZ ρ hρ hcard y hy hyc]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxR, hxr⟩ := Finset.mem_sdiff.mp hx
  rw [hF _ (hρ.insert hxR hxr hy hyc) (by rw [card_insert_cell hxr, hcard])]

/-- A realiser vanishing at level `b - 1` gives an element of `Z_b`. -/
theorem zb_realFn {R C : Finset α} {c : Equiv.Perm α → K} (hc : FitsAll R C c) {b : ℕ}
    (h0 : ∀ ρ, OnBoard R C ρ → ρ.card + 1 = b → realFn c ρ = 0) : ZB R C b (realFn c) :=
  ⟨fun ρ hρ hcard x hx hxr => by rw [sum_row_realFn hc hx hxr, h0 ρ hρ hcard],
    fun ρ hρ hcard y hy hyc => by rw [sum_col_realFn hc hy hyc, h0 ρ hρ hcard]⟩

theorem zb_sub {R C : Finset α} {b : ℕ} {F G : Finset (α × α) → K} (hF : ZB R C b F)
    (hG : ZB R C b G) : ZB R C b (fun ρ => F ρ - G ρ) :=
  ⟨fun ρ hρ hcard x hx hxr => by
      rw [Finset.sum_sub_distrib, hF.1 ρ hρ hcard x hx hxr, hG.1 ρ hρ hcard x hx hxr, sub_zero],
    fun ρ hρ hcard y hy hyc => by
      rw [Finset.sum_sub_distrib, hF.2 ρ hρ hcard y hy hyc, hG.2 ρ hρ hcard y hy hyc, sub_zero]⟩

/-- Restriction to a sub-board, for functions vanishing off it. -/
theorem zb_mono {R C R' C' : Finset α} (hR : R' ⊆ R) (hC : C' ⊆ C) {b : ℕ}
    {F : Finset (α × α) → K} (hF : ZB R C b F)
    (hvan : ∀ ρ, OnBoard R C ρ → ρ.card = b → ¬ ρ ⊆ R' ×ˢ C' → F ρ = 0) : ZB R' C' b F := by
  refine ⟨fun ρ hρ hcard x hx hxr => ?_, fun ρ hρ hcard y hy hyc => ?_⟩
  · have hρ' := hρ.mono hR hC
    rw [← hF.1 ρ hρ' hcard x (hR hx) hxr]
    refine Finset.sum_subset (Finset.sdiff_subset_sdiff hC (Finset.Subset.refl _)) fun y hy hy' => ?_
    obtain ⟨hyC, hyc⟩ := Finset.mem_sdiff.mp hy
    have hyC' : y ∉ C' := fun h => hy' (Finset.mem_sdiff.mpr ⟨h, hyc⟩)
    refine hvan _ (hρ'.insert (hR hx) hxr hyC hyc) (by rw [card_insert_cell hxr, hcard]) ?_
    intro hs
    exact hyC' (Finset.mem_product.mp (hs (Finset.mem_insert_self _ _))).2
  · have hρ' := hρ.mono hR hC
    rw [← hF.2 ρ hρ' hcard y (hC hy) hyc]
    refine Finset.sum_subset (Finset.sdiff_subset_sdiff hR (Finset.Subset.refl _)) fun x hx hx' => ?_
    obtain ⟨hxR, hxr⟩ := Finset.mem_sdiff.mp hx
    have hxR' : x ∉ R' := fun h => hx' (Finset.mem_sdiff.mpr ⟨h, hxr⟩)
    refine hvan _ (hρ'.insert hxR hxr (hC hy) hyc) (by rw [card_insert_cell hxr, hcard]) ?_
    intro hs
    exact hxR' (Finset.mem_product.mp (hs (Finset.mem_insert_self _ _))).1

theorem real_of_sub {R C : Finset α} {b : ℕ} {F : Finset (α × α) → K} {c : Equiv.Perm α → K}
    (hc : FitsAll R C c) (h : Real R C b (fun ρ => F ρ - realFn c ρ)) : Real R C b F := by
  obtain ⟨d, hd, hdF⟩ := h
  refine ⟨d + c, fitsAll_add hd hc, fun ρ hρ hcard => ?_⟩
  rw [realFn_add, ← hdF ρ hρ hcard, sub_add_cancel]

/-! ### Extension of realisers (E) -/

/-- Extend `v` by `y0 ↦ x0` (a permutation agreeing with `v` off `y0` and `v⁻¹ x0`). -/
def extP (x0 y0 : α) (v : Equiv.Perm α) : Equiv.Perm α := Equiv.swap x0 (v y0) * v

theorem extP_apply_self (x0 y0 : α) (v : Equiv.Perm α) : extP x0 y0 v y0 = x0 := by
  simp [extP, Equiv.swap_apply_right]

theorem extP_apply_of {x0 y0 : α} {v : Equiv.Perm α} {y : α} (hy : y ≠ y0) (hvy : v y ≠ x0) :
    extP x0 y0 v y = v y := by
  simp only [extP, Equiv.Perm.mul_apply]
  exact Equiv.swap_apply_of_ne_of_ne hvy fun h => hy (v.injective h)

theorem fits_extP {R C : Finset α} {v : Equiv.Perm α} (hv : Fits R C v) {x0 y0 : α}
    (hx0 : x0 ∉ R) (hy0 : y0 ∉ C) : Fits (insert x0 R) (insert y0 C) (extP x0 y0 v) := by
  intro y
  by_cases hy : y = y0
  · subst hy
    simp [extP_apply_self]
  · have hvy0 : v y0 ∉ R := fun h => hy0 ((hv y0).mp h)
    by_cases hvy : v y = x0
    · have h1 : extP x0 y0 v y = v y0 := by
        simp only [extP, Equiv.Perm.mul_apply, hvy, Equiv.swap_apply_left]
      rw [h1]
      have hne : v y0 ≠ x0 := fun h => hy (v.injective (h.trans hvy.symm)).symm
      have hyC : y ∉ C := fun h => hx0 (hvy ▸ (hv y).mpr h)
      simp [hne, hvy0, hy, hyC]
    · rw [extP_apply_of hy hvy]
      simp only [Finset.mem_insert, hvy, hy, false_or]
      exact hv y

/-- Push a coefficient function forward along a map of permutations. -/
def push (f : Equiv.Perm α → Equiv.Perm α) (c : Equiv.Perm α → K) : Equiv.Perm α → K :=
  fun w => ∑ v ∈ univ.filter (fun v => f v = w), c v

theorem realFn_push (f : Equiv.Perm α → Equiv.Perm α) (c : Equiv.Perm α → K)
    (ρ : Finset (α × α)) : realFn (push f c) ρ = ∑ v, c v * chi (f v) ρ := by
  unfold realFn push
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise univ f (fun v => c v * chi (f v) ρ)]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hv).2]

theorem fitsAll_push {R C R' C' : Finset α} {f : Equiv.Perm α → Equiv.Perm α}
    {c : Equiv.Perm α → K} (hc : FitsAll R C c) (hf : ∀ v, Fits R C v → Fits R' C' (f v)) :
    FitsAll R' C' (push f c) := by
  intro w hw
  obtain ⟨v, hv, hcv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  rw [← (Finset.mem_filter.mp hv).2]
  exact hf v (hc v hcv)

theorem fitsAll_push_extP {R C : Finset α} {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    {x0 y0 : α} (hx0 : x0 ∉ R) (hy0 : y0 ∉ C) :
    FitsAll (insert x0 R) (insert y0 C) (push (extP x0 y0) c) :=
  fitsAll_push hc fun _ hv => fits_extP hv hx0 hy0

theorem chi_extP_of_sub {R C : Finset α} {v : Equiv.Perm α} (hv : Fits R C v) {x0 y0 : α}
    (hx0 : x0 ∉ R) (hy0 : y0 ∉ C) {ρ : Finset (α × α)} (hρ : ρ ⊆ R ×ˢ C) :
    chi (K := K) (extP x0 y0 v) ρ = chi v ρ := by
  have key : ∀ p ∈ ρ, extP x0 y0 v p.2 = v p.2 := by
    intro p hp
    have hpC : p.2 ∈ C := (Finset.mem_product.mp (hρ hp)).2
    exact extP_apply_of (fun h => hy0 (h ▸ hpC)) (fun h => hx0 (h ▸ (hv p.2).mpr hpC))
  unfold chi
  by_cases h : ∀ p ∈ ρ, v p.2 = p.1
  · rw [if_pos h, if_pos (fun p hp => (key p hp).trans (h p hp))]
  · rw [if_neg h, if_neg (fun h' => h (fun p hp => (key p hp).symm.trans (h' p hp)))]

theorem chi_extP_zero {R C : Finset α} {x0 y0 : α} {ρ : Finset (α × α)}
    (hρ : OnBoard (insert x0 R) (insert y0 C) ρ) (hp : (x0, y0) ∉ ρ) (hn : ¬ ρ ⊆ R ×ˢ C)
    (v : Equiv.Perm α) : chi (K := K) (extP x0 y0 v) ρ = 0 := by
  obtain ⟨p, hpρ, hout⟩ := exists_out hρ hn
  unfold chi
  rw [if_neg]
  intro hall
  have h1 := hall p hpρ
  have hR := hρ.row_mem hpρ
  have hC := hρ.col_mem hpρ
  rw [Finset.mem_insert] at hR hC
  have hp2 : p.2 = y0 := by
    rcases hout with h | h
    · have hx : p.1 = x0 := hR.resolve_right h
      exact (extP x0 y0 v).injective (h1.trans (hx.trans (extP_apply_self x0 y0 v).symm))
    · exact hC.resolve_right h
  have hp1 : p.1 = x0 := by rw [← h1, hp2, extP_apply_self]
  exact hp (by rw [← hp1, ← hp2]; exact hpρ)

theorem realFn_push_extP_of_sub {R C : Finset α} {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    {x0 y0 : α} (hx0 : x0 ∉ R) (hy0 : y0 ∉ C) {ρ : Finset (α × α)} (hρ : ρ ⊆ R ×ˢ C) :
    realFn (push (extP x0 y0) c) ρ = realFn c ρ := by
  rw [realFn_push, realFn]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h0 : c v = 0
  · simp [h0]
  · rw [chi_extP_of_sub (hc v h0) hx0 hy0 hρ]

theorem realFn_push_extP_of_mem {R C : Finset α} {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    {x0 y0 : α} (hx0 : x0 ∉ R) (hy0 : y0 ∉ C) {ρ : Finset (α × α)}
    (hρ : OnBoard (insert x0 R) (insert y0 C) ρ) (hp : (x0, y0) ∈ ρ) :
    realFn (push (extP x0 y0) c) ρ = realFn c (ρ.erase (x0, y0)) := by
  rw [realFn_push, realFn]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h0 : c v = 0
  · simp [h0]
  · congr 1
    conv_lhs => rw [← Finset.insert_erase hp]
    rw [chi_insert, if_pos (extP_apply_self x0 y0 v),
      chi_extP_of_sub (hc v h0) hx0 hy0 (erase_sub hρ hp)]

theorem realFn_push_extP_zero {R C : Finset α} {c : Equiv.Perm α → K} {x0 y0 : α}
    {ρ : Finset (α × α)} (hρ : OnBoard (insert x0 R) (insert y0 C) ρ) (hp : (x0, y0) ∉ ρ)
    (hn : ¬ ρ ⊆ R ×ˢ C) : realFn (push (extP x0 y0) c) ρ = 0 := by
  rw [realFn_push]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [chi_extP_zero hρ hp hn, mul_zero]

/-- **(E) Extension lemma**, explicit form: a realiser `c` of `F` on `R × C` extended by
`y0 ↦ x0` realises `F` on `(R + x0) × (C + y0)`, provided `F` vanishes on the rooks leaving
`R × C` and has vanishing column lines on `R × C`. -/
theorem ext_eq {R C : Finset α} {x0 y0 : α} (hx0 : x0 ∉ R) (hy0 : y0 ∉ C) {b : ℕ}
    {F : Finset (α × α) → K} {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    (hFc : ∀ ρ, OnBoard R C ρ → ρ.card = b → F ρ = realFn c ρ) (hZ : ColLines R C b F)
    (hbC : b ≤ C.card)
    (hvan : ∀ ρ, OnBoard (insert x0 R) (insert y0 C) ρ → ρ.card = b → ¬ ρ ⊆ R ×ˢ C → F ρ = 0) :
    ∀ ρ, OnBoard (insert x0 R) (insert y0 C) ρ → ρ.card = b →
      F ρ = realFn (push (extP x0 y0) c) ρ := by
  intro ρ hρ hcard
  by_cases hs : ρ ⊆ R ×ˢ C
  · rw [realFn_push_extP_of_sub hc hx0 hy0 hs]
    exact hFc ρ ⟨hρ.1, hs⟩ hcard
  · rw [hvan ρ hρ hcard hs]
    by_cases hp : (x0, y0) ∈ ρ
    · rw [realFn_push_extP_of_mem hc hx0 hy0 hρ hp]
      have hcard' := card_erase_add_one hp
      refine (realFn_eq_zero_below hc hFc hZ ⟨(hρ.erase _).1, erase_sub hρ hp⟩
        (by omega) (by omega)).symm
    · exact (realFn_push_extP_zero hρ hp hs).symm

/-! ### Small cases -/

theorem exists_fits {R C : Finset α} (h : R.card = C.card) : ∃ w : Equiv.Perm α, Fits R C w := by
  have e : {x // x ∈ C} ≃ {x // x ∈ R} := Fintype.equivOfCardEq (by simp [h])
  refine ⟨e.extendSubtype, fun y => ⟨fun hy => ?_, fun hy => e.extendSubtype_mem y hy⟩⟩
  by_contra hyC
  exact e.extendSubtype_not_mem y hyC hy

/-- DCP at level `0`. -/
theorem dcpr_zero (N : ℕ) : DCPR α K 0 N := by
  intro R C hR hC F _
  obtain ⟨w0, hw0⟩ := exists_fits (hR.trans hC.symm)
  refine ⟨fun w => if w = w0 then F ∅ else 0, fun w hw => ?_, fun ρ _ hcard => ?_⟩
  · by_cases h : w = w0
    · rw [h]; exact hw0
    · exact absurd (by simp [h]) hw
  · rw [Finset.card_eq_zero.mp hcard]
    simp [realFn, chi_empty]

/-- DCP is vacuous when the board has fewer than `b` rows. -/
theorem dcpr_of_lt {b N : ℕ} (h : N < b) : DCPR α K b N := by
  intro R C hR _ F _
  refine ⟨0, fitsAll_zero R C, fun ρ hρ hcard => ?_⟩
  have := card_le_of_onBoard hρ
  omega

/-- Elements of `Z_b` vanishing on a row vanish identically when the board has at most `b + 1`
rows. -/
theorem eq_zero_of_card_le {R C : Finset α} {b : ℕ} (hb : 1 ≤ b) {F : Finset (α × α) → K}
    (hZ : ColLines R C b F) {x0 : α} (hx0 : x0 ∈ R)
    (hvan : ∀ ρ, OnBoard R C ρ → ρ.card = b → x0 ∈ rowsOf ρ → F ρ = 0) (hR : R.card ≤ b + 1) :
    ∀ ρ, OnBoard R C ρ → ρ.card = b → F ρ = 0 := by
  intro ρ hρ hcard
  by_cases hx : x0 ∈ rowsOf ρ
  · exact hvan ρ hρ hcard hx
  obtain ⟨p, hp⟩ : ρ.Nonempty := Finset.card_pos.mp (by omega)
  set ρ' := ρ.erase p with hρ'
  have hcard' : ρ'.card + 1 = b := by rw [hρ', card_erase_add_one hp, hcard]
  have hon' : OnBoard R C ρ' := hρ.erase p
  have hpc : p.2 ∉ colsOf ρ' := not_mem_colsOf_erase hρ.1 hp
  have hline := hZ ρ' hon' hcard' p.2 (hρ.col_mem hp) hpc
  have hp1 : p.1 ∈ R \ rowsOf ρ' :=
    Finset.mem_sdiff.mpr ⟨hρ.row_mem hp, not_mem_rowsOf_erase hρ.1 hp⟩
  have hx0' : x0 ∈ R \ rowsOf ρ' :=
    Finset.mem_sdiff.mpr ⟨hx0, fun h => hx (by
      obtain ⟨y, hy⟩ := mem_rowsOf.mp h
      exact rowsOf_mem (Finset.mem_of_mem_erase hy))⟩
  have hne : p.1 ≠ x0 := fun h => hx (h ▸ rowsOf_mem hp)
  have hsub : ({p.1, x0} : Finset α) ⊆ R \ rowsOf ρ' := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hp1
    · rw [Finset.mem_singleton.mp hz]; exact hx0'
  have hcardS : (R \ rowsOf ρ').card ≤ ({p.1, x0} : Finset α).card := by
    rw [Finset.card_sdiff_of_subset (rowsOf_subset hon'), card_rowsOf hon'.1,
      Finset.card_pair hne]
    omega
  have hEq := Finset.eq_of_subset_of_card_le hsub hcardS
  rw [← hEq, Finset.sum_pair hne] at hline
  have h2 : F (insert (x0, p.2) ρ') = 0 := by
    have hx0r : x0 ∉ rowsOf ρ' := (Finset.mem_sdiff.mp hx0').2
    refine hvan _ (hon'.insert hx0 hx0r (hρ.col_mem hp) hpc)
      (by rw [card_insert_cell hx0r, hcard']) ?_
    rw [rowsOf_insert]
    exact Finset.mem_insert_self _ _
  have h1 : insert (p.1, p.2) ρ' = ρ := by
    rw [hρ']
    exact Finset.insert_erase hp
  rw [h2, add_zero, h1] at hline
  exact hline

/-- `HALF_b(N)` holds trivially for `N ≤ b + 1`. -/
theorem half_small {b N : ℕ} (hb : 1 ≤ b) (hN : N ≤ b + 1) : HALF α K b N := by
  intro R C hR _ x0 hx0 F hZ hvan
  refine ⟨0, fitsAll_zero R C, fun ρ hρ hcard => ?_⟩
  rw [realFn_zero]
  exact eq_zero_of_card_le hb hZ.2 hx0 hvan (by omega) ρ hρ hcard

/-! ### Row peel (P) -/

/-- **(P) Row peel.** From `DCP_k(N-1)`: every `F ∈ Z_{k+1}` of an `N × N` board agrees on the
rooks meeting a row `x0` with a realiser whose level-`k` values vanish. -/
theorem row_peel {k N : ℕ} (hDCP : DCPR α K k (N - 1)) {R C : Finset α} (hR : R.card = N)
    (hC : C.card = N) (hkN : k + 1 ≤ N) {F : Finset (α × α) → K} (hZ : ZB R C (k + 1) F)
    {x0 : α} (hx0 : x0 ∈ R) :
    ∃ c, FitsAll R C c ∧ (∀ σ, OnBoard R C σ → σ.card = k → realFn c σ = 0) ∧
      ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → x0 ∈ rowsOf ρ → F ρ = realFn c ρ := by
  set H : α → Finset (α × α) → K := fun y ρ' => F (insert (x0, y) ρ') with hH
  have hRe : (R.erase x0).card = N - 1 := by rw [Finset.card_erase_of_mem hx0, hR]
  have hx0R : x0 ∉ R.erase x0 := Finset.notMem_erase x0 R
  -- the contractions are in `Z_k` of the smaller boards
  have hZH : ∀ y ∈ C, ZB (R.erase x0) (C.erase y) k (H y) := by
    intro y hy
    refine ⟨fun ρ hρ hcard x hx hxr => ?_, fun ρ hρ hcard y' hy' hyc => ?_⟩
    · have hρ' : OnBoard R C ρ := hρ.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      have hx0r : x0 ∉ rowsOf ρ := fun h => hx0R (rowsOf_subset hρ h)
      have hyc : y ∉ colsOf ρ := fun h => Finset.notMem_erase y C (colsOf_subset hρ h)
      have hσ := hρ'.insert hx0 hx0r hy hyc
      have hxne : x ≠ x0 := Finset.ne_of_mem_erase hx
      have hxr' : x ∉ rowsOf (insert (x0, y) ρ) := by
        rw [rowsOf_insert, Finset.mem_insert]; push_neg; exact ⟨hxne, hxr⟩
      have := hZ.1 _ hσ (by rw [card_insert_cell hx0r, hcard]) x (Finset.mem_of_mem_erase hx) hxr'
      rw [colsOf_insert] at this
      rw [← this]
      refine Finset.sum_congr ?_ fun y'' _ => ?_
      · ext z
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      · simp only [hH]
        rw [Finset.insert_comm]
    · have hρ' : OnBoard R C ρ := hρ.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      have hx0r : x0 ∉ rowsOf ρ := fun h => hx0R (rowsOf_subset hρ h)
      have hyc0 : y ∉ colsOf ρ := fun h => Finset.notMem_erase y C (colsOf_subset hρ h)
      have hσ := hρ'.insert hx0 hx0r hy hyc0
      have hyne : y' ≠ y := Finset.ne_of_mem_erase hy'
      have hyc' : y' ∉ colsOf (insert (x0, y) ρ) := by
        rw [colsOf_insert, Finset.mem_insert]; push_neg; exact ⟨hyne, hyc⟩
      have := hZ.2 _ hσ (by rw [card_insert_cell hx0r, hcard]) y' (Finset.mem_of_mem_erase hy')
        hyc'
      rw [rowsOf_insert] at this
      rw [← this]
      refine Finset.sum_congr ?_ fun x'' _ => ?_
      · ext z
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      · simp only [hH]
        rw [Finset.insert_comm]
  have hreal : ∀ y ∈ C, Real (R.erase x0) (C.erase y) k (H y) := fun y hy =>
    hDCP _ _ hRe (by rw [Finset.card_erase_of_mem hy, hC]) _ (hZH y hy)
  choose! cy hcyF hcy using hreal
  have hins : ∀ y ∈ C, insert x0 (R.erase x0) = R ∧ insert y (C.erase y) = C := fun y hy =>
    ⟨Finset.insert_erase hx0, Finset.insert_erase hy⟩
  have hfit : ∀ y ∈ C, FitsAll R C (push (extP x0 y) (cy y)) := by
    intro y hy
    have := fitsAll_push_extP (hcyF y hy) hx0R (Finset.notMem_erase y C)
    rwa [(hins y hy).1, (hins y hy).2] at this
  -- value on a rook containing `(x0, y1)`
  have hval : ∀ ρ, OnBoard R C ρ → ∀ y1, (x0, y1) ∈ ρ →
      ∑ y ∈ C, realFn (push (extP x0 y) (cy y)) ρ =
        realFn (cy y1) (ρ.erase (x0, y1)) := by
    intro ρ hρ y1 hp
    have hy1 : y1 ∈ C := hρ.col_mem hp
    have hρ1 : OnBoard (insert x0 (R.erase x0)) (insert y1 (C.erase y1)) ρ := by
      rw [(hins y1 hy1).1, (hins y1 hy1).2]; exact hρ
    rw [Finset.sum_eq_single y1]
    · exact realFn_push_extP_of_mem (hcyF y1 hy1) hx0R (Finset.notMem_erase y1 C) hρ1 hp
    · intro y hy hne
      have hρy : OnBoard (insert x0 (R.erase x0)) (insert y (C.erase y)) ρ := by
        rw [(hins y hy).1, (hins y hy).2]; exact hρ
      refine realFn_push_extP_zero hρy (fun h => hne ?_) (fun hs => ?_)
      · exact (rook_eq_of_row hρ.1 hp h).symm
      · exact hx0R (Finset.mem_product.mp (hs hp)).1
    · intro h; exact absurd hy1 h
  refine ⟨∑ y ∈ C, push (extP x0 y) (cy y), fitsAll_sum C hfit, fun σ hσ hcard => ?_,
    fun ρ hρ hcard hx => ?_⟩
  · rw [realFn_sum]
    by_cases hx : x0 ∈ rowsOf σ
    · obtain ⟨y1, hp⟩ := mem_rowsOf.mp hx
      have hy1 : y1 ∈ C := hσ.col_mem hp
      rw [hval σ hσ y1 hp]
      have hcard' := card_erase_add_one hp
      refine realFn_eq_zero_below (hcyF y1 hy1) (hcy y1 hy1) (hZH y1 hy1).2
        ⟨(hσ.erase _).1, erase_sub (by rw [(hins y1 hy1).1, (hins y1 hy1).2]; exact hσ) hp⟩
        (by omega) ?_
      rw [Finset.card_erase_of_mem hy1, hC]
      omega
    · rw [← hZ.1 σ hσ (by rw [hcard]) x0 hx0 hx]
      symm
      rw [← Finset.sum_subset (Finset.sdiff_subset (s := C) (t := colsOf σ))]
      · refine Finset.sum_congr rfl fun y hy => ?_
        obtain ⟨hyC, hyc⟩ := Finset.mem_sdiff.mp hy
        have hsub : σ ⊆ (R.erase x0) ×ˢ (C.erase y) := by
          intro q hq
          refine Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hx (h ▸ rowsOf_mem hq),
            hσ.row_mem hq⟩, Finset.mem_erase.mpr ⟨fun h => hyc (h ▸ colsOf_mem hq),
            hσ.col_mem hq⟩⟩
        rw [realFn_push_extP_of_sub (hcyF y hyC) hx0R (Finset.notMem_erase y C) hsub]
        exact hcy y hyC σ ⟨hσ.1, hsub⟩ hcard
      · intro y hyC hy
        have hyc : y ∈ colsOf σ := by
          by_contra h; exact hy (Finset.mem_sdiff.mpr ⟨hyC, h⟩)
        have hρy : OnBoard (insert x0 (R.erase x0)) (insert y (C.erase y)) σ := by
          rw [(hins y hyC).1, (hins y hyC).2]; exact hσ
        refine realFn_push_extP_zero hρy (fun h => hx (rowsOf_mem h)) (fun hs => ?_)
        obtain ⟨x', hx'⟩ := mem_colsOf.mp hyc
        exact Finset.notMem_erase y C (Finset.mem_product.mp (hs hx')).2
  · obtain ⟨y1, hp⟩ := mem_rowsOf.mp hx
    have hy1 : y1 ∈ C := hρ.col_mem hp
    rw [realFn_sum, hval ρ hρ y1 hp]
    have hcard' := card_erase_add_one hp
    rw [← hcy y1 hy1 _ ⟨(hρ.erase _).1,
      erase_sub (by rw [(hins y1 hy1).1, (hins y1 hy1).2]; exact hρ) hp⟩ (by omega)]
    simp only [hH]
    rw [Finset.insert_erase hp]

/-! ### Assembly lemmas -/

/-- The part of `F` not yet realised, after subtracting a realiser that vanishes one level down,
is still in `Z_{k+1}`. -/
theorem zb_sub_realFn {R C : Finset α} {k : ℕ} {F : Finset (α × α) → K} (hZ : ZB R C (k + 1) F)
    {c : Equiv.Perm α → K} (hc : FitsAll R C c)
    (h0 : ∀ σ, OnBoard R C σ → σ.card = k → realFn c σ = 0) :
    ZB R C (k + 1) (fun ρ => F ρ - realFn c ρ) :=
  zb_sub hZ (zb_realFn hc fun σ hσ hcard => h0 σ hσ (by omega))

/-- **DCP from HALF**: `DCP_k(N-1)` and `HALF_{k+1}(N)` give `DCP_{k+1}(N)`. -/
theorem dcpr_of_half {k N : ℕ} (hN : k + 1 ≤ N) (hk : DCPR α K k (N - 1))
    (hhalf : HALF α K (k + 1) N) : DCPR α K (k + 1) N := by
  intro R C hR hC F hZ
  obtain ⟨x0, hx0⟩ : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc, h0, hF⟩ := row_peel hk hR hC hN hZ hx0
  refine real_of_sub hc (hhalf R C hR hC x0 hx0 _ (zb_sub_realFn hZ hc h0) fun ρ hρ hcard hx => ?_)
  rw [hF ρ hρ hcard hx, sub_self]

/-! ### Controlled column peel (C) -/

/-- **(C) Controlled column peel.** From `DCP_k(N-2)` and Lemma D (rook form, level `k`, on the
column set `C \ y0`): every `F ∈ Z_{k+1}` of an `N × N` board vanishing on the rooks meeting row
`x0` agrees on the rooks meeting row `x0` or column `y0` with a realiser whose level-`k` values
vanish. -/
theorem col_peel {k N : ℕ} (hDCP : DCPR α K k (N - 2)) {R C : Finset α} (hR : R.card = N)
    (hC : C.card = N) (hkN : k + 2 ≤ N) {F : Finset (α × α) → K} (hZ : ZB R C (k + 1) F)
    {x0 y0 : α} (hx0 : x0 ∈ R) (hy0 : y0 ∈ C)
    (hvan : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → x0 ∈ rowsOf ρ → F ρ = 0)
    (hsplit : ColSplit K R (C.erase y0) k) :
    ∃ c, FitsAll R C c ∧ (∀ σ, OnBoard R C σ → σ.card = k → realFn c σ = 0) ∧
      ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → (x0 ∈ rowsOf ρ ∨ y0 ∈ colsOf ρ) →
        F ρ = realFn c ρ := by
  set C' := C.erase y0 with hC'
  have hy0C' : y0 ∉ C' := Finset.notMem_erase y0 C
  have hC'C : C' ⊆ C := Finset.erase_subset _ _
  have hC'card : C'.card = N - 1 := by rw [hC', Finset.card_erase_of_mem hy0, hC]
  set H : α → Finset (α × α) → K :=
    fun x ρ' => if x ∈ rowsOf ρ' then 0 else F (insert (x, y0) ρ') with hHdef
  have hH_apply : ∀ x ρ', H x ρ' = if x ∈ rowsOf ρ' then 0 else F (insert (x, y0) ρ') :=
    fun _ _ => rfl
  have hHvx : ∀ x ρ, x ∈ rowsOf ρ → H x ρ = 0 := fun x ρ h => by rw [hH_apply, if_pos h]
  -- line conditions of the contractions
  have hHrow : ∀ x ∈ R, RowLines R C' k (H x) := by
    intro x hx ρ hρ hcard x' hx' hx'r
    by_cases hxx : x ∈ rowsOf ρ ∨ x = x'
    · refine Finset.sum_eq_zero fun y _ => hHvx _ _ ?_
      rw [rowsOf_insert, Finset.mem_insert]
      rcases hxx with h | h
      · exact Or.inr h
      · exact Or.inl h
    · push_neg at hxx
      obtain ⟨hxr, hxne⟩ := hxx
      have hyc : y0 ∉ colsOf ρ := fun h => hy0C' (colsOf_subset hρ h)
      have hσ : OnBoard R C (insert (x, y0) ρ) :=
        (hρ.mono (Finset.Subset.refl _) hC'C).insert hx hxr hy0 hyc
      have hx'σ : x' ∉ rowsOf (insert (x, y0) ρ) := by
        rw [rowsOf_insert, Finset.mem_insert]; push_neg; exact ⟨fun h => hxne h.symm, hx'r⟩
      have := hZ.1 _ hσ (by rw [card_insert_cell hxr, hcard]) x' hx' hx'σ
      rw [← this]
      refine Finset.sum_congr ?_ fun y _ => ?_
      · ext z
        simp only [Finset.mem_sdiff, colsOf_insert, Finset.mem_insert, hC', Finset.mem_erase]
        tauto
      · have : x ∉ rowsOf (insert (x', y) ρ) := by
          rw [rowsOf_insert, Finset.mem_insert]; push_neg; exact ⟨hxne, hxr⟩
        rw [hH_apply, if_neg this, Finset.insert_comm]
  have hHcol : ∀ x ∈ R, ColLines R C' k (H x) := by
    intro x hx ρ hρ hcard y hy hyc
    by_cases hxr : x ∈ rowsOf ρ
    · refine Finset.sum_eq_zero fun x' _ => hHvx _ _ ?_
      rw [rowsOf_insert]; exact Finset.mem_insert_of_mem hxr
    · have hxm : x ∈ R \ rowsOf ρ := Finset.mem_sdiff.mpr ⟨hx, hxr⟩
      rw [← Finset.sum_erase_add _ _ hxm,
        hHvx _ _ (by rw [rowsOf_insert]; exact Finset.mem_insert_self _ _), add_zero]
      have hy0c : y0 ∉ colsOf ρ := fun h => hy0C' (colsOf_subset hρ h)
      have hσ : OnBoard R C (insert (x, y0) ρ) :=
        (hρ.mono (Finset.Subset.refl _) hC'C).insert hx hxr hy0 hy0c
      have hyne : y ≠ y0 := Finset.ne_of_mem_erase hy
      have hyσ : y ∉ colsOf (insert (x, y0) ρ) := by
        rw [colsOf_insert, Finset.mem_insert]; push_neg; exact ⟨hyne, hyc⟩
      have := hZ.2 _ hσ (by rw [card_insert_cell hxr, hcard]) y (hC'C hy) hyσ
      rw [← this]
      refine Finset.sum_congr ?_ fun x' hx' => ?_
      · ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, rowsOf_insert, Finset.mem_insert]
        tauto
      · have hx'ne : x' ≠ x := fun h => (Finset.mem_sdiff.mp hx').2
          (by rw [rowsOf_insert, h]; exact Finset.mem_insert_self _ _)
        have : x ∉ rowsOf (insert (x', y) ρ) := by
          rw [rowsOf_insert, Finset.mem_insert]; push_neg; exact ⟨fun h => hx'ne h.symm, hxr⟩
        rw [hH_apply, if_neg this, Finset.insert_comm]
  have hHvx0 : ∀ x ∈ R, ∀ ρ, OnBoard R C' ρ → ρ.card = k → (x0 ∈ rowsOf ρ ∨ x = x0) →
      H x ρ = 0 := by
    intro x hx ρ hρ hcard h
    by_cases hxr : x ∈ rowsOf ρ
    · exact hHvx _ _ hxr
    · rw [hH_apply, if_neg hxr]
      have hy0c : y0 ∉ colsOf ρ := fun h => hy0C' (colsOf_subset hρ h)
      refine hvan _ ((hρ.mono (Finset.Subset.refl _) hC'C).insert hx hxr hy0 hy0c)
        (by rw [card_insert_cell hxr, hcard]) ?_
      rw [rowsOf_insert, Finset.mem_insert]
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
  -- the contractions sum to zero (column-`y0` lines of `F`)
  have hHsum : ∀ ρ, OnBoard R C' ρ → ρ.card = k → ∑ x ∈ R.erase x0, H x ρ = 0 := by
    intro ρ hρ hcard
    have h1 : ∑ x ∈ R.erase x0, H x ρ = ∑ x ∈ R, H x ρ := by
      rw [← Finset.sum_erase_add _ _ hx0, hHvx0 x0 hx0 ρ hρ hcard (Or.inr rfl), add_zero]
    have hy0c : y0 ∉ colsOf ρ := fun h => hy0C' (colsOf_subset hρ h)
    rw [h1, ← hZ.2 ρ (hρ.mono (Finset.Subset.refl _) hC'C) (by rw [hcard]) y0 hy0 hy0c,
      ← Finset.sum_subset (Finset.sdiff_subset (s := R) (t := rowsOf ρ)) (f := fun x => H x ρ)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [hH_apply, if_neg (Finset.mem_sdiff.mp hx).2]
    · intro x hxR hx
      refine hHvx _ _ ?_
      by_contra h
      exact hx (Finset.mem_sdiff.mpr ⟨hxR, h⟩)
  obtain ⟨Pi, hloc, hPi⟩ := hsplit
  -- the pieces `P x y = Pi y (H x)`
  have hPvan : ∀ x ∈ R.erase x0, ∀ y ∈ C', ∀ ρ, OnBoard R C' ρ → ρ.card = k →
      ¬ ρ ⊆ ((R.erase x0).erase x) ×ˢ (C'.erase y) → Pi y (H x) ρ = 0 := by
    intro x hx y hy ρ hρ hcard hn
    have hxR := Finset.mem_of_mem_erase hx
    obtain ⟨p, hp, hout⟩ := exists_out hρ hn
    have hpR := hρ.row_mem hp
    have hpC := hρ.col_mem hp
    obtain ⟨-, -, -, hcolv, hrowv⟩ := hPi (H x) (hHrow x hxR)
    rcases hout with h | h
    · by_cases hpx : p.1 = x
      · exact hrowv y hy x (fun σ _ _ hσx => hHvx x σ hσx) ρ hρ hcard (hpx ▸ rowsOf_mem hp)
      · have hpx0 : p.1 = x0 := by
          by_contra hne
          exact h (Finset.mem_erase.mpr ⟨hpx, Finset.mem_erase.mpr ⟨hne, hpR⟩⟩)
        exact hrowv y hy x0 (fun σ hσ hσc hσx => hHvx0 x hxR σ hσ hσc (Or.inl hσx)) ρ hρ hcard
          (hpx0 ▸ rowsOf_mem hp)
    · have hpy : p.2 = y := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hpC⟩)
      exact hcolv y hy ρ hρ hcard (hpy ▸ colsOf_mem hp)
  have hPZB : ∀ x ∈ R.erase x0, ∀ y ∈ C', ZB R C' k (Pi y (H x)) := by
    intro x hx y hy
    have hxR := Finset.mem_of_mem_erase hx
    obtain ⟨-, hrow, hcol, -, -⟩ := hPi (H x) (hHrow x hxR)
    exact ⟨hrow y hy, hcol y hy (hHcol x hxR)⟩
  have hreal : ∀ x ∈ R.erase x0, ∀ y ∈ C',
      Real ((R.erase x0).erase x) (C'.erase y) k (Pi y (H x)) := by
    intro x hx y hy
    refine hDCP _ _ ?_ ?_ _ (zb_mono (Finset.Subset.trans (Finset.erase_subset _ _)
      (Finset.erase_subset _ _)) (Finset.erase_subset _ _) (hPZB x hx y hy) (hPvan x hx y hy))
    · rw [Finset.card_erase_of_mem hx, Finset.card_erase_of_mem hx0, hR]; omega
    · rw [Finset.card_erase_of_mem hy, hC'card]; omega
  choose! cc hccF hcc using hreal
  -- board identities
  have hRm : ∀ x ∈ R.erase x0, insert x0 ((R.erase x0).erase x) = R.erase x := by
    intro x hx
    rw [Finset.erase_right_comm]
    exact Finset.insert_erase (Finset.mem_erase.mpr ⟨fun h => Finset.ne_of_mem_erase hx h.symm, hx0⟩)
  have hCm : ∀ y ∈ C', insert y (C'.erase y) = C' := fun y hy => Finset.insert_erase hy
  have hRb : ∀ x ∈ R.erase x0, insert x (R.erase x) = R :=
    fun x hx => Finset.insert_erase (Finset.mem_of_mem_erase hx)
  have hCb : insert y0 C' = C := Finset.insert_erase hy0
  have hx0s : ∀ x, x0 ∉ (R.erase x0).erase x :=
    fun x h => Finset.notMem_erase x0 R (Finset.mem_of_mem_erase h)
  -- middle realisers `m x y` on `(R \ x) × C'`
  have hmF : ∀ x ∈ R.erase x0, ∀ y ∈ C', FitsAll (R.erase x) C' (push (extP x0 y) (cc x y)) := by
    intro x hx y hy
    have := fitsAll_push_extP (hccF x hx y hy) (hx0s x) (Finset.notMem_erase y C')
    rwa [hRm x hx, hCm y hy] at this
  have hmP : ∀ x ∈ R.erase x0, ∀ y ∈ C', ∀ ρ, OnBoard (R.erase x) C' ρ → ρ.card = k →
      Pi y (H x) ρ = realFn (push (extP x0 y) (cc x y)) ρ := by
    intro x hx y hy
    have hZs := zb_mono (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      (Finset.erase_subset _ _) (hPZB x hx y hy) (hPvan x hx y hy)
    have := ext_eq (hx0s x) (Finset.notMem_erase y C') (hccF x hx y hy) (hcc x hx y hy) hZs.2
      (by rw [Finset.card_erase_of_mem hy, hC'card]; omega) (by
        intro ρ hρ hcard hn
        rw [hRm x hx, hCm y hy] at hρ
        exact hPvan x hx y hy ρ (hρ.mono (Finset.erase_subset _ _) (Finset.Subset.refl _)) hcard hn)
    rwa [hRm x hx, hCm y hy] at this
  have hm0 : ∀ x ∈ R.erase x0, ∀ y ∈ C', ∀ σ, OnBoard (R.erase x) C' σ → σ.card + 1 = k →
      realFn (push (extP x0 y) (cc x y)) σ = 0 := by
    intro x hx y hy σ hσ hcard
    have hxR := Finset.mem_of_mem_erase hx
    have hZm : ZB (R.erase x) C' k (Pi y (H x)) := by
      refine zb_mono (Finset.erase_subset _ _) (Finset.Subset.refl _) (hPZB x hx y hy)
        fun ρ hρ hc hn => ?_
      obtain ⟨p, hp, hout⟩ := exists_out hρ hn
      obtain ⟨-, -, -, -, hrowv⟩ := hPi (H x) (hHrow x hxR)
      have hpx : p.1 = x := by
        rcases hout with h | h
        · by_contra hne; exact h (Finset.mem_erase.mpr ⟨hne, hρ.row_mem hp⟩)
        · exact absurd (hρ.col_mem hp) h
      exact hrowv y hy x (fun σ _ _ hσx => hHvx x σ hσx) ρ hρ hc (hpx ▸ rowsOf_mem hp)
    refine realFn_eq_zero_below (hmF x hx y hy) (hmP x hx y hy) hZm.2 hσ hcard ?_
    rw [hC'card]; omega
  -- big realisers
  set d : α → α → Equiv.Perm α → K := fun x y => push (extP x y0) (push (extP x0 y) (cc x y))
    with hddef
  have hdF : ∀ x ∈ R.erase x0, ∀ y ∈ C', FitsAll R C (d x y) := by
    intro x hx y hy
    have := fitsAll_push_extP (hmF x hx y hy) (Finset.notMem_erase x R) hy0C'
    rwa [hRb x hx, hCb] at this
  have hbig : ∀ x ∈ R.erase x0, ∀ ρ, OnBoard R C ρ →
      OnBoard (insert x (R.erase x)) (insert y0 C') ρ := by
    intro x hx ρ hρ
    rw [hRb x hx, hCb]; exact hρ
  -- (K1) rooks avoiding column `y0`
  have hK1 : ∀ x ∈ R.erase x0, ∀ σ, OnBoard R C σ → σ.card = k → y0 ∉ colsOf σ →
      ∑ y ∈ C', realFn (d x y) σ = H x σ := by
    intro x hx σ hσ hcard hyc
    by_cases hxr : x ∈ rowsOf σ
    · rw [hHvx x σ hxr]
      refine Finset.sum_eq_zero fun y _ => realFn_push_extP_zero (hbig x hx σ hσ)
        (fun h => hyc (colsOf_mem h)) fun hs => ?_
      obtain ⟨y', hy'⟩ := mem_rowsOf.mp hxr
      exact Finset.notMem_erase x R (Finset.mem_product.mp (hs hy')).1
    · have hsub : σ ⊆ (R.erase x) ×ˢ C' := sub_of_avoid (hbig x hx σ hσ) hxr hyc
      obtain ⟨hsum, -⟩ := hPi (H x) (hHrow x (Finset.mem_of_mem_erase hx))
      rw [← hsum σ ⟨hσ.1, fun q hq => Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hsub hq)).1
        |> Finset.mem_of_mem_erase, (Finset.mem_product.mp (hsub hq)).2⟩⟩ hcard]
      refine Finset.sum_congr rfl fun y hy => ?_
      show realFn (push (extP x y0) (push (extP x0 y) (cc x y))) σ = Pi y (H x) σ
      rw [realFn_push_extP_of_sub (hmF x hx y hy) (Finset.notMem_erase x R) hy0C' hsub]
      exact (hmP x hx y hy σ ⟨hσ.1, hsub⟩ hcard).symm
  -- (K2) rooks through `(x1, y0)`: only `x = x1` contributes
  have hK2 : ∀ x ∈ R.erase x0, ∀ ρ, OnBoard R C ρ → ∀ x1, (x1, y0) ∈ ρ → x ≠ x1 →
      ∀ y, realFn (d x y) ρ = 0 := by
    intro x hx ρ hρ x1 hp hne y
    refine realFn_push_extP_zero (hbig x hx ρ hρ) (fun h => hne (rook_eq_of_col hρ.1 h hp))
      fun hs => ?_
    exact hy0C' (Finset.mem_product.mp (hs hp)).2
  have hK3 : ∀ x ∈ R.erase x0, ∀ ρ, OnBoard R C ρ → (x, y0) ∈ ρ → ∀ y ∈ C',
      realFn (d x y) ρ = realFn (push (extP x0 y) (cc x y)) (ρ.erase (x, y0)) :=
    fun x hx ρ hρ hp y hy => realFn_push_extP_of_mem (hmF x hx y hy) (Finset.notMem_erase x R)
      hy0C' (hbig x hx ρ hρ) hp
  refine ⟨∑ x ∈ R.erase x0, ∑ y ∈ C', d x y,
    fitsAll_sum _ fun x hx => fitsAll_sum _ fun y hy => hdF x hx y hy, fun σ hσ hcard => ?_,
    fun ρ hρ hcard hmeet => ?_⟩
  · -- (V3) the realiser vanishes one level down
    simp only [realFn_sum]
    by_cases hyc : y0 ∈ colsOf σ
    · obtain ⟨x1, hp⟩ := mem_colsOf.mp hyc
      refine Finset.sum_eq_zero fun x hx => ?_
      by_cases hxx : x = x1
      · rw [← hxx] at hp
        refine Finset.sum_eq_zero fun y hy => ?_
        rw [hK3 x hx σ hσ hp y hy]
        have hc' := card_erase_add_one hp
        exact hm0 x hx y hy _ ⟨(hσ.erase _).1, erase_sub (hbig x hx σ hσ) hp⟩ (by omega)
      · exact Finset.sum_eq_zero fun y _ => hK2 x hx σ hσ x1 hp hxx y
    · rw [Finset.sum_congr rfl fun x hx => hK1 x hx σ hσ hcard hyc]
      exact hHsum σ (hσ.erase_col hyc) hcard
  · simp only [realFn_sum]
    by_cases hyc : y0 ∈ colsOf ρ
    · -- (V1) rooks meeting column `y0`
      obtain ⟨x1, hp⟩ := mem_colsOf.mp hyc
      by_cases hx1 : x1 = x0
      · rw [hvan ρ hρ hcard (hx1 ▸ rowsOf_mem hp)]
        exact (Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y _ =>
          hK2 x hx ρ hρ x1 hp (fun h => Finset.ne_of_mem_erase hx (h.trans hx1)) y).symm
      · have hx1m : x1 ∈ R.erase x0 := Finset.mem_erase.mpr ⟨hx1, hρ.row_mem hp⟩
        rw [Finset.sum_eq_single x1
          (fun x hx hne => Finset.sum_eq_zero fun y _ => hK2 x hx ρ hρ x1 hp hne y)
          (fun h => absurd hx1m h)]
        have hc' := card_erase_add_one hp
        have hon : OnBoard (R.erase x1) C' (ρ.erase (x1, y0)) :=
          ⟨(hρ.erase _).1, erase_sub (hbig x1 hx1m ρ hρ) hp⟩
        rw [Finset.sum_congr rfl fun y hy => (hK3 x1 hx1m ρ hρ hp y hy).trans
          (hmP x1 hx1m y hy _ hon (by omega)).symm]
        obtain ⟨hsum, -⟩ := hPi (H x1) (hHrow x1 (hρ.row_mem hp))
        rw [hsum _ (hon.mono (Finset.erase_subset _ _) (Finset.Subset.refl _)) (by omega),
          hH_apply, if_neg (not_mem_rowsOf_erase hρ.1 hp), Finset.insert_erase hp]
    · -- (V2) rooks meeting row `x0` but not column `y0`
      have hx : x0 ∈ rowsOf ρ := hmeet.resolve_right hyc
      rw [hvan ρ hρ hcard hx]
      obtain ⟨y1, hp⟩ := mem_rowsOf.mp hx
      have hy1 : y1 ∈ C' :=
        Finset.mem_erase.mpr ⟨fun e => hyc (e ▸ colsOf_mem hp), hρ.col_mem hp⟩
      have hc' := card_erase_add_one hp
      have hon' : OnBoard R C' (ρ.erase (x0, y1)) := (hρ.erase _).erase_col fun h => hyc (by
        obtain ⟨x', hx'⟩ := mem_colsOf.mp h
        exact colsOf_mem (Finset.mem_of_mem_erase hx'))
      have hper : ∀ x ∈ R.erase x0,
          ∑ y ∈ C', realFn (d x y) ρ = Pi y1 (H x) (ρ.erase (x0, y1)) := by
        intro x hx
        have hxR := Finset.mem_of_mem_erase hx
        obtain ⟨-, -, -, -, hrowv⟩ := hPi (H x) (hHrow x hxR)
        by_cases hxr : x ∈ rowsOf ρ
        · obtain ⟨y', hy'⟩ := mem_rowsOf.mp hxr
          have hxr' : x ∈ rowsOf (ρ.erase (x0, y1)) :=
            rowsOf_mem (Finset.mem_erase.mpr
              ⟨fun h => Finset.ne_of_mem_erase hx (Prod.mk.inj h).1, hy'⟩)
          rw [hrowv y1 hy1 x (fun σ _ _ hσx => hHvx x σ hσx) _ hon' (by omega) hxr']
          refine Finset.sum_eq_zero fun y _ => realFn_push_extP_zero (hbig x hx ρ hρ)
            (fun h => hyc (colsOf_mem h)) fun hs => ?_
          exact Finset.notMem_erase x R (Finset.mem_product.mp (hs hy')).1
        · have hsub : ρ ⊆ (R.erase x) ×ˢ C' := sub_of_avoid (hbig x hx ρ hρ) hxr hyc
          have hmid : ∀ y ∈ C',
              OnBoard (insert x0 ((R.erase x0).erase x)) (insert y (C'.erase y)) ρ := by
            intro y hy
            rw [hRm x hx, hCm y hy]
            exact ⟨hρ.1, hsub⟩
          rw [Finset.sum_eq_single y1]
          · show realFn (push (extP x y0) (push (extP x0 y1) (cc x y1))) ρ = _
            rw [realFn_push_extP_of_sub (hmF x hx y1 hy1) (Finset.notMem_erase x R) hy0C' hsub,
              realFn_push_extP_of_mem (hccF x hx y1 hy1) (hx0s x) (Finset.notMem_erase y1 C')
                (hmid y1 hy1) hp]
            exact (hcc x hx y1 hy1 _ ⟨(hρ.erase _).1, erase_sub (hmid y1 hy1) hp⟩
              (by omega)).symm
          · intro y hy hne
            show realFn (push (extP x y0) (push (extP x0 y) (cc x y))) ρ = 0
            rw [realFn_push_extP_of_sub (hmF x hx y hy) (Finset.notMem_erase x R) hy0C' hsub]
            refine realFn_push_extP_zero (hmid y hy)
              (fun h => hne (rook_eq_of_row hρ.1 hp h).symm) fun hs => ?_
            exact hx0s x (Finset.mem_product.mp (hs hp)).1
          · intro h
            exact absurd hy1 h
      rw [Finset.sum_congr rfl hper]
      have := hloc (∑ x ∈ R.erase x0, H x)
        (fun σ hσ hc => by rw [Finset.sum_apply]; exact hHsum σ hσ hc) y1 _ hon' (by omega)
      rw [map_sum, Finset.sum_apply] at this
      exact this.symm

/-! ### The induction -/

/-- **One step for `N ≥ 2b`** (`b = k + 1`): (P), (C), (E) and `DCP_b(N-1)`. -/
theorem dcpr_step {k N : ℕ} (hN : 2 * k + 2 ≤ N) (hprev : DCPR α K (k + 1) (N - 1))
    (hk1 : DCPR α K k (N - 1)) (hk2 : DCPR α K k (N - 2))
    (hsplit : ∀ R C : Finset α, 2 * k + 1 ≤ C.card → ColSplit K R C k) :
    DCPR α K (k + 1) N := by
  intro R C hR hC F hZ
  obtain ⟨x0, hx0⟩ : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y0, hy0⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c1, hc1, h01, hF1⟩ := row_peel hk1 hR hC (by omega) hZ hx0
  have hZ1 := zb_sub_realFn hZ hc1 h01
  obtain ⟨c2, hc2, h02, hF2⟩ := col_peel hk2 hR hC (by omega) hZ1 hx0 hy0
    (fun ρ hρ hcard hx => by show F ρ - realFn c1 ρ = 0; rw [hF1 ρ hρ hcard hx, sub_self])
    (hsplit R (C.erase y0) (by rw [Finset.card_erase_of_mem hy0, hC]; omega))
  have hZ2 := zb_sub_realFn hZ1 hc2 h02
  have hvan2 : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → ¬ ρ ⊆ (R.erase x0) ×ˢ (C.erase y0) →
      (fun ρ => (fun ρ => F ρ - realFn c1 ρ) ρ - realFn c2 ρ) ρ = 0 := by
    intro ρ hρ hcard hn
    have hm : x0 ∈ rowsOf ρ ∨ y0 ∈ colsOf ρ := by
      by_contra h
      push_neg at h
      exact hn (sub_of_avoid (by rw [Finset.insert_erase hx0, Finset.insert_erase hy0]; exact hρ)
        h.1 h.2)
    show (F ρ - realFn c1 ρ) - realFn c2 ρ = 0
    rw [← hF2 ρ hρ hcard hm]
    exact sub_self _
  have hZs := zb_mono (Finset.erase_subset _ _) (Finset.erase_subset _ _) hZ2 hvan2
  obtain ⟨c3, hc3, hF3⟩ := hprev _ _ (by rw [Finset.card_erase_of_mem hx0, hR])
    (by rw [Finset.card_erase_of_mem hy0, hC]) _ hZs
  have hext := ext_eq (Finset.notMem_erase x0 R) (Finset.notMem_erase y0 C) hc3 hF3 hZs.2
    (by rw [Finset.card_erase_of_mem hy0, hC]; omega)
    (by rw [Finset.insert_erase hx0, Finset.insert_erase hy0]; exact hvan2)
  rw [Finset.insert_erase hx0, Finset.insert_erase hy0] at hext
  have hfit3 := fitsAll_push_extP hc3 (Finset.notMem_erase x0 R) (Finset.notMem_erase y0 C)
  rw [Finset.insert_erase hx0, Finset.insert_erase hy0] at hfit3
  exact real_of_sub hc1 (real_of_sub hc2 ⟨_, hfit3, hext⟩)

/-- **The reduction.**  Given Lemma D in rook form (`ColSplit`, proved from B's `lemmaD` in
`DCPBridge`) and the OPEN statement `HALF` in the window `b' + 2 ≤ N ≤ 2b' - 1` for all levels
`b' ≤ b`, `DCP_b(N)` holds for every `N`. -/
theorem dcpr_all (hsplit : ∀ (k : ℕ) (R C : Finset α), 2 * k + 1 ≤ C.card → ColSplit K R C k)
    (b : ℕ) (hhalf : ∀ b' N, b' ≤ b → b' + 2 ≤ N → N + 1 ≤ 2 * b' → HALF α K b' N) :
    ∀ N, DCPR α K b N := by
  induction b with
  | zero => exact dcpr_zero
  | succ k ih =>
    have ihk := ih (fun b' N hb' => hhalf b' N (by omega))
    intro N
    induction N with
    | zero => exact dcpr_of_lt (by omega)
    | succ M ihM =>
      by_cases h1 : M + 1 < k + 1
      · exact dcpr_of_lt h1
      by_cases h2 : M + 1 ≤ k + 2
      · exact dcpr_of_half (by omega) (ihk _) (half_small (by omega) h2)
      by_cases h3 : M + 1 + 1 ≤ 2 * (k + 1)
      · exact dcpr_of_half (by omega) (ihk _) (hhalf (k + 1) (M + 1) le_rfl (by omega) h3)
      · exact dcpr_step (k := k) (N := M + 1) (by omega) (by simpa using ihM) (ihk _) (ihk _)
          (hsplit k)

/-- For `b ≤ 2` the window is empty: `DCP_b(N)` for all `N` from `ColSplit` alone. -/
theorem dcpr_le_two (hsplit : ∀ (k : ℕ) (R C : Finset α), 2 * k + 1 ≤ C.card → ColSplit K R C k)
    {b : ℕ} (hb : b ≤ 2) : ∀ N, DCPR α K b N :=
  dcpr_all hsplit b fun b' N hb' h1 h2 => absurd h2 (by omega)

end ClaudeDCP
