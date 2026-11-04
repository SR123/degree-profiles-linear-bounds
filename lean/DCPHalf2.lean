/-
Agent D, round 4 (26 Sep 2026).  **HALF_b(b+2) is elementary**: the first point `N = b + 2` of the
window.  (Paper argument: work/BDM_PLAN.md §3.6; numerical check work/half_b2_check.py.)

Board `R × C`, `|R| = |C| = b + 2`, `F ∈ Z_b` vanishing on the rooks meeting row `x0`.
* `move_neg` : moving a cell inside its column to another free row (not `x0`) negates `F`
  (a column line through a `(b-1)`-rook has exactly three free rows, one of them `x0`);
* `swap_neg` : exchanging the columns of two cells negates `F` (three moves);
* `piece yb ys` : explicit pieces (base column `yb`, `ys ≠ yb`), vanishing on column `ys` and on
  row `x0`, in `Z_b`, summing to `F`;
* `half_succ_succ` : `DCP_b(b+1) → HALF_b(b+2)` (each piece is realised on the `(b+1)`-sub-board and
  extended by (E)).
Consequences: `dcpr_all2` (HALF needed only for `b + 3 ≤ N ≤ 2b - 1`), `dcpr_le_three`
(DCP_b(N) for `b ≤ 3`, all `N`, given `ColSplit`).
-/
import DCPRook
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ClaudeDCP

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {K : Type*} [CommRing K]

/-! ### Small combinatorial helpers -/

theorem sdiff_cols_insert (C : Finset α) (ρ : Finset (α × α)) (x y : α) :
    C \ colsOf (insert (x, y) ρ) = (C \ colsOf ρ).erase y := by
  ext z
  simp only [Finset.mem_sdiff, colsOf_insert, Finset.mem_insert, Finset.mem_erase]
  tauto

theorem sdiff_rows_insert (R : Finset α) (ρ : Finset (α × α)) (x y : α) :
    R \ rowsOf (insert (x, y) ρ) = (R \ rowsOf ρ).erase x := by
  ext z
  simp only [Finset.mem_sdiff, rowsOf_insert, Finset.mem_insert, Finset.mem_erase]
  tauto

theorem card_free_rows {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) :
    (R \ rowsOf ρ).card = R.card - ρ.card := by
  rw [Finset.card_sdiff_of_subset (rowsOf_subset h), card_rowsOf h.1]

theorem card_free_cols {R C : Finset α} {ρ : Finset (α × α)} (h : OnBoard R C ρ) :
    (C \ colsOf ρ).card = C.card - ρ.card := by
  rw [Finset.card_sdiff_of_subset (colsOf_subset h), card_colsOf h.1]

theorem rowsOf_erase_sub (ρ : Finset (α × α)) (p : α × α) : rowsOf (ρ.erase p) ⊆ rowsOf ρ :=
  fun x hx => by
    obtain ⟨y, hy⟩ := mem_rowsOf.mp hx
    exact rowsOf_mem (Finset.mem_of_mem_erase hy)

theorem colsOf_erase_sub (ρ : Finset (α × α)) (p : α × α) : colsOf (ρ.erase p) ⊆ colsOf ρ :=
  fun y hy => by
    obtain ⟨x, hx⟩ := mem_colsOf.mp hy
    exact colsOf_mem (Finset.mem_of_mem_erase hx)

/-- Replacing the column of a cell by a free column. -/
theorem onBoard_rep {R C : Finset α} {ρ : Finset (α × α)} (hρ : OnBoard R C ρ) {p : α × α}
    (hp : p ∈ ρ) {y' : α} (hy' : y' ∈ C) (hy'c : y' ∉ colsOf ρ) :
    OnBoard R C (insert (p.1, y') (ρ.erase p)) ∧ (insert (p.1, y') (ρ.erase p)).card = ρ.card := by
  have h1 : p.1 ∉ rowsOf (ρ.erase p) := not_mem_rowsOf_erase hρ.1 hp
  refine ⟨(hρ.erase p).insert (hρ.row_mem hp) h1 hy' (fun h => hy'c (colsOf_erase_sub ρ p h)), ?_⟩
  rw [card_insert_cell h1, card_erase_add_one hp]

theorem rowsOf_rep {ρ : Finset (α × α)} {p : α × α} (hp : p ∈ ρ) (y' : α) :
    rowsOf (insert (p.1, y') (ρ.erase p)) = rowsOf ρ := by
  conv_rhs => rw [← Finset.insert_erase hp]
  rw [rowsOf_insert, rowsOf_insert]

/-! ### Moves and swaps -/

section Moves

variable {R C : Finset α} {b : ℕ} {F : Finset (α × α) → K} {x0 : α}

/-- Moving a cell inside its column to another free row negates `F`. -/
theorem move_neg (hR : R.card = b + 2) (hZ : ColLines R C b F) (hx0 : x0 ∈ R)
    (hvan : ∀ ρ, OnBoard R C ρ → ρ.card = b → x0 ∈ rowsOf ρ → F ρ = 0)
    {ρ : Finset (α × α)} (hρ : OnBoard R C ρ) (hc : ρ.card + 1 = b) (hx0ρ : x0 ∉ rowsOf ρ)
    {y : α} (hy : y ∈ C) (hyc : y ∉ colsOf ρ) {x1 x2 : α} (hx1 : x1 ∈ R) (hx2 : x2 ∈ R)
    (hx1r : x1 ∉ rowsOf ρ) (hx2r : x2 ∉ rowsOf ρ) (h12 : x1 ≠ x2) (h10 : x1 ≠ x0)
    (h20 : x2 ≠ x0) : F (insert (x1, y) ρ) = -F (insert (x2, y) ρ) := by
  have hline := hZ ρ hρ hc y hy hyc
  have hn0 : x0 ∉ ({x1, x2} : Finset α) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm h10, Ne.symm h20⟩
  have hsub : ({x0, x1, x2} : Finset α) ⊆ R \ rowsOf ρ := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨hx0, hx0ρ⟩
    · exact Finset.mem_sdiff.mpr ⟨hx1, hx1r⟩
    · exact Finset.mem_sdiff.mpr ⟨hx2, hx2r⟩
  have hcard3 : ({x0, x1, x2} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem hn0, Finset.card_pair h12]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_free_rows hρ, hcard3]; omega)
  rw [← heq, Finset.sum_insert hn0, Finset.sum_pair h12] at hline
  have h0 : F (insert (x0, y) ρ) = 0 :=
    hvan _ (hρ.insert hx0 hx0ρ hy hyc) (by rw [card_insert_cell hx0ρ, hc])
      (by rw [rowsOf_insert]; exact Finset.mem_insert_self _ _)
  rw [h0, zero_add] at hline
  exact eq_neg_of_add_eq_zero_left hline

/-- Exchanging the columns of two cells negates `F` (three moves through the free row). -/
theorem swap_neg (hR : R.card = b + 2) (hZ : ColLines R C b F) (hx0 : x0 ∈ R)
    (hvan : ∀ ρ, OnBoard R C ρ → ρ.card = b → x0 ∈ rowsOf ρ → F ρ = 0)
    {σ : Finset (α × α)} (hσ : OnBoard R C σ) (hc : σ.card + 2 = b) (hx0σ : x0 ∉ rowsOf σ)
    {x1 x2 y1 y2 : α} (hx1 : x1 ∈ R) (hx2 : x2 ∈ R) (hx1r : x1 ∉ rowsOf σ)
    (hx2r : x2 ∉ rowsOf σ) (h12 : x1 ≠ x2) (h10 : x1 ≠ x0) (h20 : x2 ≠ x0) (hy1 : y1 ∈ C)
    (hy2 : y2 ∈ C) (hy1c : y1 ∉ colsOf σ) (hy2c : y2 ∉ colsOf σ) (hy12 : y1 ≠ y2) :
    F (insert (x1, y1) (insert (x2, y2) σ)) = -F (insert (x1, y2) (insert (x2, y1) σ)) := by
  -- the free row `m`
  have hcard4 : (R \ rowsOf σ).card = 4 := by rw [card_free_rows hσ]; omega
  have hm : (((R \ rowsOf σ).erase x0).erase x1).erase x2 |>.Nonempty := by
    apply Finset.card_pos.mp
    have h0m : x0 ∈ R \ rowsOf σ := Finset.mem_sdiff.mpr ⟨hx0, hx0σ⟩
    have h1m : x1 ∈ (R \ rowsOf σ).erase x0 :=
      Finset.mem_erase.mpr ⟨h10, Finset.mem_sdiff.mpr ⟨hx1, hx1r⟩⟩
    have h2m : x2 ∈ ((R \ rowsOf σ).erase x0).erase x1 :=
      Finset.mem_erase.mpr ⟨Ne.symm h12, Finset.mem_erase.mpr ⟨h20, Finset.mem_sdiff.mpr ⟨hx2, hx2r⟩⟩⟩
    rw [Finset.card_erase_of_mem h2m, Finset.card_erase_of_mem h1m, Finset.card_erase_of_mem h0m,
      hcard4]
    omega
  obtain ⟨m, hm⟩ := hm
  simp only [Finset.mem_erase, Finset.mem_sdiff] at hm
  obtain ⟨hm2, hm1, hm0, hmR, hmr⟩ := hm
  -- rows and columns of the intermediate rooks
  have r_ins : ∀ (a c : α) (τ : Finset (α × α)) (z : α), z ∉ rowsOf τ → z ≠ a →
      z ∉ rowsOf (insert (a, c) τ) := by
    intro a c τ z hz hza h
    rw [rowsOf_insert, Finset.mem_insert] at h
    rcases h with h | h
    · exact hza h
    · exact hz h
  have c_ins : ∀ (a c : α) (τ : Finset (α × α)) (z : α), z ∉ colsOf τ → z ≠ c →
      z ∉ colsOf (insert (a, c) τ) := by
    intro a c τ z hz hzc h
    rw [colsOf_insert, Finset.mem_insert] at h
    rcases h with h | h
    · exact hzc h
    · exact hz h
  have hcard1 : ∀ (a c : α), a ∉ rowsOf σ → (insert (a, c) σ).card + 1 = b := by
    intro a c ha
    rw [card_insert_cell ha]
    omega
  -- step 1: move `(x1, y1)` to `(m, y1)` over `insert (x2, y2) σ`
  have s1 : F (insert (x1, y1) (insert (x2, y2) σ)) = -F (insert (m, y1) (insert (x2, y2) σ)) :=
    move_neg hR hZ hx0 hvan (hσ.insert hx2 hx2r hy2 hy2c) (hcard1 x2 y2 hx2r)
      (r_ins x2 y2 σ x0 hx0σ (Ne.symm h20)) hy1 (c_ins x2 y2 σ y1 hy1c hy12) hx1 hmR
      (r_ins x2 y2 σ x1 hx1r h12) (r_ins x2 y2 σ m hmr hm2) (Ne.symm hm1) h10 hm0
  -- step 2: move `(x2, y2)` to `(x1, y2)` over `insert (m, y1) σ`
  have s2 : F (insert (x2, y2) (insert (m, y1) σ)) = -F (insert (x1, y2) (insert (m, y1) σ)) :=
    move_neg hR hZ hx0 hvan (hσ.insert hmR hmr hy1 hy1c) (hcard1 m y1 hmr)
      (r_ins m y1 σ x0 hx0σ (Ne.symm hm0)) hy2 (c_ins m y1 σ y2 hy2c (Ne.symm hy12)) hx2 hx1
      (r_ins m y1 σ x2 hx2r (Ne.symm hm2)) (r_ins m y1 σ x1 hx1r (Ne.symm hm1)) (Ne.symm h12)
      h20 h10
  -- step 3: move `(m, y1)` to `(x2, y1)` over `insert (x1, y2) σ`
  have s3 : F (insert (m, y1) (insert (x1, y2) σ)) = -F (insert (x2, y1) (insert (x1, y2) σ)) :=
    move_neg hR hZ hx0 hvan (hσ.insert hx1 hx1r hy2 hy2c) (hcard1 x1 y2 hx1r)
      (r_ins x1 y2 σ x0 hx0σ (Ne.symm h10)) hy1 (c_ins x1 y2 σ y1 hy1c hy12) hmR hx2
      (r_ins x1 y2 σ m hmr hm1) (r_ins x1 y2 σ x2 hx2r (Ne.symm h12)) hm2 hm0 h20
  calc F (insert (x1, y1) (insert (x2, y2) σ))
      = -F (insert (m, y1) (insert (x2, y2) σ)) := s1
    _ = -F (insert (x2, y2) (insert (m, y1) σ)) := by rw [Finset.insert_comm (m, y1) (x2, y2) σ]
    _ = F (insert (x1, y2) (insert (m, y1) σ)) := by rw [s2, neg_neg]
    _ = F (insert (m, y1) (insert (x1, y2) σ)) := by rw [Finset.insert_comm (x1, y2) (m, y1) σ]
    _ = -F (insert (x2, y1) (insert (x1, y2) σ)) := s3
    _ = -F (insert (x1, y2) (insert (x2, y1) σ)) := by
      rw [Finset.insert_comm (x2, y1) (x1, y2) σ]

end Moves

/-! ### The pieces -/

/-- The piece of `F` attached to the column `ys` (base column `yb`): zero on rooks using `ys`;
`F` itself on rooks missing `ys` and `yb`; otherwise `-F` of the rook with the `yb`-cell moved to
the other missing column. -/
def piece (C : Finset α) (F : Finset (α × α) → K) (yb ys : α) (ρ : Finset (α × α)) : K :=
  if ys ∈ colsOf ρ then 0 else if yb ∈ colsOf ρ then
    -∑ p ∈ ρ, ∑ y' ∈ (C \ colsOf ρ).erase ys,
      (if p.2 = yb then F (insert (p.1, y') (ρ.erase p)) else 0)
  else F ρ

section Pieces

variable {C : Finset α} {F : Finset (α × α) → K} {yb ys : α}

theorem piece_of_mem {ρ : Finset (α × α)} (h : ys ∈ colsOf ρ) : piece C F yb ys ρ = 0 := by
  unfold piece
  rw [if_pos h]

theorem piece_of_not_base {ρ : Finset (α × α)} (h : ys ∉ colsOf ρ) (hb : yb ∉ colsOf ρ) :
    piece C F yb ys ρ = F ρ := by
  unfold piece
  rw [if_neg h, if_neg hb]

theorem piece_of_base {ρ : Finset (α × α)} (hρ : IsRook ρ) (h : ys ∉ colsOf ρ) {xb : α}
    (hp : (xb, yb) ∈ ρ) {y' : α} (hy' : (C \ colsOf ρ).erase ys = {y'}) :
    piece C F yb ys ρ = -F (insert (xb, y') (ρ.erase (xb, yb))) := by
  unfold piece
  rw [if_neg h, if_pos (colsOf_mem hp), hy']
  congr 1
  rw [Finset.sum_eq_single (xb, yb)]
  · rw [Finset.sum_singleton, if_pos rfl]
  · intro p hpρ hne
    refine Finset.sum_eq_zero fun y'' _ => ?_
    rw [if_neg]
    intro h2
    exact hne (hρ p hpρ _ hp (Or.inr h2))
  · intro h'
    exact absurd hp h'

/-- The pieces vanish on the rooks meeting row `x0`. -/
theorem piece_of_x0 {R : Finset α} {b : ℕ} {x0 : α}
    (hvan : ∀ ρ, OnBoard R C ρ → ρ.card = b → x0 ∈ rowsOf ρ → F ρ = 0) {ρ : Finset (α × α)}
    (hρ : OnBoard R C ρ) (hc : ρ.card = b) (hx : x0 ∈ rowsOf ρ) : piece C F yb ys ρ = 0 := by
  unfold piece
  split_ifs with h1 h2
  · rfl
  · rw [neg_eq_zero]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun y' hy' => ?_
    split_ifs with h3
    · have hy'' := Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hy')
      obtain ⟨hon, hcard⟩ := onBoard_rep hρ hp hy''.1 hy''.2
      exact hvan _ hon (by rw [hcard, hc]) (by rw [rowsOf_rep hp]; exact hx)
    · rfl
  · exact hvan ρ hρ hc hx

end Pieces

/-! ### HALF at `N = b + 2` -/

theorem half_succ_succ {b : ℕ} (hb : 1 ≤ b) (hD : DCPR α K b (b + 1)) : HALF α K b (b + 2) := by
  intro R C hR hC x0 hx0 F hZ hvan
  obtain ⟨yb, hyb⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  -- (A) the pieces sum to `F`
  have hA : ∀ ρ, OnBoard R C ρ → ρ.card = b → F ρ = ∑ ys ∈ C.erase yb, piece C F yb ys ρ := by
    intro ρ hρ hc
    have hS : (C \ colsOf ρ).card = 2 := by rw [card_free_cols hρ, hC, hc]; omega
    by_cases hbase : yb ∈ colsOf ρ
    · obtain ⟨xb, hp⟩ := mem_colsOf.mp hbase
      obtain ⟨y1, y2, h12, hS12⟩ := Finset.card_eq_two.mp hS
      have hy1 : y1 ∈ C \ colsOf ρ := by rw [hS12]; simp
      have hy2 : y2 ∈ C \ colsOf ρ := by rw [hS12]; simp
      have hy1b : y1 ≠ yb := fun h => (Finset.mem_sdiff.mp hy1).2 (h ▸ hbase)
      have hy2b : y2 ≠ yb := fun h => (Finset.mem_sdiff.mp hy2).2 (h ▸ hbase)
      have hsub : ({y1, y2} : Finset α) ⊆ C.erase yb := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hy1b, (Finset.mem_sdiff.mp hy1).1⟩
        · exact Finset.mem_erase.mpr ⟨hy2b, (Finset.mem_sdiff.mp hy2).1⟩
      rw [← Finset.sum_subset hsub (fun z hz hz' => piece_of_mem (by
        by_contra hzc
        apply hz'
        have : z ∈ C \ colsOf ρ := Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hz).2, hzc⟩
        rw [hS12] at this
        exact this)), Finset.sum_pair h12]
      rw [piece_of_base hρ.1 (Finset.mem_sdiff.mp hy1).2 hp (y' := y2)
          (by rw [hS12, Finset.erase_insert (by simpa using h12)]),
        piece_of_base hρ.1 (Finset.mem_sdiff.mp hy2).2 hp (y' := y1)
          (by rw [hS12, Finset.pair_comm, Finset.erase_insert (by simpa using (Ne.symm h12))])]
      -- the row line through `ρ \ (xb, yb)` in row `xb`
      have hσon : OnBoard R C (ρ.erase (xb, yb)) := hρ.erase _
      have hxbσ : xb ∉ rowsOf (ρ.erase (xb, yb)) := not_mem_rowsOf_erase hρ.1 hp
      have hcσ : (ρ.erase (xb, yb)).card + 1 = b := by rw [card_erase_add_one hp, hc]
      have hline := hZ.1 _ hσon hcσ xb (hρ.row_mem hp) hxbσ
      have hfree : C \ colsOf (ρ.erase (xb, yb)) = insert yb (C \ colsOf ρ) := by
        conv_rhs => rw [← Finset.insert_erase hp]
        rw [sdiff_cols_insert, Finset.insert_erase (Finset.mem_sdiff.mpr
          ⟨hyb, not_mem_colsOf_erase hρ.1 hp⟩)]
      rw [hfree, Finset.sum_insert (fun h => (Finset.mem_sdiff.mp h).2 hbase), hS12,
        Finset.sum_pair h12, Finset.insert_erase hp] at hline
      linear_combination hline
    · have hybS : yb ∈ C \ colsOf ρ := Finset.mem_sdiff.mpr ⟨hyb, hbase⟩
      have hS1 : ((C \ colsOf ρ).erase yb).card = 1 := by
        rw [Finset.card_erase_of_mem hybS, hS]
      obtain ⟨y1, hy1⟩ := Finset.card_eq_one.mp hS1
      have hy1m : y1 ∈ (C \ colsOf ρ).erase yb := by rw [hy1]; exact Finset.mem_singleton_self _
      have hy1b := Finset.ne_of_mem_erase hy1m
      have hy1S := Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hy1m)
      rw [Finset.sum_eq_single y1]
      · rw [piece_of_not_base hy1S.2 hbase]
      · intro z hz hzne
        apply piece_of_mem
        by_contra hzc
        have : z ∈ (C \ colsOf ρ).erase yb :=
          Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1,
            Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hz).2, hzc⟩⟩
        rw [hy1] at this
        exact hzne (Finset.mem_singleton.mp this)
      · intro h
        exact absurd (Finset.mem_erase.mpr ⟨hy1b, hy1S.1⟩) h
  -- (B) each piece is in `Z_b`
  have hB : ∀ ys ∈ C.erase yb, ZB R C b (piece C F yb ys) := by
    intro ys hys
    have hysb : ys ≠ yb := Finset.ne_of_mem_erase hys
    have hysC : ys ∈ C := Finset.mem_of_mem_erase hys
    refine ⟨fun ρ' hρ' hc x hx hxr => ?_, fun ρ' hρ' hc y hy hyc => ?_⟩
    · -- row lines
      have hon : ∀ y ∈ C \ colsOf ρ', OnBoard R C (insert (x, y) ρ') ∧
          (insert (x, y) ρ').card = b := fun y hy =>
        ⟨hρ'.insert hx hxr (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2,
          by rw [card_insert_cell hxr, hc]⟩
      by_cases h0 : x0 ∈ rowsOf ρ' ∨ x = x0
      · refine Finset.sum_eq_zero fun y hy => piece_of_x0 hvan (hon y hy).1 (hon y hy).2 ?_
        rw [rowsOf_insert, Finset.mem_insert]
        rcases h0 with h | h
        · exact Or.inr h
        · exact Or.inl h.symm
      push_neg at h0
      obtain ⟨hx0ρ', hxx0⟩ := h0
      by_cases hysc : ys ∈ colsOf ρ'
      · refine Finset.sum_eq_zero fun y _ => piece_of_mem ?_
        rw [colsOf_insert]
        exact Finset.mem_insert_of_mem hysc
      have hS3 : (C \ colsOf ρ').card = 3 := by rw [card_free_cols hρ', hC]; omega
      have hysS : ys ∈ C \ colsOf ρ' := Finset.mem_sdiff.mpr ⟨hysC, hysc⟩
      obtain ⟨a, a', haa', hpair⟩ := Finset.card_eq_two.mp (by
        rw [Finset.card_erase_of_mem hysS, hS3] : ((C \ colsOf ρ').erase ys).card = 2)
      have hSeq : C \ colsOf ρ' = insert ys {a, a'} := by
        rw [← hpair, Finset.insert_erase hysS]
      have ha : a ∈ (C \ colsOf ρ').erase ys := by rw [hpair]; simp
      have ha' : a' ∈ (C \ colsOf ρ').erase ys := by rw [hpair]; simp
      have hays := Finset.ne_of_mem_erase ha
      have ha'ys := Finset.ne_of_mem_erase ha'
      have haS := Finset.mem_sdiff.mp (Finset.mem_of_mem_erase ha)
      have ha'S := Finset.mem_sdiff.mp (Finset.mem_of_mem_erase ha')
      have hysnot : ys ∉ ({a, a'} : Finset α) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hays, Ne.symm ha'ys⟩
      have hys0 : piece C F yb ys (insert (x, ys) ρ') = 0 :=
        piece_of_mem (by rw [colsOf_insert]; exact Finset.mem_insert_self _ _)
      rw [hSeq, Finset.sum_insert hysnot, Finset.sum_pair haa', hys0, zero_add]
      -- the free columns of `insert (x, a) ρ'` are `ys, a'`
      have hfreeA : ∀ c c' : α, c ∈ (C \ colsOf ρ').erase ys → c' ∈ (C \ colsOf ρ').erase ys →
          c ≠ c' → (C \ colsOf (insert (x, c) ρ')).erase ys = {c'} := by
        intro c c' hc hc' hcc'
        rw [sdiff_cols_insert, Finset.erase_right_comm]
        have hcard : (((C \ colsOf ρ').erase ys).erase c).card = 1 := by
          rw [Finset.card_erase_of_mem hc, hpair, Finset.card_pair haa']
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
        have : c' ∈ ((C \ colsOf ρ').erase ys).erase c := Finset.mem_erase.mpr ⟨Ne.symm hcc', hc'⟩
        rw [hz] at this ⊢
        rw [Finset.mem_singleton.mp this]
      have hrook : ∀ c ∈ C \ colsOf ρ', IsRook (insert (x, c) ρ') := fun c hc => (hon c hc).1.1
      have hysnc : ∀ c : α, c ≠ ys → ys ∉ colsOf (insert (x, c) ρ') := by
        intro c hc h
        rw [colsOf_insert, Finset.mem_insert] at h
        rcases h with h | h
        · exact hc h.symm
        · exact hysc h
      by_cases hbase : yb ∈ colsOf ρ'
      · obtain ⟨xb, hp⟩ := mem_colsOf.mp hbase
        have hxbx : xb ≠ x := fun h => hxr (h ▸ rowsOf_mem hp)
        have hne : ∀ c : α, (x, c) ≠ (xb, yb) := fun c h => hxbx (Prod.mk.inj h).1.symm
        rw [piece_of_base (hrook a (Finset.mem_of_mem_erase ha)) (hysnc a hays)
            (Finset.mem_insert_of_mem hp) (hfreeA a a' ha ha' haa'),
          piece_of_base (hrook a' (Finset.mem_of_mem_erase ha')) (hysnc a' ha'ys)
            (Finset.mem_insert_of_mem hp) (hfreeA a' a ha' ha (Ne.symm haa')),
          Finset.erase_insert_of_ne (hne a), Finset.erase_insert_of_ne (hne a')]
        set σ := ρ'.erase (xb, yb) with hσ
        have hσon : OnBoard R C σ := hρ'.erase _
        have hxbσ : xb ∉ rowsOf σ := not_mem_rowsOf_erase hρ'.1 hp
        have hxσ : x ∉ rowsOf σ := fun h => hxr (rowsOf_erase_sub ρ' _ h)
        have hx0σ : x0 ∉ rowsOf σ := fun h => hx0ρ' (rowsOf_erase_sub ρ' _ h)
        have hcσ : σ.card + 2 = b := by rw [hσ]; have := card_erase_add_one hp; omega
        have hswap := swap_neg hR hZ.2 hx0 hvan hσon hcσ hx0σ (hρ'.row_mem hp) hx hxbσ hxσ hxbx
          (fun h => hx0ρ' (by rw [← h]; exact rowsOf_mem hp)) hxx0 ha'S.1 haS.1
          (fun h => ha'S.2 (colsOf_erase_sub ρ' _ h)) (fun h => haS.2 (colsOf_erase_sub ρ' _ h))
          (Ne.symm haa')
        rw [hswap]
        ring
      · -- `yb` is one of `a, a'`
        have hybS : yb ∈ (C \ colsOf ρ').erase ys :=
          Finset.mem_erase.mpr ⟨Ne.symm hysb, Finset.mem_sdiff.mpr ⟨hyb, hbase⟩⟩
        have key : ∀ c : α, c ∈ (C \ colsOf ρ').erase ys → c ≠ yb →
            piece C F yb ys (insert (x, c) ρ') + piece C F yb ys (insert (x, yb) ρ') = 0 := by
          intro c hc hcb
          rw [piece_of_not_base (hysnc c (Finset.ne_of_mem_erase hc)) (by
                rw [colsOf_insert, Finset.mem_insert]; push_neg; exact ⟨Ne.symm hcb, hbase⟩),
            piece_of_base (hrook yb (Finset.mem_of_mem_erase hybS)) (hysnc yb (Ne.symm hysb))
              (Finset.mem_insert_self _ _) (hfreeA yb c hybS hc (Ne.symm hcb)),
            Finset.erase_insert (fun h => hbase (colsOf_mem h))]
          ring
        have hyb2 := hybS
        rw [hpair] at hyb2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyb2
        rcases hyb2 with h | h
        · rw [← h, add_comm]
          exact key a' ha' (fun e => haa' (e.trans h).symm)
        · rw [← h]
          exact key a ha (fun e => haa' (e.trans h))
    · -- column lines
      have hon : ∀ x ∈ R \ rowsOf ρ', OnBoard R C (insert (x, y) ρ') ∧
          (insert (x, y) ρ').card = b := fun x hx =>
        ⟨hρ'.insert (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2 hy hyc,
          by rw [card_insert_cell (Finset.mem_sdiff.mp hx).2, hc]⟩
      by_cases hysc : ys ∈ colsOf ρ' ∨ y = ys
      · refine Finset.sum_eq_zero fun x _ => piece_of_mem ?_
        rw [colsOf_insert, Finset.mem_insert]
        rcases hysc with h | h
        · exact Or.inr h
        · exact Or.inl h.symm
      push_neg at hysc
      obtain ⟨hysc, hyys⟩ := hysc
      have hS3 : (C \ colsOf ρ').card = 3 := by rw [card_free_cols hρ', hC]; omega
      have hyS : y ∈ C \ colsOf ρ' := Finset.mem_sdiff.mpr ⟨hy, hyc⟩
      have hysS : ys ∈ (C \ colsOf ρ').erase y :=
        Finset.mem_erase.mpr ⟨Ne.symm hyys, Finset.mem_sdiff.mpr ⟨hysC, hysc⟩⟩
      obtain ⟨y'', hy''⟩ := Finset.card_eq_one.mp (by
        rw [Finset.card_erase_of_mem hysS, Finset.card_erase_of_mem hyS, hS3] :
          (((C \ colsOf ρ').erase y).erase ys).card = 1)
      have hy''m : y'' ∈ ((C \ colsOf ρ').erase y).erase ys := by
        rw [hy'']; exact Finset.mem_singleton_self _
      have hy''ys := Finset.ne_of_mem_erase hy''m
      have hy''y := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy''m)
      have hy''S := Finset.mem_sdiff.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy''m))
      have hfree : ∀ x : α, (C \ colsOf (insert (x, y) ρ')).erase ys = {y''} := by
        intro x
        rw [sdiff_cols_insert, hy'']
      have hysnc : ∀ x : α, ys ∉ colsOf (insert (x, y) ρ') := by
        intro x h
        rw [colsOf_insert, Finset.mem_insert] at h
        rcases h with h | h
        · exact hyys h.symm
        · exact hysc h
      by_cases hyb : y = yb
      · -- the added cell is in the base column
        subst hyb
        have hterm : ∀ x ∈ R \ rowsOf ρ', piece C F y ys (insert (x, y) ρ') =
            -F (insert (x, y'') ρ') := by
          intro x hx
          rw [piece_of_base (hon x hx).1.1 (hysnc x) (Finset.mem_insert_self _ _) (hfree x),
            Finset.erase_insert (fun h => hyc (colsOf_mem h))]
        rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib,
          hZ.2 ρ' hρ' hc y'' hy''S.1 hy''S.2, neg_zero]
      by_cases hbase : yb ∈ colsOf ρ'
      · obtain ⟨xb, hp⟩ := mem_colsOf.mp hbase
        set ρ'' := insert (xb, y'') (ρ'.erase (xb, yb)) with hρ''
        have hon'' : OnBoard R C ρ'' := (onBoard_rep hρ' hp hy''S.1 hy''S.2).1
        have hc'' : ρ''.card = ρ'.card := (onBoard_rep hρ' hp hy''S.1 hy''S.2).2
        have hrows'' : rowsOf ρ'' = rowsOf ρ' := rowsOf_rep hp y''
        have hyc'' : y ∉ colsOf ρ'' := by
          rw [hρ'', colsOf_insert, Finset.mem_insert]
          push_neg
          exact ⟨Ne.symm hy''y, fun h => hyc (colsOf_erase_sub ρ' _ h)⟩
        have hterm : ∀ x ∈ R \ rowsOf ρ', piece C F yb ys (insert (x, y) ρ') =
            -F (insert (x, y) ρ'') := by
          intro x hx
          have hne : (x, y) ≠ (xb, yb) := fun h => hyc (by rw [(Prod.mk.inj h).2]; exact hbase)
          rw [piece_of_base (hon x hx).1.1 (hysnc x) (Finset.mem_insert_of_mem hp) (hfree x),
            Finset.erase_insert_of_ne hne, Finset.insert_comm (xb, y'') (x, y) (ρ'.erase (xb, yb)),
            ← hρ'']
        rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← hrows'',
          hZ.2 ρ'' hon'' (by rw [hc'']; exact hc) y hy hyc'', neg_zero]
      · -- `yb` is the other free column: the pieces are `F` itself
        have hterm : ∀ x ∈ R \ rowsOf ρ', piece C F yb ys (insert (x, y) ρ') =
            F (insert (x, y) ρ') := by
          intro x _
          refine piece_of_not_base (hysnc x) ?_
          rw [colsOf_insert, Finset.mem_insert]
          push_neg
          exact ⟨Ne.symm hyb, hbase⟩
        rw [Finset.sum_congr rfl hterm]
        exact hZ.2 ρ' hρ' hc y hy hyc
  -- (C) each piece vanishes off the sub-board `(R \ x0) × (C \ ys)`
  have hCv : ∀ ys ∈ C.erase yb, ∀ ρ, OnBoard R C ρ → ρ.card = b →
      ¬ ρ ⊆ (R.erase x0) ×ˢ (C.erase ys) → piece C F yb ys ρ = 0 := by
    intro ys _ ρ hρ hc hn
    obtain ⟨p, hp, hout⟩ := exists_out hρ hn
    rcases hout with h | h
    · have hpx : p.1 = x0 := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hρ.row_mem hp⟩)
      exact piece_of_x0 hvan hρ hc (hpx ▸ rowsOf_mem hp)
    · have hpy : p.2 = ys := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hρ.col_mem hp⟩)
      exact piece_of_mem (hpy ▸ colsOf_mem hp)
  -- realise each piece on its sub-board and extend
  have hreal : ∀ ys ∈ C.erase yb, Real R C b (piece C F yb ys) := by
    intro ys hys
    have hys' : ys ∈ C := Finset.mem_of_mem_erase hys
    have hZs := zb_mono (Finset.erase_subset _ _) (Finset.erase_subset _ _) (hB ys hys) (hCv ys hys)
    obtain ⟨c, hc, hFc⟩ := hD _ _ (by rw [Finset.card_erase_of_mem hx0, hR]; omega)
      (by rw [Finset.card_erase_of_mem hys', hC]; omega) _ hZs
    have hext := ext_eq (Finset.notMem_erase x0 R) (Finset.notMem_erase ys C) hc hFc hZs.2
      (by rw [Finset.card_erase_of_mem hys', hC]; omega)
      (by rw [Finset.insert_erase hx0, Finset.insert_erase hys']; exact hCv ys hys)
    rw [Finset.insert_erase hx0, Finset.insert_erase hys'] at hext
    have hfit := fitsAll_push_extP hc (Finset.notMem_erase x0 R) (Finset.notMem_erase ys C)
    rw [Finset.insert_erase hx0, Finset.insert_erase hys'] at hfit
    exact ⟨_, hfit, hext⟩
  choose! cs hcsF hcs using hreal
  refine ⟨∑ ys ∈ C.erase yb, cs ys, fitsAll_sum _ hcsF, fun ρ hρ hc => ?_⟩
  rw [hA ρ hρ hc, realFn_sum]
  exact Finset.sum_congr rfl fun ys hys => hcs ys hys ρ hρ hc

end ClaudeDCP

namespace ClaudeDCP

variable {α : Type*} [Fintype α] [DecidableEq α] {K : Type*} [CommRing K]

/-- **The reduction, improved**: with `HALF_b(b+2)` proved, `HALF` is needed only for
`b' + 3 ≤ N ≤ 2b' - 1` (so `b' ≥ 4`). -/
theorem dcpr_all2 (hsplit : ∀ (k : ℕ) (R C : Finset α), 2 * k + 1 ≤ C.card → ColSplit K R C k)
    (b : ℕ) (hhalf : ∀ b' N, b' ≤ b → b' + 3 ≤ N → N + 1 ≤ 2 * b' → HALF α K b' N) :
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
      by_cases h2' : M = k + 2
      · subst h2'
        exact dcpr_of_half (by omega) (ihk _) (half_succ_succ (by omega) ihM)
      by_cases h3 : M + 1 + 1 ≤ 2 * (k + 1)
      · exact dcpr_of_half (by omega) (ihk _) (hhalf (k + 1) (M + 1) le_rfl (by omega) h3)
      · exact dcpr_step (k := k) (N := M + 1) (by omega) (by simpa using ihM) (ihk _) (ihk _)
          (hsplit k)

/-- For `b ≤ 3` the (remaining) window is empty. -/
theorem dcpr_le_three (hsplit : ∀ (k : ℕ) (R C : Finset α), 2 * k + 1 ≤ C.card → ColSplit K R C k)
    {b : ℕ} (hb : b ≤ 3) : ∀ N, DCPR α K b N :=
  dcpr_all2 hsplit b fun b' N hb' h1 h2 => absurd h2 (by omega)

end ClaudeDCP
