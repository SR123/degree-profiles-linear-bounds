/-
Agent R, round 6 (26 Sep 2026).  Theorem GP of R_referee/work/HALF_PROOF.md §4 (the
generalised forcing statement), by induction on the board size.

Conditions are predicates `cc rc : α → ℕ → Prop` (column side, row side); `cc t d` stands for
the condition `(col, t+1, d)` of the paper (threshold "column > t", depth `d`).
* `Sat w C cc rc L` : `LIS(w | col > t) + d ≤ L` and `LIS(w | row > t) + d ≤ L`;
* `InQ R C cc rc ρ` : `|C_{≤t} \ cols ρ| < d` for some `cc t d`, or the row analogue;
* `GPStmt α K M` : Theorem GP for all boards of size `M`.
Main result: `gp : GPStmt α K M` for every `M`.
-/
import RForceBase

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RForce

open Finset ClaudeDCP BLemmaL

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- `w` satisfies the conditions `cc`, `rc` at length `L`. -/
def Sat (w : Equiv.Perm α) (C : Finset α) (cc rc : α → ℕ → Prop) (L : ℕ) : Prop :=
  (∀ t d, cc t d → lisOn w (C.filter (fun y => t < y)) + d ≤ L) ∧
  (∀ t d, rc t d → lisOn w (C.filter (fun y => t < w y)) + d ≤ L)

/-- The rooks violating a necessary condition (the set `Q` of HALF_PROOF §4.1). -/
def InQ (R C : Finset α) (cc rc : α → ℕ → Prop) (ρ : Finset (α × α)) : Prop :=
  (∃ t d, cc t d ∧ ((C.filter (fun y => y ≤ t)) \ colsOf ρ).card < d) ∨
  (∃ t d, rc t d ∧ ((R.filter (fun x => x ≤ t)) \ rowsOf ρ).card < d)

variable (α) (K : Type*) [CommRing K] in
/-- **Theorem GP** for boards of size `M`. -/
def GPStmt (M : ℕ) : Prop :=
  ∀ (R C : Finset α), R.card = M → C.card = M → ∀ (c L : ℕ), c + L = M →
    ∀ (cc rc : α → ℕ → Prop) (F : Finset (α × α) → K), ZB R C c F →
    (∀ w, Fits R C w → lisOn w C = L → Sat w C cc rc L → F (rhoOf w C) = 0) →
    (∀ ρ, OnBoard R C ρ → ρ.card = c → InQ R C cc rc ρ → F ρ = 0) →
    ∀ ρ, OnBoard R C ρ → ρ.card = c → F ρ = 0

/-! ### Auxiliary facts -/

theorem card_filter_fits {R C : Finset α} {w : Equiv.Perm α} (hw : Fits R C w) (p : α → Prop)
    [DecidablePred p] : (C.filter (fun y => p (w y))).card = (R.filter p).card := by
  have h : (C.filter (fun y => p (w y))).image w = R.filter p := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hy, hp⟩, rfl⟩
      exact ⟨(hw y).mpr hy, hp⟩
    · rintro ⟨hx, hp⟩
      refine ⟨w.symm x, ⟨(hw _).mp (by simpa using hx), by simpa using hp⟩, by simp⟩
  rw [← h, Finset.card_image_of_injective _ w.injective]

/-- The increasing bijection `C → R`. -/
theorem exists_incr {R C : Finset α} {M : ℕ} (hR : R.card = M) (hC : C.card = M) :
    ∃ w : Equiv.Perm α, Fits R C w ∧ IncOn w C := by
  let e : {x // x ∈ C} ≃o {x // x ∈ R} := (C.orderIsoOfFin hC).symm.trans (R.orderIsoOfFin hR)
  refine ⟨e.toEquiv.extendSubtype, fun y => ?_, fun y hy y' hy' hlt => ?_⟩
  · by_cases hy : y ∈ C
    · exact iff_of_true (Equiv.extendSubtype_mem e.toEquiv y hy) hy
    · exact iff_of_false (Equiv.extendSubtype_not_mem e.toEquiv y hy) hy
  · rw [Equiv.extendSubtype_apply_of_mem e.toEquiv y hy,
      Equiv.extendSubtype_apply_of_mem e.toEquiv y' hy']
    have h1 : e ⟨y, hy⟩ < e ⟨y', hy'⟩ :=
      e.strictMono (show (⟨y, hy⟩ : {x // x ∈ C}) < ⟨y', hy'⟩ from hlt)
    exact h1

theorem sdiff_insert_filter (C X : Finset α) (y : α) (p : α → Prop) [DecidablePred p] :
    (C.filter p) \ insert y X = ((C.erase y).filter p) \ X := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase, not_or]
  tauto

theorem card_filter_sdiff_le (C X : Finset α) (y : α) (p : α → Prop) [DecidablePred p] :
    ((C.filter p) \ X).card ≤ (((C.erase y).filter p) \ X).card + 1 := by
  refine le_trans (Finset.card_le_card (s := (C.filter p) \ X)
    (t := insert y (((C.erase y).filter p) \ X)) ?_) (Finset.card_insert_le _ _)
  intro z hz
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase] at hz ⊢
  by_cases hzy : z = y
  · exact Or.inl hzy
  · exact Or.inr ⟨⟨⟨hzy, hz.1.1⟩, hz.1.2⟩, hz.2⟩

/-- The count used for the new conditions at a row or column stage. -/
theorem card_new_le (C X : Finset α) {y y' t' : α} (hty : t' < y) (hy'C : y' ∈ C)
    (hy'X : y' ∉ X) (hy'y : y' < y) {d' : ℕ}
    (hlt : (((C.erase y).filter (fun z => z ≤ y)) \ X).card < d' + 1) :
    ((C.filter (fun z => z ≤ t')) \ insert y' X).card < d' := by
  set Mi := ((C.erase y).filter (fun z => z ≤ y)) \ X with hMi
  have hy'Mi : y' ∈ Mi := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ne_of_lt hy'y, hy'C⟩, le_of_lt hy'y⟩, hy'X⟩
  have hsub : (C.filter (fun z => z ≤ t')) \ insert y' X ⊆ Mi.erase y' := by
    intro z hz
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_insert, not_or] at hz
    obtain ⟨⟨hzC, hzt⟩, hzy', hzX⟩ := hz
    refine Finset.mem_erase.mpr ⟨hzy', Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨ne_of_lt (lt_of_le_of_lt hzt hty), hzC⟩,
        le_of_lt (lt_of_le_of_lt hzt hty)⟩, hzX⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_erase_add_one hy'Mi
  omega

theorem max_add_le {a b d L : ℕ} (ha : a + d ≤ L) (hb : b + d ≤ L) : max a b + d ≤ L := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

variable {K : Type*} [CommRing K]

/-! ### The case `c = 0` -/

theorem gp_zero {R C : Finset α} {M : ℕ} (hR : R.card = M) (hC : C.card = M)
    {cc rc : α → ℕ → Prop} {F : Finset (α × α) → K}
    (hPsi : ∀ w, Fits R C w → lisOn w C = M → Sat w C cc rc M → F (rhoOf w C) = 0)
    (hQ : ∀ ρ, OnBoard R C ρ → ρ.card = 0 → InQ R C cc rc ρ → F ρ = 0) :
    ∀ ρ, OnBoard R C ρ → ρ.card = 0 → F ρ = 0 := by
  intro ρ hρ hcard
  have hρe : ρ = ∅ := Finset.card_eq_zero.mp hcard
  subst hρe
  by_cases hdeg : (∃ t d, cc t d ∧ (C.filter (fun y => y ≤ t)).card < d) ∨
      (∃ t d, rc t d ∧ (R.filter (fun x => x ≤ t)).card < d)
  · apply hQ ∅ hρ hcard
    rcases hdeg with ⟨t, d, h, hlt⟩ | ⟨t, d, h, hlt⟩
    · exact Or.inl ⟨t, d, h, by simpa [colsOf] using hlt⟩
    · exact Or.inr ⟨t, d, h, by simpa [rowsOf] using hlt⟩
  · push_neg at hdeg
    obtain ⟨hdc, hdr⟩ := hdeg
    obtain ⟨w, hw, hinc⟩ := exists_incr hR hC
    have hlis : lisOn w C = M := le_antisymm (hC ▸ lisOn_le_card w C)
      (hC ▸ le_lisOn (Finset.Subset.refl C) hinc)
    have hlex : lexFirst w C = C := Finset.eq_of_subset_of_card_le (lexFirst_subset w C)
      (by rw [lexFirst_card, hlis, hC])
    have hrho : rhoOf w C = ∅ := by
      unfold rhoOf
      rw [hlex, Finset.sdiff_self, Finset.image_empty]
    have key := hPsi w hw hlis ⟨fun t d h => ?_, fun t d h => ?_⟩
    · rwa [hrho] at key
    · have h1 := lisOn_le_card w (C.filter (fun y => t < y))
      have h2 := Finset.filter_card_add_filter_neg_card_eq_card (s := C) (fun y => t < y)
      have h3 : C.filter (fun y => ¬ t < y) = C.filter (fun y => y ≤ t) :=
        Finset.filter_congr (fun y _ => not_lt)
      have h4 := hdc t d h
      rw [h3] at h2
      omega
    · have h1 := lisOn_le_card w (C.filter (fun y => t < w y))
      have h5 := card_filter_fits hw (fun x => t < x)
      have h2 := Finset.filter_card_add_filter_neg_card_eq_card (s := R) (fun x => t < x)
      have h3 : R.filter (fun x => ¬ t < x) = R.filter (fun x => x ≤ t) :=
        Finset.filter_congr (fun x _ => not_lt)
      have h4 := hdr t d h
      rw [h3] at h2
      omega

/-! ### Step 1: the bottom row -/

theorem step_row {M : ℕ} (ih : GPStmt α K M) {R C : Finset α} (hR : R.card = M + 1)
    (hC : C.card = M + 1) {k L : ℕ} (hkL : k + 1 + L = M + 1) {cc rc : α → ℕ → Prop}
    {F : Finset (α × α) → K} (hZ : ZB R C (k + 1) F)
    (hPsi : ∀ w, Fits R C w → lisOn w C = L → Sat w C cc rc L → F (rhoOf w C) = 0)
    (hQ : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → InQ R C cc rc ρ → F ρ = 0)
    {r0 : α} (hr0R : r0 ∈ R) (hr0 : ∀ x ∈ R, r0 ≤ x)
    (hnd : ∀ t d, rc t d → 0 < d → r0 ≤ t) :
    ∀ y, y ∈ C → ∀ σ, OnBoard (R.erase r0) (C.erase y) σ → σ.card = k →
      F (insert (r0, y) σ) = 0 := by
  intro y
  induction y using WellFoundedGT.induction with
  | _ y ihy =>
  intro hy
  have hRc : (R.erase r0).card = M := by rw [Finset.card_erase_of_mem hr0R, hR]; rfl
  have hCc : (C.erase y).card = M := by rw [Finset.card_erase_of_mem hy, hC]; rfl
  -- the conditions of the row stage
  let cc' : α → ℕ → Prop := fun t d =>
    cc t d ∨ (t = y ∧ d = 1) ∨ (t = y ∧ ∃ t' d', cc t' d' ∧ t' < y ∧ d = d' + 1)
  have hpsi : ∀ v, Fits (R.erase r0) (C.erase y) v → lisOn v (C.erase y) = L →
      Sat v (C.erase y) cc' rc L → F (insert (r0, y) (rhoOf v (C.erase y))) = 0 := by
    intro v hv hL hsat
    have hA := extP_agree hv
    have h0 : extP r0 y v y = r0 := extP_apply_self _ _ _
    have hag : ∀ z ∈ C, z ≠ y → extP r0 y v z = v z := fun z hz hne => (hA z hz hne).1
    have hgt : ∀ z ∈ C, z ≠ y → r0 < v z := fun z hz hne =>
      lt_of_le_of_ne (hr0 _ (hA z hz hne).2.1) (hA z hz hne).2.2.symm
    have hlow : ∀ z ∈ C, z ≠ y → z < y → r0 < v z := fun z hz hne _ => hgt z hz hne
    have hfit : Fits R C (extP r0 y v) := fits_extP' hv hr0R hy
    have hreg : lisOn v ((C.erase y).filter (fun z => y < z)) + 1 ≤ L :=
      hsat.1 y 1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hPsub : ∀ S ⊆ C, S.filter (fun z => y < z ∧ r0 < v z) ⊆
        (C.erase y).filter (fun z => y < z) := by
      intro S hS z hz
      obtain ⟨hzS, hzy, -⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ne_of_gt hzy, hS hzS⟩, hzy⟩
    have hlisw : lisOn (extP r0 y v) C = L := by
      rw [corner_lis h0 hag hlow (Finset.Subset.refl C) hy, hL]
      have := lisOn_mono v (hPsub C (Finset.Subset.refl C))
      exact max_eq_left (by omega)
    have hlex : lexFirst (extP r0 y v) C = lexFirst v (C.erase y) := by
      refine lexFirst_of_corner hag (by rw [hlisw, hL]) fun B hB hyB => ?_
      obtain ⟨hBC, hBinc, -⟩ := mem_maxChains.mp hB
      obtain ⟨hP, -⟩ := corner_chain h0 hag hlow hBC hyB hBinc
      have hIsub := lexFirst_subset v (C.erase y)
      have hnot : ¬ lexFirst v (C.erase y) ⊆ (C.erase y).filter (fun z => y < z) := by
        intro hsub
        have := le_lisOn hsub (lexFirst_incOn v _)
        rw [lexFirst_card, hL] at this
        omega
      obtain ⟨m, hmI, hm⟩ := Finset.not_subset.mp hnot
      have hmCy := hIsub hmI
      have hmy : m < y := by
        rcases lt_trichotomy m y with h | h | h
        · exact h
        · exact absurd h (Finset.ne_of_mem_erase hmCy)
        · exact absurd (Finset.mem_filter.mpr ⟨hmCy, h⟩) hm
      have hBge : ∀ b ∈ B, y ≤ b := fun b hb => by
        by_cases hby : b = y
        · exact hby ▸ le_rfl
        · exact le_of_lt (hP b (Finset.mem_erase.mpr ⟨hby, hb⟩)).1
      exact ⟨m, hmI, fun hmB => absurd (hBge m hmB) (not_le.mpr hmy),
        fun b hb _ => lt_of_lt_of_le hmy (hBge b hb)⟩
    have hrho := rhoOf_of_lexFirst_eq h0 hag hy hlex
    have hsatw : Sat (extP r0 y v) C cc rc L := by
      constructor
      · intro t d hcc
        by_cases hty : y ≤ t
        · have hyS : y ∉ C.filter (fun z => t < z) := fun h =>
            absurd (Finset.mem_filter.mp h).2 (not_lt.mpr hty)
          rw [corner_lis_not hag (Finset.filter_subset _ _) hyS]
          have hsub : C.filter (fun z => t < z) ⊆ (C.erase y).filter (fun z => t < z) := by
            intro z hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun e => hyS (e ▸ hz), hzC⟩, hzt⟩
          have e1 := lisOn_mono v hsub
          have s1 := hsat.1 t d (Or.inl hcc)
          omega
        · push_neg at hty
          have hyS : y ∈ C.filter (fun z => t < z) := Finset.mem_filter.mpr ⟨hy, hty⟩
          rw [corner_lis h0 hag hlow (Finset.filter_subset _ _) hyS]
          have h1 : (C.filter (fun z => t < z)).erase y ⊆ (C.erase y).filter (fun z => t < z) := by
            intro z hz
            obtain ⟨hzy, hz'⟩ := Finset.mem_erase.mp hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz'
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzy, hzC⟩, hzt⟩
          have e1 := lisOn_mono v h1
          have e2 := lisOn_mono v (hPsub _ (Finset.filter_subset (fun z => t < z) C))
          have s1 := hsat.1 t d (Or.inl hcc)
          have s2 := hsat.1 y (d + 1) (Or.inr (Or.inr ⟨rfl, t, d, hcc, hty, rfl⟩))
          exact max_add_le (by omega) (by omega)
      · intro t d hrc
        rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd
          have := lisOn_mono (extP r0 y v) (Finset.filter_subset (fun z => t < extP r0 y v z) C)
          omega
        · have hrt := hnd t d hrc hd
          have hyS : y ∉ C.filter (fun z => t < extP r0 y v z) := fun h => by
            have h2 := (Finset.mem_filter.mp h).2
            rw [h0] at h2
            exact absurd hrt (not_le.mpr h2)
          rw [corner_lis_not hag (Finset.filter_subset _ _) hyS]
          have hsub : C.filter (fun z => t < extP r0 y v z) ⊆
              (C.erase y).filter (fun z => t < v z) := by
            intro z hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz
            have hzy : z ≠ y := fun e => hyS (e ▸ hz)
            rw [hag z hzC hzy] at hzt
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzy, hzC⟩, hzt⟩
          have e1 := lisOn_mono v hsub
          have s1 := hsat.2 t d hrc
          omega
    have := hPsi _ hfit hlisw hsatw
    rwa [hrho] at this
  have hq : ∀ σ, OnBoard (R.erase r0) (C.erase y) σ → σ.card = k →
      InQ (R.erase r0) (C.erase y) cc' rc σ → F (insert (r0, y) σ) = 0 := by
    intro σ hσ hcard hq
    have hσbig : OnBoard R C σ := hσ.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    have hr0σ : r0 ∉ rowsOf σ := fun h => Finset.notMem_erase r0 R (rowsOf_subset hσ h)
    have hyσ : y ∉ colsOf σ := fun h => Finset.notMem_erase y C (colsOf_subset hσ h)
    have hρ : OnBoard R C (insert (r0, y) σ) := hσbig.insert hr0R hr0σ hy hyσ
    have hρc : (insert (r0, y) σ).card = k + 1 := by rw [card_insert_cell hr0σ, hcard]
    -- the row line of `F` through `σ` at row `r0`
    have line : (∀ y' ∈ C, y' ∉ colsOf σ → y' < y → F (insert (r0, y') σ) = 0) →
        F (insert (r0, y) σ) = 0 := by
      intro hsmall
      have hline := hZ.1 σ hσbig (by omega) r0 hr0R hr0σ
      rw [Finset.sum_eq_single_of_mem y (Finset.mem_sdiff.mpr ⟨hy, hyσ⟩) ?_] at hline
      · exact hline
      intro y' hy' hne
      obtain ⟨hy'C, hy'σ⟩ := Finset.mem_sdiff.mp hy'
      rcases lt_or_gt_of_ne hne with hlt' | hgt'
      · exact hsmall y' hy'C hy'σ hlt'
      · exact ihy y' hgt' hy'C σ ((hσbig.erase_row hr0σ).erase_col hy'σ) hcard
    rcases hq with ⟨t, d, hcc', hlt⟩ | ⟨t, d, hrc, hlt⟩
    · rcases hcc' with hcc | ⟨ht, hd⟩ | ⟨ht, t', d', hcc, ht'y, hd⟩
      · refine hQ _ hρ hρc (Or.inl ⟨t, d, hcc, ?_⟩)
        rw [colsOf_insert, sdiff_insert_filter C (colsOf σ) y (fun z => z ≤ t)]
        exact hlt
      · refine line fun y' hy'C hy'σ hy'y => ?_
        exfalso
        rw [ht, hd] at hlt
        have hmem : y' ∈ ((C.erase y).filter (fun z => z ≤ y)) \ colsOf σ :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨ne_of_lt hy'y, hy'C⟩, le_of_lt hy'y⟩, hy'σ⟩
        have := Finset.card_pos.mpr ⟨y', hmem⟩
        omega
      · refine line fun y' hy'C hy'σ hy'y => ?_
        rw [ht, hd] at hlt
        have hρ' : OnBoard R C (insert (r0, y') σ) := hσbig.insert hr0R hr0σ hy'C hy'σ
        have hρ'c : (insert (r0, y') σ).card = k + 1 := by rw [card_insert_cell hr0σ, hcard]
        refine hQ _ hρ' hρ'c (Or.inl ⟨t', d', hcc, ?_⟩)
        rw [colsOf_insert]
        exact card_new_le C (colsOf σ) ht'y hy'C hy'σ hy'y hlt
    · refine hQ _ hρ hρc (Or.inr ⟨t, d, hrc, ?_⟩)
      rw [rowsOf_insert, sdiff_insert_filter R (rowsOf σ) r0 (fun z => z ≤ t)]
      exact hlt
  exact ih (R.erase r0) (C.erase y) hRc hCc k L (by omega) cc' rc
    (fun σ => F (insert (r0, y) σ)) (zb_contract hZ hr0R hy) hpsi hq

/-! ### Step 3: the first column -/

theorem step_col {M : ℕ} (ih : GPStmt α K M) {R C : Finset α} (hR : R.card = M + 1)
    (hC : C.card = M + 1) {k L : ℕ} (hkL : k + 1 + L = M + 1) {cc rc : α → ℕ → Prop}
    {F : Finset (α × α) → K} (hZ : ZB R C (k + 1) F)
    (hPsi : ∀ w, Fits R C w → lisOn w C = L → Sat w C cc rc L → F (rhoOf w C) = 0)
    (hQ : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → InQ R C cc rc ρ → F ρ = 0)
    {r0 y0 : α} (hy0C : y0 ∈ C) (hy0 : ∀ z ∈ C, y0 ≤ z) (hrc0 : rc r0 1)
    (hnd : ∀ t d, cc t d → 0 < d → y0 ≤ t) :
    ∀ x, x ∈ R → r0 < x → ∀ σ, OnBoard (R.erase x) (C.erase y0) σ → σ.card = k →
      F (insert (x, y0) σ) = 0 := by
  intro x
  induction x using WellFoundedGT.induction with
  | _ x ihx =>
  intro hxR hr0x
  have hRc : (R.erase x).card = M := by rw [Finset.card_erase_of_mem hxR, hR]; rfl
  have hCc : (C.erase y0).card = M := by rw [Finset.card_erase_of_mem hy0C, hC]; rfl
  -- the conditions of the column stage
  let rc' : α → ℕ → Prop := fun t d =>
    rc t d ∨ (t = x ∧ ∃ t' d', rc t' d' ∧ t' < x ∧ d = d' + 1)
  have hpsi : ∀ v, Fits (R.erase x) (C.erase y0) v → lisOn v (C.erase y0) = L →
      Sat v (C.erase y0) cc rc' L → F (insert (x, y0) (rhoOf v (C.erase y0))) = 0 := by
    intro v hv hL hsat
    have hA := extP_agree hv
    have h0 : extP x y0 v y0 = x := extP_apply_self _ _ _
    have hag : ∀ z ∈ C, z ≠ y0 → extP x y0 v z = v z := fun z hz hne => (hA z hz hne).1
    have hlow : ∀ z ∈ C, z ≠ y0 → z < y0 → x < v z := fun z hz _ hlt =>
      absurd (hy0 z hz) (not_le.mpr hlt)
    have hfit : Fits R C (extP x y0 v) := fits_extP' hv hxR hy0C
    have hreg : lisOn v ((C.erase y0).filter (fun z => x < v z)) + 2 ≤ L :=
      hsat.2 x 2 (Or.inr ⟨rfl, r0, 1, hrc0, hr0x, rfl⟩)
    have hPsub : ∀ S ⊆ C, S.filter (fun z => y0 < z ∧ x < v z) ⊆
        (C.erase y0).filter (fun z => x < v z) := by
      intro S hS z hz
      obtain ⟨hzS, hzy, hzx⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ne_of_gt hzy, hS hzS⟩, hzx⟩
    have hlisw : lisOn (extP x y0 v) C = L := by
      rw [corner_lis h0 hag hlow (Finset.Subset.refl C) hy0C, hL]
      have := lisOn_mono v (hPsub C (Finset.Subset.refl C))
      exact max_eq_left (by omega)
    have hlex : lexFirst (extP x y0 v) C = lexFirst v (C.erase y0) := by
      refine lexFirst_of_corner hag (by rw [hlisw, hL]) fun B hB hyB => ?_
      exfalso
      obtain ⟨hBC, hBinc, hBcard⟩ := mem_maxChains.mp hB
      obtain ⟨hP, hinc'⟩ := corner_chain h0 hag hlow hBC hyB hBinc
      have hsub : B.erase y0 ⊆ C.filter (fun z => y0 < z ∧ x < v z) := fun z hz =>
        Finset.mem_filter.mpr ⟨hBC (Finset.mem_of_mem_erase hz), hP z hz⟩
      have e1 := le_lisOn hsub hinc'
      have e2 := lisOn_mono v (hPsub C (Finset.Subset.refl C))
      have e3 := Finset.card_erase_add_one hyB
      omega
    have hrho := rhoOf_of_lexFirst_eq h0 hag hy0C hlex
    have hsatw : Sat (extP x y0 v) C cc rc L := by
      constructor
      · intro t d hcc
        rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd
          have := lisOn_mono (extP x y0 v) (Finset.filter_subset (fun z => t < z) C)
          omega
        · have hyt := hnd t d hcc hd
          have hyS : y0 ∉ C.filter (fun z => t < z) := fun h =>
            absurd (Finset.mem_filter.mp h).2 (not_lt.mpr hyt)
          rw [corner_lis_not hag (Finset.filter_subset _ _) hyS]
          have hsub : C.filter (fun z => t < z) ⊆ (C.erase y0).filter (fun z => t < z) := by
            intro z hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun e => hyS (e ▸ hz), hzC⟩, hzt⟩
          have e1 := lisOn_mono v hsub
          have s1 := hsat.1 t d hcc
          omega
      · intro t d hrc
        by_cases hxt : x ≤ t
        · have hyS : y0 ∉ C.filter (fun z => t < extP x y0 v z) := fun h => by
            have h2 := (Finset.mem_filter.mp h).2
            rw [h0] at h2
            exact absurd hxt (not_le.mpr h2)
          rw [corner_lis_not hag (Finset.filter_subset _ _) hyS]
          have hsub : C.filter (fun z => t < extP x y0 v z) ⊆
              (C.erase y0).filter (fun z => t < v z) := by
            intro z hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz
            have hzy : z ≠ y0 := fun e => hyS (e ▸ hz)
            rw [hag z hzC hzy] at hzt
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzy, hzC⟩, hzt⟩
          have e1 := lisOn_mono v hsub
          have s1 := hsat.2 t d (Or.inl hrc)
          omega
        · push_neg at hxt
          have hyS : y0 ∈ C.filter (fun z => t < extP x y0 v z) :=
            Finset.mem_filter.mpr ⟨hy0C, by rw [h0]; exact hxt⟩
          rw [corner_lis h0 hag hlow (Finset.filter_subset _ _) hyS]
          have h1 : (C.filter (fun z => t < extP x y0 v z)).erase y0 ⊆
              (C.erase y0).filter (fun z => t < v z) := by
            intro z hz
            obtain ⟨hzy, hz'⟩ := Finset.mem_erase.mp hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz'
            rw [hag z hzC hzy] at hzt
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzy, hzC⟩, hzt⟩
          have e1 := lisOn_mono v h1
          have e2 := lisOn_mono v
            (hPsub _ (Finset.filter_subset (fun z => t < extP x y0 v z) C))
          have s1 := hsat.2 t d (Or.inl hrc)
          have s2 := hsat.2 x (d + 1) (Or.inr ⟨rfl, t, d, hrc, hxt, rfl⟩)
          exact max_add_le (by omega) (by omega)
    have := hPsi _ hfit hlisw hsatw
    rwa [hrho] at this
  have hq : ∀ σ, OnBoard (R.erase x) (C.erase y0) σ → σ.card = k →
      InQ (R.erase x) (C.erase y0) cc rc' σ → F (insert (x, y0) σ) = 0 := by
    intro σ hσ hcard hq
    have hσbig : OnBoard R C σ := hσ.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    have hxσ : x ∉ rowsOf σ := fun h => Finset.notMem_erase x R (rowsOf_subset hσ h)
    have hyσ : y0 ∉ colsOf σ := fun h => Finset.notMem_erase y0 C (colsOf_subset hσ h)
    have hρ : OnBoard R C (insert (x, y0) σ) := hσbig.insert hxR hxσ hy0C hyσ
    have hρc : (insert (x, y0) σ).card = k + 1 := by rw [card_insert_cell hxσ, hcard]
    rcases hq with ⟨t, d, hcc, hlt⟩ | ⟨t, d, hrc', hlt⟩
    · refine hQ _ hρ hρc (Or.inl ⟨t, d, hcc, ?_⟩)
      rw [colsOf_insert, sdiff_insert_filter C (colsOf σ) y0 (fun z => z ≤ t)]
      exact hlt
    · rcases hrc' with hrc | ⟨ht, t', d', hrc, ht'x, hd⟩
      · refine hQ _ hρ hρc (Or.inr ⟨t, d, hrc, ?_⟩)
        rw [rowsOf_insert, sdiff_insert_filter R (rowsOf σ) x (fun z => z ≤ t)]
        exact hlt
      · rw [ht, hd] at hlt
        -- the column line of `F` through `σ` at column `y0`
        have hline := hZ.2 σ hσbig (by omega) y0 hy0C hyσ
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_sdiff.mpr ⟨hxR, hxσ⟩) ?_] at hline
        · exact hline
        intro x' hx' hne
        obtain ⟨hx'R, hx'σ⟩ := Finset.mem_sdiff.mp hx'
        rcases lt_or_gt_of_ne hne with hlt' | hgt'
        · have hρ' : OnBoard R C (insert (x', y0) σ) := hσbig.insert hx'R hx'σ hy0C hyσ
          have hρ'c : (insert (x', y0) σ).card = k + 1 := by rw [card_insert_cell hx'σ, hcard]
          refine hQ _ hρ' hρ'c (Or.inr ⟨t', d', hrc, ?_⟩)
          rw [rowsOf_insert]
          exact card_new_le R (rowsOf σ) ht'x hx'R hx'σ hlt' hlt
        · exact ihx x' hgt' hx'R (lt_trans hr0x hgt') σ ((hσbig.erase_row hx'σ).erase_col hyσ)
            hcard
  exact ih (R.erase x) (C.erase y0) hRc hCc k L (by omega) cc rc'
    (fun σ => F (insert (x, y0) σ)) (zb_contract hZ hxR hy0C) hpsi hq

/-! ### Steps 2 and 4, and the induction -/

theorem gp_succ {M : ℕ} (ih : GPStmt α K M) : GPStmt α K (M + 1) := by
  intro R C hR hC c L hcL cc rc F hZ hPsi hQ
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0
    have hL : L = M + 1 := by omega
    subst hL
    exact gp_zero hR hC hPsi hQ
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  by_cases hdeg : (∃ t d, cc t d ∧ (C.filter (fun y => y ≤ t)).card < d) ∨
      (∃ t d, rc t d ∧ (R.filter (fun x => x ≤ t)).card < d)
  · intro ρ hρ hcard
    apply hQ ρ hρ hcard
    rcases hdeg with ⟨t, d, h, hlt⟩ | ⟨t, d, h, hlt⟩
    · exact Or.inl ⟨t, d, h, lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset) hlt⟩
    · exact Or.inr ⟨t, d, h, lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset) hlt⟩
  push_neg at hdeg
  obtain ⟨hdc, hdr⟩ := hdeg
  have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  set r0 := R.min' hRne with hr0def
  set y0 := C.min' hCne with hy0def
  have hr0R : r0 ∈ R := Finset.min'_mem _ _
  have hr0 : ∀ x ∈ R, r0 ≤ x := fun x hx => Finset.min'_le _ _ hx
  have hy0C : y0 ∈ C := Finset.min'_mem _ _
  have hy0 : ∀ z ∈ C, y0 ≤ z := fun z hz => Finset.min'_le _ _ hz
  have hndc : ∀ t d, cc t d → 0 < d → y0 ≤ t := by
    intro t d h hd
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (lt_of_lt_of_le hd (hdc t d h))
    obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz
    exact le_trans (hy0 z hzC) hzt
  have hndr : ∀ t d, rc t d → 0 < d → r0 ≤ t := by
    intro t d h hd
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (lt_of_lt_of_le hd (hdr t d h))
    obtain ⟨hzR, hzt⟩ := Finset.mem_filter.mp hz
    exact le_trans (hr0 z hzR) hzt
  -- Step 1
  have s1 := step_row ih hR hC (by omega) hZ hPsi hQ hr0R hr0 hndr
  have hrow : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → r0 ∈ rowsOf ρ → F ρ = 0 := by
    intro ρ hρ hcard hr
    obtain ⟨y, hy⟩ := mem_rowsOf.mp hr
    obtain ⟨hσ, hins, hc⟩ := rook_decomp hρ hy
    rw [← hins]
    exact s1 y (hρ.col_mem hy) _ hσ (by omega)
  -- Step 2
  let rc2 : α → ℕ → Prop := fun t d => rc t d ∨ (t = r0 ∧ d = 1)
  have hPsi2 : ∀ w, Fits R C w → lisOn w C = L → Sat w C cc rc2 L → F (rhoOf w C) = 0 :=
    fun w hw hl hs => hPsi w hw hl ⟨hs.1, fun t d h => hs.2 t d (Or.inl h)⟩
  have hQ2 : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → InQ R C cc rc2 ρ → F ρ = 0 := by
    intro ρ hρ hcard hq
    rcases hq with ⟨t, d, h, hlt⟩ | ⟨t, d, h | ⟨ht, hd⟩, hlt⟩
    · exact hQ ρ hρ hcard (Or.inl ⟨t, d, h, hlt⟩)
    · exact hQ ρ hρ hcard (Or.inr ⟨t, d, h, hlt⟩)
    · apply hrow ρ hρ hcard
      by_contra hr
      rw [ht, hd] at hlt
      have hmem : r0 ∈ (R.filter (fun x => x ≤ r0)) \ rowsOf ρ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hr0R, le_rfl⟩, hr⟩
      have := Finset.card_pos.mpr ⟨r0, hmem⟩
      omega
  have hndr2 : ∀ t d, rc2 t d → 0 < d → r0 ≤ t := by
    intro t d h hd
    rcases h with h | ⟨ht, -⟩
    · exact hndr t d h hd
    · exact ht ▸ le_rfl
  -- Step 3
  have s3 := step_col ih hR hC (by omega) hZ hPsi2 hQ2 hy0C hy0 (Or.inr ⟨rfl, rfl⟩) hndc
  have hcol : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → y0 ∈ colsOf ρ → F ρ = 0 := by
    intro ρ hρ hcard hc
    obtain ⟨x, hx⟩ := mem_colsOf.mp hc
    by_cases hxr : x = r0
    · exact hrow ρ hρ hcard (mem_rowsOf.mpr ⟨y0, hxr ▸ hx⟩)
    · obtain ⟨hσ, hins, hc'⟩ := rook_decomp hρ hx
      rw [← hins]
      exact s3 x (hρ.row_mem hx) (lt_of_le_of_ne (hr0 x (hρ.row_mem hx)) (Ne.symm hxr)) _ hσ
        (by omega)
  -- Step 4 (shift)
  have hvan : ∀ ρ, OnBoard R C ρ → ρ.card = k + 1 → ¬ ρ ⊆ (R.erase r0) ×ˢ (C.erase y0) →
      F ρ = 0 := by
    intro ρ hρ hcard hn
    obtain ⟨p, hp, hout⟩ := exists_out hρ hn
    rcases hout with h | h
    · have hp1 : p.1 = r0 := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hρ.row_mem hp⟩)
      exact hrow ρ hρ hcard (hp1 ▸ rowsOf_mem hp)
    · have hp2 : p.2 = y0 := by
        by_contra hne
        exact h (Finset.mem_erase.mpr ⟨hne, hρ.col_mem hp⟩)
      exact hcol ρ hρ hcard (hp2 ▸ colsOf_mem hp)
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · intro ρ hρ hcard
    apply hrow ρ hρ hcard
    have hrows : rowsOf ρ = R := Finset.eq_of_subset_of_card_le (rowsOf_subset hρ)
      (by rw [card_rowsOf hρ.1, hcard, hR]; omega)
    rw [hrows]
    exact hr0R
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hRc : (R.erase r0).card = M := by rw [Finset.card_erase_of_mem hr0R, hR]; rfl
  have hCc : (C.erase y0).card = M := by rw [Finset.card_erase_of_mem hy0C, hC]; rfl
  have hpsi : ∀ v, Fits (R.erase r0) (C.erase y0) v → lisOn v (C.erase y0) = L' →
      Sat v (C.erase y0) (fun t d => cc t (d + 1)) (fun t d => rc2 t (d + 1)) L' →
      F (rhoOf v (C.erase y0)) = 0 := by
    intro v hv hL hsat
    have hA := extP_agree hv
    have h0 : extP r0 y0 v y0 = r0 := extP_apply_self _ _ _
    have hag : ∀ z ∈ C, z ≠ y0 → extP r0 y0 v z = v z := fun z hz hne => (hA z hz hne).1
    have hall : ∀ z ∈ C, z ≠ y0 → y0 < z ∧ r0 < v z := fun z hz hne =>
      ⟨lt_of_le_of_ne (hy0 z hz) (Ne.symm hne),
        lt_of_le_of_ne (hr0 _ (hA z hz hne).2.1) (hA z hz hne).2.2.symm⟩
    have hfit : Fits R C (extP r0 y0 v) := fits_extP' hv hr0R hy0C
    have hlisw : lisOn (extP r0 y0 v) C = L' + 1 := by
      rw [shift_lis h0 hag hall hy0C, hL]
    have hrho := shift_rhoOf h0 hag hall hy0C
    have hsatw : Sat (extP r0 y0 v) C cc rc2 (L' + 1) := by
      constructor
      · intro t d hcc
        rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd
          have := lisOn_mono (extP r0 y0 v) (Finset.filter_subset (fun z => t < z) C)
          omega
        · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          have hyt := hndc t (d' + 1) hcc hd
          have hyS : y0 ∉ C.filter (fun z => t < z) := fun h =>
            absurd (Finset.mem_filter.mp h).2 (not_lt.mpr hyt)
          rw [corner_lis_not hag (Finset.filter_subset _ _) hyS]
          have hsub : C.filter (fun z => t < z) ⊆ (C.erase y0).filter (fun z => t < z) := by
            intro z hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun e => hyS (e ▸ hz), hzC⟩, hzt⟩
          have e1 := lisOn_mono v hsub
          have s1 := hsat.1 t d' hcc
          omega
      · intro t d hrc
        rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd
          have := lisOn_mono (extP r0 y0 v)
            (Finset.filter_subset (fun z => t < extP r0 y0 v z) C)
          omega
        · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          have hrt := hndr2 t (d' + 1) hrc hd
          have hyS : y0 ∉ C.filter (fun z => t < extP r0 y0 v z) := fun h => by
            have h2 := (Finset.mem_filter.mp h).2
            rw [h0] at h2
            exact absurd hrt (not_le.mpr h2)
          rw [corner_lis_not hag (Finset.filter_subset _ _) hyS]
          have hsub : C.filter (fun z => t < extP r0 y0 v z) ⊆
              (C.erase y0).filter (fun z => t < v z) := by
            intro z hz
            obtain ⟨hzC, hzt⟩ := Finset.mem_filter.mp hz
            have hzy : z ≠ y0 := fun e => hyS (e ▸ hz)
            rw [hag z hzC hzy] at hzt
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hzy, hzC⟩, hzt⟩
          have e1 := lisOn_mono v hsub
          have s1 := hsat.2 t d' hrc
          omega
    have := hPsi2 _ hfit hlisw hsatw
    rwa [hrho] at this
  have hq : ∀ σ, OnBoard (R.erase r0) (C.erase y0) σ → σ.card = k + 1 →
      InQ (R.erase r0) (C.erase y0) (fun t d => cc t (d + 1)) (fun t d => rc2 t (d + 1)) σ →
      F σ = 0 := by
    intro σ hσ hcard hq
    have hσbig : OnBoard R C σ := hσ.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    apply hQ2 σ hσbig hcard
    rcases hq with ⟨t, d, h, hlt⟩ | ⟨t, d, h, hlt⟩
    · refine Or.inl ⟨t, d + 1, h, ?_⟩
      have := card_filter_sdiff_le C (colsOf σ) y0 (fun z => z ≤ t)
      omega
    · refine Or.inr ⟨t, d + 1, h, ?_⟩
      have := card_filter_sdiff_le R (rowsOf σ) r0 (fun z => z ≤ t)
      omega
  have hsmall := ih (R.erase r0) (C.erase y0) hRc hCc (k + 1) L' (by omega)
    (fun t d => cc t (d + 1)) (fun t d => rc2 t (d + 1)) F
    (zb_mono (Finset.erase_subset _ _) (Finset.erase_subset _ _) hZ hvan) hpsi hq
  intro ρ hρ hcard
  by_cases hsub : ρ ⊆ (R.erase r0) ×ˢ (C.erase y0)
  · exact hsmall ρ ⟨hρ.1, hsub⟩ hcard
  · exact hvan ρ hρ hcard hsub

/-- **Theorem GP** (HALF_PROOF §4), for every board size. -/
theorem gp (M : ℕ) : GPStmt α K M := by
  induction M with
  | zero =>
    intro R C hR hC c L hcL cc rc F hZ hPsi hQ
    have hc0 : c = 0 := by omega
    have hL0 : L = 0 := by omega
    subst hc0
    subst hL0
    exact gp_zero hR hC hPsi hQ
  | succ M ih => exact gp_succ ih

end RForce
