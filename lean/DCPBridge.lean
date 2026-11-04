/-
Agent D, round 4 (26 Sep 2026).  Bridge between the rook language of `DCPRook` and the tuple
language of B's `BLemmaD` (copied verbatim into this folder), and the proof of the rook form of
Lemma D (`ColSplit`) from `BExact.lemmaD`.

* `rk s t` : the rook placement `{(s i, t i)}` of a pair of partial tuples (`ι → Option α`).
* `tup v`  : the total tuple `i ↦ some (v i)`.
* `exists_enum` : every `k`-rook of a board is `rk (tup u) (tup v)` with `u, v` injective;
  `exists_perm_of_rk_eq` : two such enumerations differ by a permutation of positions.
* `gFn C F s` : the column function `t ↦ F (rk s t)` (on injective tuples into `C`);
  `gFn_mem_Soc` : it lies in `Soc_k(C)` when the row lines of `F` vanish.
* `PiOf π C y` : the rook-language transport of B's `π_y` (applied to the column factor);
  `PiOf_rk` : its value on `rk (tup u) (tup v)` is `π_y (gFn C F (tup u)) (tup v)` (uses the
  `S_k`-equivariance of `π_y`).
* `colSplit` : **`ColSplit K R C k` for `2k + 1 ≤ |C|`**, from `BExact.lemmaD`.
* `dcpr_of_half`-style corollaries: `dcpr_all'` (DCP_b(N) for all N from HALF in the window) and
  `dcpr_le_two'` (DCP_b(N) for all N, `b ≤ 2`, unconditional).
-/
import DCPRook
import BLemmaD
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ClaudeDCP

open Finset Function BExact

section Tuples

variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rook placement `{(s i, t i)}` of two partial tuples. -/
def rk (s t : ι → Option α) : Finset (α × α) :=
  univ.filter (fun p => ∃ i, s i = some p.1 ∧ t i = some p.2)

theorem mem_rk {s t : ι → Option α} {p : α × α} :
    p ∈ rk s t ↔ ∃ i, s i = some p.1 ∧ t i = some p.2 := by
  simp [rk]

/-- A total tuple. -/
def tup (v : ι → α) : ι → Option α := fun i => some (v i)

theorem tup_update (v : ι → α) (i : ι) (x : α) :
    tup (update v i x) = update (tup v) i (some x) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [tup]
  · simp [tup, update_of_ne h]

theorem good_tup {L : Finset α} {v : ι → α} (hv : ∀ i, v i ∈ L) (hinj : Injective v) :
    Good (univ : Finset ι) L (tup v) :=
  ⟨fun j => by simp [tup], fun j y h => by
    simp only [tup, Option.some.injEq] at h
    rw [← h]
    exact hv j,
   fun j k y hj hk => by
    simp only [tup, Option.some.injEq] at hj hk
    exact hinj (hj.trans hk.symm)⟩

theorem good_tup_mem {L : Finset α} {v : ι → α} (h : Good (univ : Finset ι) L (tup v)) (i : ι) :
    v i ∈ L :=
  h.val i (v i) rfl

theorem good_tup_inj {L : Finset α} {v : ι → α} (h : Good (univ : Finset ι) L (tup v)) :
    Injective v :=
  fun i j hij => h.inj i j (v i) rfl (by rw [hij]; rfl)

theorem exists_tup {L : Finset α} {t : ι → Option α} (h : Good (univ : Finset ι) L t) :
    ∃ v : ι → α, t = tup v := by
  have hs : ∀ i, (t i).isSome := fun i =>
    Option.isSome_iff_ne_none.mpr ((h.dom i).mpr (mem_univ i))
  exact ⟨fun i => (t i).get (hs i), funext fun i => (Option.some_get (hs i)).symm⟩

theorem rk_tup (u v : ι → α) : rk (tup u) (tup v) = univ.image (fun i => (u i, v i)) := by
  ext p
  simp only [mem_rk, tup, Option.some.injEq, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, Prod.ext h1 h2⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl, rfl⟩

theorem mem_rk_tup {u v : ι → α} {p : α × α} : p ∈ rk (tup u) (tup v) ↔ ∃ i, u i = p.1 ∧ v i = p.2 := by
  simp [mem_rk, tup]

theorem card_rk_tup {u : ι → α} (hu : Injective u) (v : ι → α) :
    (rk (tup u) (tup v)).card = Fintype.card ι := by
  rw [rk_tup, Finset.card_image_of_injective _ (fun i j h => hu (Prod.mk.inj h).1),
    Finset.card_univ]

theorem onBoard_rk_tup {R C : Finset α} {u v : ι → α} (huR : ∀ i, u i ∈ R) (hu : Injective u)
    (hvC : ∀ i, v i ∈ C) (hv : Injective v) : OnBoard R C (rk (tup u) (tup v)) := by
  refine ⟨fun p hp q hq h => ?_, fun p hp => ?_⟩
  · obtain ⟨i, hi1, hi2⟩ := mem_rk_tup.mp hp
    obtain ⟨j, hj1, hj2⟩ := mem_rk_tup.mp hq
    rcases h with h | h
    · have hij : i = j := hu (by rw [hi1, hj1, h])
      subst hij
      exact Prod.ext h (hi2.symm.trans hj2)
    · have hij : i = j := hv (by rw [hi2, hj2, h])
      subst hij
      exact Prod.ext (hi1.symm.trans hj1) h
  · obtain ⟨i, hi1, hi2⟩ := mem_rk_tup.mp hp
    exact Finset.mem_product.mpr ⟨hi1 ▸ huR i, hi2 ▸ hvC i⟩

theorem mem_rowsOf_rk_tup {u v : ι → α} {x : α} : x ∈ rowsOf (rk (tup u) (tup v)) ↔ ∃ i, u i = x := by
  rw [mem_rowsOf]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨i, h1, -⟩ := mem_rk_tup.mp hy
    exact ⟨i, h1⟩
  · rintro ⟨i, rfl⟩
    exact ⟨v i, mem_rk_tup.mpr ⟨i, rfl, rfl⟩⟩

theorem mem_colsOf_rk_tup {u v : ι → α} {y : α} : y ∈ colsOf (rk (tup u) (tup v)) ↔ ∃ i, v i = y := by
  rw [mem_colsOf]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨i, -, h2⟩ := mem_rk_tup.mp hx
    exact ⟨i, h2⟩
  · rintro ⟨i, rfl⟩
    exact ⟨u i, mem_rk_tup.mpr ⟨i, rfl, rfl⟩⟩

/-- Removing position `i` from the column tuple removes the cell `(u i, v i)`. -/
theorem rk_erase_col {u : ι → α} (hu : Injective u) (v : ι → α) (i : ι) :
    rk (tup u) (update (tup v) i none) = (rk (tup u) (tup v)).erase (u i, v i) := by
  ext p
  rw [Finset.mem_erase, mem_rk, mem_rk_tup]
  constructor
  · rintro ⟨j, h1, h2⟩
    have hj : j ≠ i := by rintro rfl; simp at h2
    rw [update_of_ne hj] at h2
    simp only [tup, Option.some.injEq] at h1 h2
    refine ⟨fun h => hj (hu (h1.trans (congrArg Prod.fst h))), j, h1, h2⟩
  · rintro ⟨hne, j, h1, h2⟩
    have hj : j ≠ i := by
      rintro rfl
      exact hne (Prod.ext h1.symm h2.symm)
    exact ⟨j, by simp [tup, h1], by rw [update_of_ne hj]; simp [tup, h2]⟩

/-- Removing position `i` from the row tuple removes the cell `(u i, v i)`. -/
theorem rk_erase_row (u : ι → α) {v : ι → α} (hv : Injective v) (i : ι) :
    rk (update (tup u) i none) (tup v) = (rk (tup u) (tup v)).erase (u i, v i) := by
  ext p
  rw [Finset.mem_erase, mem_rk, mem_rk_tup]
  constructor
  · rintro ⟨j, h1, h2⟩
    have hj : j ≠ i := by rintro rfl; simp at h1
    rw [update_of_ne hj] at h1
    simp only [tup, Option.some.injEq] at h1 h2
    refine ⟨fun h => hj (hv (h2.trans (congrArg Prod.snd h))), j, h1, h2⟩
  · rintro ⟨hne, j, h1, h2⟩
    have hj : j ≠ i := by
      rintro rfl
      exact hne (Prod.ext h1.symm h2.symm)
    exact ⟨j, by rw [update_of_ne hj]; simp [tup, h1], by simp [tup, h2]⟩

theorem rk_update_col (u v : ι → α) (i : ι) (y : α) :
    rk (tup u) (update (tup v) i (some y)) = insert (u i, y) (rk (tup u) (update (tup v) i none)) := by
  ext p
  rw [Finset.mem_insert, mem_rk, mem_rk]
  constructor
  · rintro ⟨j, h1, h2⟩
    by_cases hj : j = i
    · subst hj
      simp only [update_self, Option.some.injEq, tup] at h1 h2
      exact Or.inl (Prod.ext h1.symm h2.symm)
    · rw [update_of_ne hj] at h2
      exact Or.inr ⟨j, h1, by rw [update_of_ne hj]; exact h2⟩
  · rintro (rfl | ⟨j, h1, h2⟩)
    · exact ⟨i, rfl, by simp⟩
    · have hj : j ≠ i := by rintro rfl; simp at h2
      rw [update_of_ne hj] at h2
      exact ⟨j, h1, by rw [update_of_ne hj]; exact h2⟩

theorem rk_update_row (u v : ι → α) (i : ι) (x : α) :
    rk (update (tup u) i (some x)) (tup v) = insert (x, v i) (rk (update (tup u) i none) (tup v)) := by
  ext p
  rw [Finset.mem_insert, mem_rk, mem_rk]
  constructor
  · rintro ⟨j, h1, h2⟩
    by_cases hj : j = i
    · subst hj
      simp only [update_self, Option.some.injEq, tup] at h1 h2
      exact Or.inl (Prod.ext h1.symm h2.symm)
    · rw [update_of_ne hj] at h1
      exact Or.inr ⟨j, by rw [update_of_ne hj]; exact h1, h2⟩
  · rintro (rfl | ⟨j, h1, h2⟩)
    · exact ⟨i, by simp, rfl⟩
    · have hj : j ≠ i := by rintro rfl; simp at h1
      rw [update_of_ne hj] at h1
      exact ⟨j, by rw [update_of_ne hj]; exact h1, h2⟩

theorem injective_update {w : ι → α} (hinj : Injective w) {i : ι} {y : α}
    (hy : ∀ j, j ≠ i → w j ≠ y) : Injective (update w i y) := by
  intro a b hab
  by_cases ha : a = i <;> by_cases hb : b = i
  · rw [ha, hb]
  · subst ha
    rw [update_self, update_of_ne hb] at hab
    exact absurd hab.symm (hy b hb)
  · subst hb
    rw [update_self, update_of_ne ha] at hab
    exact absurd hab (hy a ha)
  · rw [update_of_ne ha, update_of_ne hb] at hab
    exact hinj hab

theorem mem_colsOf_rk_erase {u v : ι → α} (hu : Injective u) {i : ι} {y : α} :
    y ∈ colsOf (rk (tup u) (update (tup v) i none)) ↔ ∃ j, j ≠ i ∧ v j = y := by
  rw [rk_erase_col hu, mem_colsOf]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
    obtain ⟨j, h1, h2⟩ := mem_rk_tup.mp hx
    refine ⟨j, fun h => hne ?_, h2⟩
    subst h
    exact Prod.ext h1.symm h2.symm
  · rintro ⟨j, hj, rfl⟩
    exact ⟨u j, Finset.mem_erase.mpr ⟨fun h => hj (hu (congrArg Prod.fst h)),
      mem_rk_tup.mpr ⟨j, rfl, rfl⟩⟩⟩

theorem mem_rowsOf_rk_erase {u v : ι → α} (hv : Injective v) {i : ι} {x : α} :
    x ∈ rowsOf (rk (update (tup u) i none) (tup v)) ↔ ∃ j, j ≠ i ∧ u j = x := by
  rw [rk_erase_row u hv, mem_rowsOf]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨hne, hy⟩ := Finset.mem_erase.mp hy
    obtain ⟨j, h1, h2⟩ := mem_rk_tup.mp hy
    refine ⟨j, fun h => hne ?_, h1⟩
    subst h
    exact Prod.ext h1.symm h2.symm
  · rintro ⟨j, hj, rfl⟩
    exact ⟨v j, Finset.mem_erase.mpr ⟨fun h => hj (hv (congrArg Prod.snd h)),
      mem_rk_tup.mpr ⟨j, rfl, rfl⟩⟩⟩

theorem good_update_iff {C : Finset α} {u w : ι → α} (hu : Injective u) (hw : ∀ j, w j ∈ C)
    (hinj : Injective w) (i : ι) (y : α) :
    Good (univ : Finset ι) C (update (tup w) i (some y)) ↔
      y ∈ C \ colsOf (rk (tup u) (update (tup w) i none)) := by
  rw [Finset.mem_sdiff, mem_colsOf_rk_erase hu]
  constructor
  · intro g
    refine ⟨g.val i y (by simp), ?_⟩
    rintro ⟨j, hj, hwj⟩
    exact hj (g.inj j i y (by rw [update_of_ne hj]; simp [tup, hwj]) (by simp))
  · rintro ⟨hyC, hy⟩
    rw [← tup_update]
    refine good_tup (fun j => ?_) (injective_update hinj fun j hj h => hy ⟨j, hj, h⟩)
    by_cases hj : j = i
    · subst hj
      simpa using hyC
    · rw [update_of_ne hj]
      exact hw j

/-! ### Enumerations of rooks -/

/-- An enumeration of a finite set with `|ι|` elements. -/
noncomputable def enumE (ρ : Finset (α × α)) (h : ρ.card = Fintype.card ι) : ι ≃ ρ :=
  Fintype.equivOfCardEq (by rw [Fintype.card_coe, h])

theorem rk_enum (ρ : Finset (α × α)) (e : ι ≃ ρ) :
    rk (tup fun i => (e i).1.1) (tup fun i => (e i).1.2) = ρ := by
  ext p
  rw [mem_rk_tup]
  constructor
  · rintro ⟨i, h1, h2⟩
    have : (e i).1 = p := Prod.ext h1 h2
    rw [← this]
    exact (e i).2
  · intro hp
    exact ⟨e.symm ⟨p, hp⟩, by simp, by simp⟩

theorem enum_injective {ρ : Finset (α × α)} (hρ : IsRook ρ) (e : ι ≃ ρ) :
    Injective (fun i => (e i).1.1) ∧ Injective (fun i => (e i).1.2) := by
  constructor
  · intro i j h
    exact e.injective (Subtype.ext (hρ _ (e i).2 _ (e j).2 (Or.inl h)))
  · intro i j h
    exact e.injective (Subtype.ext (hρ _ (e i).2 _ (e j).2 (Or.inr h)))

theorem exists_enum {R C : Finset α} {ρ : Finset (α × α)} (hρ : OnBoard R C ρ)
    (hc : ρ.card = Fintype.card ι) :
    ∃ u v : ι → α, (∀ i, u i ∈ R) ∧ Injective u ∧ (∀ i, v i ∈ C) ∧ Injective v ∧
      rk (tup u) (tup v) = ρ := by
  let e := enumE (ι := ι) ρ hc
  exact ⟨fun i => (e i).1.1, fun i => (e i).1.2, fun i => hρ.row_mem (e i).2,
    (enum_injective hρ.1 e).1, fun i => hρ.col_mem (e i).2, (enum_injective hρ.1 e).2,
    rk_enum ρ e⟩

theorem exists_perm_of_rk_eq {u v u' v' : ι → α} (hu' : Injective u')
    (h : rk (tup u) (tup v) = rk (tup u') (tup v')) :
    ∃ σ : Equiv.Perm ι, u' = u ∘ σ ∧ v' = v ∘ σ := by
  have hmem : ∀ i, ∃ j, u j = u' i ∧ v j = v' i := by
    intro i
    have : (u' i, v' i) ∈ rk (tup u) (tup v) := by
      rw [h]
      exact mem_rk_tup.mpr ⟨i, rfl, rfl⟩
    exact mem_rk_tup.mp this
  choose f hf1 hf2 using hmem
  have hf : Injective f := fun i j hij => hu' (by rw [← hf1 i, ← hf1 j, hij])
  have hbij : Bijective f := Finite.injective_iff_bijective.mp hf
  exact ⟨Equiv.ofBijective f hbij, funext fun i => (hf1 i).symm, funext fun i => (hf2 i).symm⟩

theorem good_comp_perm {L : Finset α} {t : ι → Option α} (σ : Equiv.Perm ι)
    (h : Good (univ : Finset ι) L t) : Good (univ : Finset ι) L (t ∘ σ) :=
  ⟨fun j => by simpa using (h.dom (σ j)), fun j y hy => h.val (σ j) y hy,
    fun j k y hj hk => σ.injective (h.inj (σ j) (σ k) y hj hk)⟩

theorem good_comp_perm_iff {L : Finset α} {t : ι → Option α} (σ : Equiv.Perm ι) :
    Good (univ : Finset ι) L (t ∘ σ) ↔ Good (univ : Finset ι) L t := by
  constructor
  · intro h
    have := good_comp_perm σ⁻¹ h
    have e : (t ∘ σ) ∘ (σ⁻¹ : Equiv.Perm ι) = t := by
      funext j
      simp
    rwa [e] at this
  · exact good_comp_perm σ

theorem rk_comp_perm (s t : ι → Option α) (σ : Equiv.Perm ι) :
    rk (s ∘ σ) t = rk s (t ∘ (σ⁻¹ : Equiv.Perm ι)) := by
  ext p
  rw [mem_rk, mem_rk]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨σ i, h1, by simpa using h2⟩
  · rintro ⟨j, h1, h2⟩
    exact ⟨σ⁻¹ j, by simpa using h1, h2⟩

end Tuples

/-! ### The column functions and the transported maps -/

section Transport

variable {α : Type} [Fintype α] [DecidableEq α] {ι : Type} [Fintype ι] [DecidableEq ι]
  {K : Type} [CommRing K]

/-- The column function of `F` at the row tuple `s`: `t ↦ F (rk s t)` on injective tuples into `C`. -/
noncomputable def gFn (C : Finset α) (F : Finset (α × α) → K) (s : ι → Option α) : Fn K ι α := by
  classical
  exact fun t => if Good (univ : Finset ι) C t then F (rk s t) else 0

theorem gFn_of_good {C : Finset α} (F : Finset (α × α) → K) (s : ι → Option α)
    {t : ι → Option α} (h : Good (univ : Finset ι) C t) : gFn C F s t = F (rk s t) := by
  unfold gFn
  exact if_pos h

theorem gFn_of_not {C : Finset α} (F : Finset (α × α) → K) (s : ι → Option α)
    {t : ι → Option α} (h : ¬ Good (univ : Finset ι) C t) : gFn C F s t = 0 := by
  unfold gFn
  exact if_neg h

theorem gFn_add (C : Finset α) (F G : Finset (α × α) → K) (s : ι → Option α) :
    gFn C (F + G) s = gFn C F s + gFn C G s := by
  funext t
  by_cases h : Good (univ : Finset ι) C t
  · simp only [Pi.add_apply, gFn_of_good _ _ h]
  · simp only [Pi.add_apply, gFn_of_not _ _ h, add_zero]

theorem gFn_smul (C : Finset α) (c : K) (F : Finset (α × α) → K) (s : ι → Option α) :
    gFn C (c • F) s = c • gFn C F s := by
  funext t
  by_cases h : Good (univ : Finset ι) C t
  · simp only [Pi.smul_apply, gFn_of_good _ _ h]
  · simp only [Pi.smul_apply, gFn_of_not _ _ h, smul_zero]

theorem gFn_comp (C : Finset α) (F : Finset (α × α) → K) (s : ι → Option α)
    (σ : Equiv.Perm ι) : gFn C F (s ∘ σ) = rowAct σ⁻¹ (gFn C F s) := by
  funext t
  rw [rowAct_apply]
  by_cases h : Good (univ : Finset ι) C t
  · rw [gFn_of_good _ _ h, gFn_of_good _ _ ((good_comp_perm_iff σ⁻¹).mpr h), rk_comp_perm]
  · rw [gFn_of_not _ _ h, gFn_of_not _ _ (fun h' => h ((good_comp_perm_iff σ⁻¹).mp h'))]

/-- The transport of `π_y` (acting on the column factor) to rook functions. -/
noncomputable def PiOf (π : α → Module.End K (Fn K ι α)) (C : Finset α) (y : α) :
    (Finset (α × α) → K) →ₗ[K] (Finset (α × α) → K) where
  toFun F ρ := if h : ρ.card = Fintype.card ι then
      π y (gFn C F (tup fun i => (enumE ρ h i).1.1)) (tup fun i => (enumE ρ h i).1.2) else 0
  map_add' F G := by
    funext ρ
    by_cases h : ρ.card = Fintype.card ι
    · simp only [dif_pos h, Pi.add_apply, gFn_add, map_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' c F := by
    funext ρ
    by_cases h : ρ.card = Fintype.card ι
    · simp only [dif_pos h, Pi.smul_apply, gFn_smul, map_smul, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero, RingHom.id_apply]

/-- Two enumerations of the same rook give the same value (uses `S_ι`-equivariance of `π`). -/
theorem pi_enum_eq (π : α → Module.End K (Fn K ι α))
    (hπ : ∀ (σ : Equiv.Perm ι) x, rowAct σ * π x = π x * rowAct σ) (C : Finset α) (y : α)
    (F : Finset (α × α) → K) (u₀ v₀ u v : ι → α) (hu : Injective u)
    (h : rk (tup u₀) (tup v₀) = rk (tup u) (tup v)) :
    π y (gFn C F (tup u₀)) (tup v₀) = π y (gFn C F (tup u)) (tup v) := by
  obtain ⟨σ, hσu, hσv⟩ := exists_perm_of_rk_eq hu h
  subst hσu hσv
  have e1 : tup (u₀ ∘ σ) = tup u₀ ∘ σ := rfl
  have e2 : tup (v₀ ∘ σ) = tup v₀ ∘ σ := rfl
  rw [e1, e2, gFn_comp]
  have hc := congrArg (fun T => T (gFn C F (tup u₀))) (hπ σ⁻¹ y)
  simp only [Module.End.mul_apply] at hc
  rw [← hc, rowAct_apply]
  have e3 : (tup v₀ ∘ σ) ∘ (σ⁻¹ : Equiv.Perm ι) = tup v₀ := by
    funext j
    simp
  rw [e3]

/-- Well-definedness: the value of `PiOf` on any enumeration. -/
theorem PiOf_rk (π : α → Module.End K (Fn K ι α))
    (hπ : ∀ (σ : Equiv.Perm ι) x, rowAct σ * π x = π x * rowAct σ) (C : Finset α) (y : α)
    (F : Finset (α × α) → K) {u v : ι → α} (hu : Injective u) :
    PiOf π C y F (rk (tup u) (tup v)) = π y (gFn C F (tup u)) (tup v) := by
  have h : (rk (tup u) (tup v)).card = Fintype.card ι := card_rk_tup hu v
  unfold PiOf
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]
  exact pi_enum_eq π hπ C y F _ _ u v hu (rk_enum _ _)

end Transport

/-! ### Lemma D in rook form -/

section Split

variable {α : Type} [Fintype α] [DecidableEq α] {K : Type} [CommRing K]

theorem gFn_mem_Soc {R C : Finset α} {k : ℕ} {F : Finset (α × α) → K} (hF : RowLines R C k F)
    {u : Fin k → α} (huR : ∀ i, u i ∈ R) (hu : Injective u) :
    gFn C F (tup u) ∈ Soc (univ : Finset (Fin k)) univ C := by
  refine ⟨fun t ht => ?_, fun i _ => ?_⟩
  · by_contra hg
    exact ht (gFn_of_not _ _ hg)
  · funext t0
    rw [del_apply]
    show ∑ x, part i x (gFn C F (tup u)) t0 = 0
    by_cases ht0 : t0 i = none
    · by_cases hex : ∃ y, Good (univ : Finset (Fin k)) C (update t0 i (some y))
      · obtain ⟨y1, hy1⟩ := hex
        obtain ⟨w, hw⟩ := exists_tup hy1
        have hwC : ∀ j, w j ∈ C := fun j => good_tup_mem (hw ▸ hy1 : Good univ C (tup w)) j
        have hwinj : Injective w := good_tup_inj (hw ▸ hy1 : Good univ C (tup w))
        have ht0' : t0 = update (tup w) i none := by
          rw [← hw, update_idem]
          funext j
          by_cases hj : j = i
          · subst hj; simp [ht0]
          · simp [update_of_ne hj]
        subst ht0'
        set ρ' := rk (tup u) (update (tup w) i none) with hρ'
        have hon : OnBoard R C ρ' := by
          rw [hρ', rk_erase_col hu]
          exact (onBoard_rk_tup huR hu hwC hwinj).erase _
        have hcard : ρ'.card + 1 = k := by
          rw [hρ', rk_erase_col hu, Finset.card_erase_add_one (mem_rk_tup.mpr ⟨i, rfl, rfl⟩),
            card_rk_tup hu, Fintype.card_fin]
        have hrow : u i ∉ rowsOf ρ' := by
          rw [hρ', rk_erase_col hu]
          exact not_mem_rowsOf_erase (onBoard_rk_tup huR hu hwC hwinj).1
            (mem_rk_tup.mpr ⟨i, rfl, rfl⟩)
        have key : ∀ y, part i y (gFn C F (tup u)) (update (tup w) i none) =
            if y ∈ C \ colsOf ρ' then F (insert (u i, y) ρ') else 0 := by
          intro y
          rw [part_apply, if_pos (by simp), update_idem]
          by_cases hy : y ∈ C \ colsOf ρ'
          · rw [if_pos hy, gFn_of_good _ _ ((good_update_iff hu hwC hwinj i y).mpr hy),
              rk_update_col]
          · rw [if_neg hy, gFn_of_not _ _ (fun h => hy ((good_update_iff hu hwC hwinj i y).mp h))]
        rw [Finset.sum_congr rfl fun y _ => key y, ← Finset.sum_filter,
          Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact hF ρ' hon hcard (u i) (huR i) hrow
      · push_neg at hex
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [part_apply, if_pos ht0, gFn_of_not _ _ (hex y)]
    · refine Finset.sum_eq_zero fun y _ => ?_
      rw [part_apply, if_neg ht0]

/-- **Lemma D in rook form** (column side), from B's `lemmaD`. -/
theorem colSplit {R C : Finset α} {k : ℕ} (hC : 2 * k + 1 ≤ C.card) : ColSplit K R C k := by
  obtain ⟨π, hπS, hπsum, hπrow⟩ :=
    lemmaD (R := K) (univ : Finset (Fin k)) C (by simpa using hC)
  have hπ : ∀ (σ : Equiv.Perm (Fin k)) x, rowAct σ * π x = π x * rowAct σ :=
    fun σ x => hπrow σ (Finset.map_univ_equiv σ) x
  have hk : Fintype.card (Fin k) = k := Fintype.card_fin k
  -- vanishing of the column functions
  have hg0 : ∀ (F : Finset (α × α) → K) (u : Fin k → α), (∀ i, u i ∈ R) → Injective u →
      (∀ w : Fin k → α, (∀ i, w i ∈ C) → Injective w → F (rk (tup u) (tup w)) = 0) →
      gFn C F (tup u) = 0 := by
    intro F u huR hu hF
    funext t
    by_cases ht : Good (univ : Finset (Fin k)) C t
    · obtain ⟨w, rfl⟩ := exists_tup ht
      rw [gFn_of_good _ _ ht]
      exact hF w (good_tup_mem ht) (good_tup_inj ht)
    · rw [gFn_of_not _ _ ht]
      rfl
  refine ⟨PiOf π C, fun F hF0 y ρ hρ hcard => ?_, fun F hF => ⟨fun ρ hρ hcard => ?_,
    fun y hy => ?_, fun y hy hcolF => ?_, fun y hy ρ hρ hcard hyρ => ?_,
    fun y hy x hFx ρ hρ hcard hxρ => ?_⟩⟩
  · -- locality
    obtain ⟨u, v, huR, hu, hvC, hv, rfl⟩ := exists_enum (ι := Fin k) hρ (by rw [hcard, hk])
    rw [PiOf_rk π hπ C y F hu, hg0 F u huR hu fun w hwC hw => hF0 _
      (onBoard_rk_tup huR hu hwC hw) (by rw [card_rk_tup hu, hk]), map_zero]
    rfl
  · -- the decomposition sums to `F`
    obtain ⟨u, v, huR, hu, hvC, hv, rfl⟩ := exists_enum (ι := Fin k) hρ (by rw [hcard, hk])
    have hs := congrFun (hπsum _ (gFn_mem_Soc hF huR hu)) (tup v)
    rw [Finset.sum_apply] at hs
    rw [Finset.sum_congr rfl fun y _ => PiOf_rk π hπ C y F hu, hs,
      gFn_of_good _ _ (good_tup hvC hv)]
  · -- row lines of the pieces
    intro ρ' hρ' hcard x hx hxr
    by_cases hne : (C \ colsOf ρ').Nonempty
    · obtain ⟨y1, hy1⟩ := hne
      obtain ⟨hy1C, hy1c⟩ := Finset.mem_sdiff.mp hy1
      have hon := hρ'.insert hx hxr hy1C hy1c
      obtain ⟨u, v, huR, hu, hvC, hv, hρeq⟩ := exists_enum (ι := Fin k) hon
        (by rw [card_insert_cell hxr, hcard, hk])
      obtain ⟨i, hui, hvi⟩ : ∃ i, u i = x ∧ v i = y1 := by
        have : (x, y1) ∈ rk (tup u) (tup v) := by rw [hρeq]; exact Finset.mem_insert_self _ _
        exact mem_rk_tup.mp this
      have hρ'eq : ρ' = rk (tup u) (update (tup v) i none) := by
        rw [rk_erase_col hu, hρeq, hui, hvi, Finset.erase_insert (fun h => hxr (rowsOf_mem h))]
      have hG := hπS _ (gFn_mem_Soc hF huR hu) y hy
      have hterm : ∀ y' ∈ C \ colsOf ρ', PiOf π C y F (insert (x, y') ρ') =
          π y (gFn C F (tup u)) (update (tup v) i (some y')) := by
        intro y' hy'
        have hy'' : ∀ j, j ≠ i → v j ≠ y' := by
          intro j hj h
          exact (Finset.mem_sdiff.mp hy').2 (by
            rw [hρ'eq, mem_colsOf_rk_erase hu]; exact ⟨j, hj, h⟩)
        rw [← tup_update, ← PiOf_rk π hπ C y F hu, tup_update,
          rk_update_col, hui, ← hρ'eq]
      rw [Finset.sum_congr rfl hterm]
      have hdel : ∑ x, part i x (π y (gFn C F (tup u))) (update (tup v) i none) = 0 := by
        have := congrFun (hG.2 i (mem_univ i)) (update (tup v) i none)
        rw [del_apply] at this
        exact this
      refine Eq.trans ?_ hdel
      rw [Finset.sum_subset (Finset.subset_univ (C \ colsOf ρ'))]
      · refine Finset.sum_congr rfl fun y' _ => ?_
        rw [part_apply, if_pos (by simp), update_idem]
      · intro y' _ hy'
        by_contra hne0
        have hgood := hG.1 _ hne0
        have hgood' : Good (univ : Finset (Fin k)) C (update (tup v) i (some y')) :=
          ⟨hgood.dom, fun j z hz => Finset.mem_of_mem_erase (hgood.val j z hz), hgood.inj⟩
        rw [good_update_iff hu hvC hv i y', ← hρ'eq] at hgood'
        exact hy' hgood'
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
  · -- column lines of the pieces
    intro ρ' hρ' hcard y' hy' hy'c
    by_cases hne : (R \ rowsOf ρ').Nonempty
    · obtain ⟨x1, hx1⟩ := hne
      obtain ⟨hx1R, hx1r⟩ := Finset.mem_sdiff.mp hx1
      have hon := hρ'.insert hx1R hx1r hy' hy'c
      obtain ⟨u, v, huR, hu, hvC, hv, hρeq⟩ := exists_enum (ι := Fin k) hon
        (by rw [card_insert_cell hx1r, hcard, hk])
      obtain ⟨i, hui, hvi⟩ : ∃ i, u i = x1 ∧ v i = y' := by
        have : (x1, y') ∈ rk (tup u) (tup v) := by rw [hρeq]; exact Finset.mem_insert_self _ _
        exact mem_rk_tup.mp this
      have hρ'eq : ρ' = rk (update (tup u) i none) (tup v) := by
        rw [rk_erase_row u hv, hρeq, hui, hvi, Finset.erase_insert (fun h => hx1r (rowsOf_mem h))]
      have hterm : ∀ x ∈ R \ rowsOf ρ', PiOf π C y F (insert (x, y') ρ') =
          π y (gFn C F (tup (update u i x))) (tup v) := by
        intro x hx
        have hx' : ∀ j, j ≠ i → u j ≠ x := by
          intro j hj h
          exact (Finset.mem_sdiff.mp hx).2 (by
            rw [hρ'eq, mem_rowsOf_rk_erase hv]; exact ⟨j, hj, h⟩)
        rw [← PiOf_rk π hπ C y F (injective_update hu hx'), tup_update, rk_update_row, hvi,
          ← hρ'eq]
      have hmap : ∑ x ∈ R \ rowsOf ρ', π y (gFn C F (tup (update u i x))) (tup v) =
          π y (∑ x ∈ R \ rowsOf ρ', gFn C F (tup (update u i x))) (tup v) := by
        rw [map_sum, Finset.sum_apply]
      rw [Finset.sum_congr rfl hterm, hmap]
      have hzero : ∑ x ∈ R \ rowsOf ρ', gFn C F (tup (update u i x)) = 0 := by
        funext t
        rw [Finset.sum_apply, Pi.zero_apply]
        by_cases ht : Good (univ : Finset (Fin k)) C t
        · obtain ⟨w, rfl⟩ := exists_tup ht
          have hwC := good_tup_mem ht
          have hw := good_tup_inj ht
          set ρ'' := rk (update (tup u) i none) (tup w) with hρ''
          have hon'' : OnBoard R C ρ'' := by
            rw [hρ'', rk_erase_row u hw]
            exact (onBoard_rk_tup huR hu hwC hw).erase _
          have hcard'' : ρ''.card + 1 = k := by
            rw [hρ'', rk_erase_row u hw, Finset.card_erase_add_one (mem_rk_tup.mpr ⟨i, rfl, rfl⟩),
              card_rk_tup hu, hk]
          have hcol'' : w i ∉ colsOf ρ'' := by
            rw [hρ'', rk_erase_row u hw]
            exact not_mem_colsOf_erase (onBoard_rk_tup huR hu hwC hw).1
              (mem_rk_tup.mpr ⟨i, rfl, rfl⟩)
          have hrows : R \ rowsOf ρ' = R \ rowsOf ρ'' := by
            ext z
            rw [Finset.mem_sdiff, Finset.mem_sdiff, hρ'eq, hρ'', mem_rowsOf_rk_erase hv,
              mem_rowsOf_rk_erase hw]
          rw [hrows, ← hcolF ρ'' hon'' hcard'' (w i) (hwC i) hcol'']
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [gFn_of_good _ _ ht, tup_update, rk_update_row]
        · exact Finset.sum_eq_zero fun x _ => gFn_of_not _ _ ht
      rw [hzero, map_zero]
      rfl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
  · -- vanishing on column `y`
    obtain ⟨u, v, huR, hu, hvC, hv, rfl⟩ := exists_enum (ι := Fin k) hρ (by rw [hcard, hk])
    rw [PiOf_rk π hπ C y F hu]
    obtain ⟨i, hi⟩ := mem_colsOf_rk_tup.mp hyρ
    by_contra hne
    have hgood := (hπS _ (gFn_mem_Soc hF huR hu) y hy).1 _ hne
    exact Finset.notMem_erase y C (hi ▸ good_tup_mem hgood i)
  · -- vanishing on a row where `F` vanishes
    obtain ⟨u, v, huR, hu, hvC, hv, rfl⟩ := exists_enum (ι := Fin k) hρ (by rw [hcard, hk])
    obtain ⟨i, hi⟩ := mem_rowsOf_rk_tup.mp hxρ
    rw [PiOf_rk π hπ C y F hu, hg0 F u huR hu fun w hwC hw => hFx _
      (onBoard_rk_tup huR hu hwC hw) (by rw [card_rk_tup hu, hk])
      (mem_rowsOf_rk_tup.mpr ⟨i, hi⟩), map_zero]
    rfl

/-- **DCP_b(N) for all `N` from HALF in the window** (all other inputs proved). -/
theorem dcpr_of_halfWindow (b : ℕ)
    (hhalf : ∀ b' N, b' ≤ b → b' + 2 ≤ N → N + 1 ≤ 2 * b' → HALF α K b' N) :
    ∀ N, DCPR α K b N :=
  dcpr_all (fun _ _ _ hC => colSplit hC) b hhalf

/-- **DCP_b(N) for `b ≤ 2` and all `N`, unconditionally.** -/
theorem dcpr_le_two_uncond {b : ℕ} (hb : b ≤ 2) : ∀ N, DCPR α K b N :=
  dcpr_le_two (fun _ _ _ hC => colSplit hC) hb

end Split

end ClaudeDCP
