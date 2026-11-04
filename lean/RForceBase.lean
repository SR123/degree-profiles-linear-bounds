/-
Agent R, round 6 (26 Sep 2026).  Foundations for Theorem A (FORCE) of
R_referee/work/HALF_PROOF.md, in the conventions of `BLemmaL`/`ForceInterface`:
a permutation `w` has cells `(w y, y)` (row = value, column = argument), increasing sets are
column sets `I` with `IncOn w I`, and sub-boards are pairs `R C : Finset α`, a bijection
`C → R` being a permutation `w` with `Fits R C w`.

Contents:
* `lisOn w S` : the length of a longest increasing subset of the column set `S`;
* `LexLt`, `lexKey` (colex on the order dual), `maxChains`, `lexFirst` (the lexicographically
  first longest increasing set) with its characterisation `lexFirst_eq`;
* `rhoOf w C` : the rook `{(w y, y) : y ∈ C \ lexFirst w C}`;
* corner lemmas (HALF_PROOF Lemma 3.1, Cor. 3.2): `corner_chain`, `corner_ext`,
  `corner_lis`, `corner_lis_not`;
* the three contractions (Lemma 3.3): `lexFirst_of_corner`, `rhoOf_of_lexFirst_eq`,
  `shift_lis`, `shift_rhoOf`;
* balanced contraction of rook functions (Lemma 3.4): `zb_contract`.
-/
import ForceInterface

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RForce

open Finset ClaudeDCP BLemmaL

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

instance incOnDec (w : Equiv.Perm α) : DecidablePred (IncOn w) := fun I => by
  unfold IncOn
  infer_instance

/-! ### Longest increasing subsets of a column set -/

/-- The length of a longest subset of `S` on which `w` is increasing. -/
def lisOn (w : Equiv.Perm α) (S : Finset α) : ℕ :=
  ((S.powerset).filter (IncOn w)).sup Finset.card

theorem le_lisOn {w : Equiv.Perm α} {S I : Finset α} (hIS : I ⊆ S) (hI : IncOn w I) :
    I.card ≤ lisOn w S :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hIS, hI⟩)

theorem lisOn_le {w : Equiv.Perm α} {S : Finset α} {n : ℕ}
    (h : ∀ I ⊆ S, IncOn w I → I.card ≤ n) : lisOn w S ≤ n :=
  Finset.sup_le fun I hI =>
    h I (Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1) (Finset.mem_filter.mp hI).2

theorem incOn_empty (w : Equiv.Perm α) : IncOn w ∅ :=
  fun y hy => absurd hy (Finset.notMem_empty y)

theorem exists_lisOn (w : Equiv.Perm α) (S : Finset α) :
    ∃ I ⊆ S, IncOn w I ∧ I.card = lisOn w S := by
  obtain ⟨I, hI, heq⟩ := Finset.exists_mem_eq_sup ((S.powerset).filter (IncOn w))
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, incOn_empty w⟩⟩ Finset.card
  exact ⟨I, Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1, (Finset.mem_filter.mp hI).2,
    heq.symm⟩

theorem lisOn_mono (w : Equiv.Perm α) {S T : Finset α} (h : S ⊆ T) : lisOn w S ≤ lisOn w T :=
  lisOn_le fun _ hI hinc => le_lisOn (hI.trans h) hinc

theorem lisOn_le_card (w : Equiv.Perm α) (S : Finset α) : lisOn w S ≤ S.card :=
  lisOn_le fun _ hI _ => Finset.card_le_card hI

theorem incOn_congr {w w' : Equiv.Perm α} {I : Finset α} (h : ∀ y ∈ I, w y = w' y) :
    IncOn w I ↔ IncOn w' I := by
  constructor
  · intro hI y hy y' hy' hlt
    rw [← h y hy, ← h y' hy']
    exact hI y hy y' hy' hlt
  · intro hI y hy y' hy' hlt
    rw [h y hy, h y' hy']
    exact hI y hy y' hy' hlt

theorem lisOn_congr {w w' : Equiv.Perm α} {S : Finset α} (h : ∀ y ∈ S, w y = w' y) :
    lisOn w S = lisOn w' S := by
  apply le_antisymm
  · exact lisOn_le fun I hI hinc => le_lisOn hI ((incOn_congr fun y hy => h y (hI hy)).mp hinc)
  · exact lisOn_le fun I hI hinc => le_lisOn hI ((incOn_congr fun y hy => h y (hI hy)).mpr hinc)

/-! ### The lexicographic order and the lexicographically first longest increasing set -/

/-- `A` precedes `B` lexicographically: the least element of `A Δ B` lies in `A`. -/
def LexLt (A B : Finset α) : Prop := ∃ a ∈ A, a ∉ B ∧ ∀ b ∈ B, b ∉ A → a < b

/-- Lexicographic key: indicator functions compared in `Lex (α → Bool)`;
`lexKey B < lexKey A ↔ LexLt A B`. -/
def lexKey (A : Finset α) : Lex (α → Bool) := toLex (fun a => decide (a ∈ A))

theorem lexLt_of_lexKey_lt {A B : Finset α} (h : lexKey B < lexKey A) : LexLt A B := by
  obtain ⟨i, hbelow, hi⟩ := h
  have hi' : decide (i ∈ B) < decide (i ∈ A) := hi
  have hf : ∀ x : Bool, ¬ x < false := by decide
  have ht : ∀ x : Bool, ¬ true < x := by decide
  have hiA : i ∈ A := by
    by_contra hA
    rw [decide_eq_false hA] at hi'
    exact hf _ hi'
  have hiB : i ∉ B := by
    intro hB
    rw [decide_eq_true hB] at hi'
    exact ht _ hi'
  refine ⟨i, hiA, hiB, fun b hb hbA => ?_⟩
  rcases lt_trichotomy b i with hlt | heq | hgt
  · have h2 : decide (b ∈ B) = decide (b ∈ A) := hbelow b hlt
    rw [decide_eq_true hb, decide_eq_false hbA] at h2
    exact absurd h2 (by decide)
  · exact absurd (heq ▸ hb) hiB
  · exact hgt

theorem lexKey_injective : Function.Injective (lexKey (α := α)) := by
  intro A B h
  have h' := congrFun (toLex.injective h)
  ext a
  have := h' a
  simp only [decide_eq_decide] at this
  exact this

theorem lexKey_lt_iff {A B : Finset α} : lexKey B < lexKey A ↔ LexLt A B := by
  refine ⟨lexLt_of_lexKey_lt, fun hAB => ?_⟩
  by_contra hn
  have hne : A ≠ B := by
    obtain ⟨a, ha, haB, -⟩ := hAB
    exact fun e => haB (e ▸ ha)
  have hlt : lexKey A < lexKey B :=
    lt_of_le_of_ne (not_lt.mp hn) fun e => hne (lexKey_injective e)
  obtain ⟨a, ha, haB, hall⟩ := hAB
  obtain ⟨b, hb, hbA, hall'⟩ := lexLt_of_lexKey_lt hlt
  exact lt_asymm (hall b hb hbA) (hall' a ha haB)

/-- The longest increasing subsets of `C`. -/
def maxChains (w : Equiv.Perm α) (C : Finset α) : Finset (Finset α) :=
  (C.powerset).filter (fun I => IncOn w I ∧ I.card = lisOn w C)

theorem mem_maxChains {w : Equiv.Perm α} {C I : Finset α} :
    I ∈ maxChains w C ↔ I ⊆ C ∧ IncOn w I ∧ I.card = lisOn w C := by
  unfold maxChains
  rw [Finset.mem_filter, Finset.mem_powerset]

theorem maxChains_nonempty (w : Equiv.Perm α) (C : Finset α) : (maxChains w C).Nonempty := by
  obtain ⟨I, hI, hinc, hc⟩ := exists_lisOn w C
  exact ⟨I, mem_maxChains.mpr ⟨hI, hinc, hc⟩⟩

/-- The lexicographically first longest increasing subset of `C`. -/
noncomputable def lexFirst (w : Equiv.Perm α) (C : Finset α) : Finset α :=
  Classical.choose (Finset.exists_max_image (maxChains w C) lexKey (maxChains_nonempty w C))

theorem lexFirst_spec (w : Equiv.Perm α) (C : Finset α) :
    lexFirst w C ∈ maxChains w C ∧ ∀ B ∈ maxChains w C, lexKey B ≤ lexKey (lexFirst w C) :=
  Classical.choose_spec (Finset.exists_max_image (maxChains w C) lexKey (maxChains_nonempty w C))

theorem lexFirst_mem (w : Equiv.Perm α) (C : Finset α) : lexFirst w C ∈ maxChains w C :=
  (lexFirst_spec w C).1

theorem lexFirst_subset (w : Equiv.Perm α) (C : Finset α) : lexFirst w C ⊆ C :=
  (mem_maxChains.mp (lexFirst_mem w C)).1

theorem lexFirst_incOn (w : Equiv.Perm α) (C : Finset α) : IncOn w (lexFirst w C) :=
  (mem_maxChains.mp (lexFirst_mem w C)).2.1

theorem lexFirst_card (w : Equiv.Perm α) (C : Finset α) : (lexFirst w C).card = lisOn w C :=
  (mem_maxChains.mp (lexFirst_mem w C)).2.2

theorem lexFirst_lt (w : Equiv.Perm α) (C : Finset α) :
    ∀ B ∈ maxChains w C, B ≠ lexFirst w C → LexLt (lexFirst w C) B := by
  intro B hB hne
  rw [← lexKey_lt_iff]
  exact lt_of_le_of_ne ((lexFirst_spec w C).2 B hB) fun h => hne (lexKey_injective h)

/-- Characterisation of `lexFirst`. -/
theorem lexFirst_eq {w : Equiv.Perm α} {C I : Finset α} (hI : I ∈ maxChains w C)
    (h : ∀ B ∈ maxChains w C, B ≠ I → LexLt I B) : lexFirst w C = I := by
  by_contra hne
  have h1 := lexKey_lt_iff.mpr (h _ (lexFirst_mem w C) hne)
  exact absurd ((lexFirst_spec w C).2 I hI) (not_le.mpr h1)

/-- `ρ_w = {(w y, y) : y ∈ C \ I_w}` for the lexicographically first longest increasing `I_w`. -/
noncomputable def rhoOf (w : Equiv.Perm α) (C : Finset α) : Finset (α × α) :=
  (C \ lexFirst w C).image (fun y => (w y, y))

/-! ### Corner cells (HALF_PROOF Lemma 3.1, Cor. 3.2) -/

section Corner

variable {w v : Equiv.Perm α} {C : Finset α} {y0 x0 : α}

/-- A chain of `w` through the corner cell `(x0, y0)`. -/
theorem corner_chain (h0 : w y0 = x0) (hag : ∀ y ∈ C, y ≠ y0 → w y = v y)
    (hlow : ∀ y ∈ C, y ≠ y0 → y < y0 → x0 < v y) {I : Finset α} (hIC : I ⊆ C)
    (hy0 : y0 ∈ I) (hinc : IncOn w I) :
    (∀ y ∈ I.erase y0, y0 < y ∧ x0 < v y) ∧ IncOn v (I.erase y0) := by
  refine ⟨fun y hy => ?_, ?_⟩
  · have hyne := Finset.ne_of_mem_erase hy
    have hyI := Finset.mem_of_mem_erase hy
    have hyC := hIC hyI
    rcases lt_or_gt_of_ne hyne with hlt | hgt
    · exfalso
      have h1 := hinc y hyI y0 hy0 hlt
      rw [h0, hag y hyC hyne] at h1
      exact lt_asymm h1 (hlow y hyC hyne hlt)
    · refine ⟨hgt, ?_⟩
      have h1 := hinc y0 hy0 y hyI hgt
      rw [h0, hag y hyC hyne] at h1
      exact h1
  · exact (incOn_congr fun y hy => hag y (hIC (Finset.mem_of_mem_erase hy))
      (Finset.ne_of_mem_erase hy)).mp (hinc.mono (Finset.erase_subset _ _))

/-- Extending a chain of `v` above-right of the corner by the corner cell. -/
theorem corner_ext (h0 : w y0 = x0) (hag : ∀ y ∈ C, y ≠ y0 → w y = v y) {J : Finset α}
    (hJC : J ⊆ C) (hP : ∀ y ∈ J, y0 < y ∧ x0 < v y) (hinc : IncOn v J) :
    IncOn w (insert y0 J) ∧ y0 ∉ J := by
  have hy0J : y0 ∉ J := fun h => lt_irrefl _ (hP y0 h).1
  refine ⟨?_, hy0J⟩
  have hne : ∀ y ∈ J, y ≠ y0 := fun y hy e => hy0J (e ▸ hy)
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with rfl | haJ <;> rcases Finset.mem_insert.mp hb with rfl | hbJ
  · exact absurd hab (lt_irrefl _)
  · rw [h0, hag b (hJC hbJ) (hne b hbJ)]
    exact (hP b hbJ).2
  · exact absurd (lt_trans hab (hP a haJ).1) (lt_irrefl _)
  · rw [hag a (hJC haJ) (hne a haJ), hag b (hJC hbJ) (hne b hbJ)]
    exact hinc a haJ b hbJ hab

theorem corner_lis (h0 : w y0 = x0) (hag : ∀ y ∈ C, y ≠ y0 → w y = v y)
    (hlow : ∀ y ∈ C, y ≠ y0 → y < y0 → x0 < v y) {S : Finset α} (hSC : S ⊆ C)
    (hy0 : y0 ∈ S) :
    lisOn w S = max (lisOn v (S.erase y0))
      (lisOn v (S.filter (fun y => y0 < y ∧ x0 < v y)) + 1) := by
  apply le_antisymm
  · refine lisOn_le fun I hIS hinc => ?_
    by_cases hyI : y0 ∈ I
    · obtain ⟨hP, hinc'⟩ := corner_chain h0 hag hlow (hIS.trans hSC) hyI hinc
      have hsub : I.erase y0 ⊆ S.filter (fun y => y0 < y ∧ x0 < v y) := fun y hy =>
        Finset.mem_filter.mpr ⟨hIS (Finset.mem_of_mem_erase hy), hP y hy⟩
      have h1 := le_lisOn hsub hinc'
      have h2 := Finset.card_erase_add_one hyI
      omega
    · have hsub : I ⊆ S.erase y0 := fun y hy =>
        Finset.mem_erase.mpr ⟨fun e => hyI (e ▸ hy), hIS hy⟩
      have hinc' : IncOn v I := (incOn_congr fun y hy =>
        hag y (hSC (hIS hy)) fun e => hyI (e ▸ hy)).mp hinc
      exact le_trans (le_lisOn hsub hinc') (le_max_left _ _)
  · refine max_le ?_ ?_
    · refine lisOn_le fun J hJ hinc => le_lisOn (hJ.trans (Finset.erase_subset _ _)) ?_
      exact (incOn_congr fun y hy => hag y (hSC (Finset.mem_of_mem_erase (hJ hy)))
        (Finset.ne_of_mem_erase (hJ hy))).mpr hinc
    · obtain ⟨J, hJ, hinc, hcard⟩ := exists_lisOn v (S.filter (fun y => y0 < y ∧ x0 < v y))
      have hJS : J ⊆ S := hJ.trans (Finset.filter_subset _ _)
      obtain ⟨hinc', hy0J⟩ := corner_ext h0 hag (hJS.trans hSC)
        (fun y hy => (Finset.mem_filter.mp (hJ hy)).2) hinc
      have h1 := le_lisOn (Finset.insert_subset hy0 hJS) hinc'
      rw [Finset.card_insert_of_notMem hy0J] at h1
      omega

theorem corner_lis_not (hag : ∀ y ∈ C, y ≠ y0 → w y = v y) {S : Finset α} (hSC : S ⊆ C)
    (hy0 : y0 ∉ S) : lisOn w S = lisOn v S :=
  lisOn_congr fun y hy => hag y (hSC hy) fun e => hy0 (e ▸ hy)

/-- If the longest increasing sets of `w` through the corner are lexicographically later than
the lexicographically first one of `v` on `C \ {y0}`, the two lexicographically first sets
agree (HALF_PROOF Lemma 3.3 (a), (b)). -/
theorem lexFirst_of_corner (hag : ∀ y ∈ C, y ≠ y0 → w y = v y)
    (hlis : lisOn w C = lisOn v (C.erase y0))
    (hBy : ∀ B ∈ maxChains w C, y0 ∈ B → LexLt (lexFirst v (C.erase y0)) B) :
    lexFirst w C = lexFirst v (C.erase y0) := by
  set I := lexFirst v (C.erase y0) with hIdef
  have hIC : I ⊆ C.erase y0 := lexFirst_subset v _
  have hagI : ∀ y ∈ I, w y = v y := fun y hy =>
    hag y (Finset.mem_of_mem_erase (hIC hy)) (Finset.ne_of_mem_erase (hIC hy))
  refine lexFirst_eq (mem_maxChains.mpr ⟨hIC.trans (Finset.erase_subset _ _),
    (incOn_congr hagI).mpr (lexFirst_incOn v _), by rw [lexFirst_card, hlis]⟩) ?_
  intro B hB hne
  by_cases hyB : y0 ∈ B
  · exact hBy B hB hyB
  · obtain ⟨hBC, hinc, hcard⟩ := mem_maxChains.mp hB
    have hBC' : B ⊆ C.erase y0 := fun y hy =>
      Finset.mem_erase.mpr ⟨fun e => hyB (e ▸ hy), hBC hy⟩
    have hB' : B ∈ maxChains v (C.erase y0) := mem_maxChains.mpr ⟨hBC',
      (incOn_congr fun y hy => hag y (hBC hy) fun e => hyB (e ▸ hy)).mp hinc,
      by rw [hcard, hlis]⟩
    exact lexFirst_lt v _ B hB' hne

theorem rhoOf_of_lexFirst_eq (h0 : w y0 = x0) (hag : ∀ y ∈ C, y ≠ y0 → w y = v y)
    (hy0 : y0 ∈ C) (h : lexFirst w C = lexFirst v (C.erase y0)) :
    rhoOf w C = insert (x0, y0) (rhoOf v (C.erase y0)) := by
  unfold rhoOf
  rw [h]
  have hIC : lexFirst v (C.erase y0) ⊆ C.erase y0 := lexFirst_subset v _
  have hy0I : y0 ∉ lexFirst v (C.erase y0) := fun hh => Finset.notMem_erase y0 C (hIC hh)
  have hset : C \ lexFirst v (C.erase y0) = insert y0 (C.erase y0 \ lexFirst v (C.erase y0)) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hz, hzI⟩
      by_cases hzy : z = y0
      · exact Or.inl hzy
      · exact Or.inr ⟨⟨hzy, hz⟩, hzI⟩
    · rintro (rfl | ⟨⟨_, hz⟩, hzI⟩)
      · exact ⟨hy0, hy0I⟩
      · exact ⟨hz, hzI⟩
  rw [hset, Finset.image_insert, h0]
  congr 1
  refine Finset.image_congr fun z hz => ?_
  have hz' := Finset.mem_sdiff.mp hz
  rw [hag z (Finset.mem_of_mem_erase hz'.1) (Finset.ne_of_mem_erase hz'.1)]

/-- The shift (HALF_PROOF Lemma 3.3 (c)): the corner cell is comparable with every other cell. -/
theorem shift_lis (h0 : w y0 = x0) (hag : ∀ y ∈ C, y ≠ y0 → w y = v y)
    (hall : ∀ y ∈ C, y ≠ y0 → y0 < y ∧ x0 < v y) (hy0 : y0 ∈ C) :
    lisOn w C = lisOn v (C.erase y0) + 1 := by
  have hlow : ∀ y ∈ C, y ≠ y0 → y < y0 → x0 < v y := fun y hy hne _ => (hall y hy hne).2
  rw [corner_lis h0 hag hlow (Finset.Subset.refl C) hy0]
  have heq : C.filter (fun y => y0 < y ∧ x0 < v y) = C.erase y0 := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hz, hlt, -⟩
      exact ⟨ne_of_gt hlt, hz⟩
    · rintro ⟨hne, hz⟩
      exact ⟨hz, hall z hz hne⟩
  rw [heq]
  omega

theorem shift_lexFirst (h0 : w y0 = x0) (hag : ∀ y ∈ C, y ≠ y0 → w y = v y)
    (hall : ∀ y ∈ C, y ≠ y0 → y0 < y ∧ x0 < v y) (hy0 : y0 ∈ C) :
    lexFirst w C = insert y0 (lexFirst v (C.erase y0)) := by
  have hlow : ∀ y ∈ C, y ≠ y0 → y < y0 → x0 < v y := fun y hy hne _ => (hall y hy hne).2
  have hlis := shift_lis h0 hag hall hy0
  set I := lexFirst v (C.erase y0) with hIdef
  have hIC : I ⊆ C.erase y0 := lexFirst_subset v _
  have hIC' : I ⊆ C := hIC.trans (Finset.erase_subset _ _)
  obtain ⟨hinc, hy0I⟩ := corner_ext h0 hag hIC' (fun y hy =>
    hall y (hIC' hy) (Finset.ne_of_mem_erase (hIC hy))) (lexFirst_incOn v _)
  refine lexFirst_eq (mem_maxChains.mpr ⟨Finset.insert_subset hy0 hIC', hinc,
    by rw [Finset.card_insert_of_notMem hy0I, lexFirst_card, hlis]⟩) ?_
  intro B hB hne
  obtain ⟨hBC, hBinc, hBcard⟩ := mem_maxChains.mp hB
  have hyB : y0 ∈ B := by
    by_contra hyB
    have hBC' : B ⊆ C.erase y0 := fun y hy =>
      Finset.mem_erase.mpr ⟨fun e => hyB (e ▸ hy), hBC hy⟩
    have h1 := le_lisOn hBC' ((incOn_congr fun y hy => hag y (hBC hy)
      fun e => hyB (e ▸ hy)).mp hBinc)
    omega
  obtain ⟨-, hinc'⟩ := corner_chain h0 hag hlow hBC hyB hBinc
  have hB' : B.erase y0 ∈ maxChains v (C.erase y0) := by
    refine mem_maxChains.mpr ⟨Finset.erase_subset_erase y0 hBC, hinc', ?_⟩
    have := Finset.card_erase_add_one hyB
    omega
  have hne' : B.erase y0 ≠ I := by
    intro e
    apply hne
    rw [← e, Finset.insert_erase hyB]
  obtain ⟨a, haI, haB, hall'⟩ := lexFirst_lt v _ _ hB' hne'
  have hay : a ≠ y0 := Finset.ne_of_mem_erase (hIC haI)
  refine ⟨a, Finset.mem_insert_of_mem haI, fun h => haB (Finset.mem_erase.mpr ⟨hay, h⟩),
    fun b hb hbI => ?_⟩
  have hby : b ≠ y0 := fun e => hbI (e ▸ Finset.mem_insert_self _ _)
  exact hall' b (Finset.mem_erase.mpr ⟨hby, hb⟩) fun h => hbI (Finset.mem_insert_of_mem h)

theorem shift_rhoOf (h0 : w y0 = x0) (hag : ∀ y ∈ C, y ≠ y0 → w y = v y)
    (hall : ∀ y ∈ C, y ≠ y0 → y0 < y ∧ x0 < v y) (hy0 : y0 ∈ C) :
    rhoOf w C = rhoOf v (C.erase y0) := by
  unfold rhoOf
  rw [shift_lexFirst h0 hag hall hy0]
  have hset : C \ insert y0 (lexFirst v (C.erase y0)) = C.erase y0 \ lexFirst v (C.erase y0) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
    constructor
    · rintro ⟨hz, hzy, hzI⟩
      exact ⟨⟨hzy, hz⟩, hzI⟩
    · rintro ⟨⟨hzy, hz⟩, hzI⟩
      exact ⟨hz, hzy, hzI⟩
  rw [hset]
  refine Finset.image_congr fun z hz => ?_
  have hz' := Finset.mem_sdiff.mp hz
  rw [hag z (Finset.mem_of_mem_erase hz'.1) (Finset.ne_of_mem_erase hz'.1)]

end Corner

/-! ### Extensions by a cell and balanced contraction -/

theorem extP_agree {R C : Finset α} {v : Equiv.Perm α} {x0 y0 : α}
    (hv : Fits (R.erase x0) (C.erase y0) v) :
    ∀ y ∈ C, y ≠ y0 → extP x0 y0 v y = v y ∧ v y ∈ R ∧ v y ≠ x0 := by
  intro y hy hne
  have h1 : v y ∈ R.erase x0 := (hv y).mpr (Finset.mem_erase.mpr ⟨hne, hy⟩)
  have hvx : v y ≠ x0 := Finset.ne_of_mem_erase h1
  exact ⟨extP_apply_of hne hvx, Finset.mem_of_mem_erase h1, hvx⟩

theorem fits_extP' {R C : Finset α} {v : Equiv.Perm α} {x0 y0 : α}
    (hv : Fits (R.erase x0) (C.erase y0) v) (hx : x0 ∈ R) (hy : y0 ∈ C) :
    Fits R C (extP x0 y0 v) := by
  have := fits_extP hv (Finset.notMem_erase x0 R) (Finset.notMem_erase y0 C)
  rwa [Finset.insert_erase hx, Finset.insert_erase hy] at this

variable {K : Type*} [CommRing K]

/-- HALF_PROOF Lemma 3.4 (a), (b): contracting a function in `Z_{k+1}` at a cell gives an
element of `Z_k` of the smaller board. -/
theorem zb_contract {R C : Finset α} {k : ℕ} {F : Finset (α × α) → K} (hF : ZB R C (k + 1) F)
    {x0 y0 : α} (hx0 : x0 ∈ R) (hy0 : y0 ∈ C) :
    ZB (R.erase x0) (C.erase y0) k (fun σ => F (insert (x0, y0) σ)) := by
  have prep : ∀ σ, OnBoard (R.erase x0) (C.erase y0) σ → σ.card + 1 = k →
      OnBoard R C (insert (x0, y0) σ) ∧ (insert (x0, y0) σ).card + 1 = k + 1 ∧
      x0 ∉ rowsOf σ ∧ y0 ∉ colsOf σ := by
    intro σ hσ hcard
    have hxr : x0 ∉ rowsOf σ := fun h => Finset.notMem_erase x0 R (rowsOf_subset hσ h)
    have hyc : y0 ∉ colsOf σ := fun h => Finset.notMem_erase y0 C (colsOf_subset hσ h)
    refine ⟨(hσ.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)).insert hx0 hxr hy0 hyc,
      by rw [card_insert_cell hxr, ← hcard], hxr, hyc⟩
  refine ⟨fun σ hσ hcard x hx hxr => ?_, fun σ hσ hcard y hy hyc => ?_⟩
  · obtain ⟨hπ, hπc, hx0r, hy0c⟩ := prep σ hσ hcard
    have hxR := Finset.mem_of_mem_erase hx
    have hxne := Finset.ne_of_mem_erase hx
    have hxπ : x ∉ rowsOf (insert (x0, y0) σ) := by
      rw [rowsOf_insert, Finset.mem_insert, not_or]
      exact ⟨hxne, hxr⟩
    have h := hF.1 _ hπ hπc x hxR hxπ
    have hset : C \ colsOf (insert (x0, y0) σ) = C.erase y0 \ colsOf σ := by
      rw [colsOf_insert]
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
      tauto
    rw [hset] at h
    rw [← h]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.insert_comm]
  · obtain ⟨hπ, hπc, hx0r, hy0c⟩ := prep σ hσ hcard
    have hyC := Finset.mem_of_mem_erase hy
    have hyne := Finset.ne_of_mem_erase hy
    have hyπ : y ∉ colsOf (insert (x0, y0) σ) := by
      rw [colsOf_insert, Finset.mem_insert, not_or]
      exact ⟨hyne, hyc⟩
    have h := hF.2 _ hπ hπc y hyC hyπ
    have hset : R \ rowsOf (insert (x0, y0) σ) = R.erase x0 \ rowsOf σ := by
      rw [rowsOf_insert]
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
      tauto
    rw [hset] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.insert_comm]

/-- A rook through a cell `(x0, y0)` is that cell added to a rook of the smaller board. -/
theorem rook_decomp {R C : Finset α} {ρ : Finset (α × α)} (hρ : OnBoard R C ρ) {x0 y0 : α}
    (hp : (x0, y0) ∈ ρ) :
    OnBoard (R.erase x0) (C.erase y0) (ρ.erase (x0, y0)) ∧
      insert (x0, y0) (ρ.erase (x0, y0)) = ρ ∧ (ρ.erase (x0, y0)).card + 1 = ρ.card := by
  refine ⟨((hρ.erase _).erase_row (not_mem_rowsOf_erase hρ.1 hp)).erase_col
    (not_mem_colsOf_erase hρ.1 hp), Finset.insert_erase hp, Finset.card_erase_add_one hp⟩

end RForce
