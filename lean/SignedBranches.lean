import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Actual finite matching terms of the signed injection rewrite, with a supplied
chain C. This module proves both directions of relabelling/compression for the
terms. It does not yet choose the first failed prefix or prove termination,
path grouping, normalization, or a degree lower-bound endpoint.
-/

namespace SelfContainedCycle035

abbrev Edges := Finset (ℕ × ℕ)

def IsMatching (R : Edges) : Prop :=
  ∀ e ∈ R, ∀ e' ∈ R, (e.1 = e'.1 ∨ e.2 = e'.2) → e = e'

def rows (R : Edges) : Finset ℕ := R.image Prod.fst
def cols (R : Edges) : Finset ℕ := R.image Prod.snd

def edgeEmbedding (f g : ℕ ↪ ℕ) : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun e := (f e.1, g e.2)
  inj' := by
    intro a b h
    exact Prod.ext (f.injective (congrArg Prod.fst h))
      (g.injective (congrArg Prod.snd h))

def rename (f g : ℕ ↪ ℕ) (R : Edges) : Edges := R.map (edgeEmbedding f g)

@[simp] theorem rename_card (f g : ℕ ↪ ℕ) (R : Edges) :
    (rename f g R).card = R.card := Finset.card_map _

@[simp] theorem rename_union (f g : ℕ ↪ ℕ) (P M : Edges) :
    rename f g (P ∪ M) = rename f g P ∪ rename f g M := Finset.map_union _ _

theorem rename_injective (f g : ℕ ↪ ℕ) : Function.Injective (rename f g) :=
  Finset.map_injective (edgeEmbedding f g)

theorem exists_rename_of_supported (f g : ℕ ↪ ℕ) (Q : Edges)
    (hQ : ∀ e ∈ Q, e.1 ∈ Set.range f ∧ e.2 ∈ Set.range g) :
    ∃ P, rename f g P = Q := by
  classical
  refine ⟨Q.preimage (edgeEmbedding f g) (edgeEmbedding f g).injective.injOn, ?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_preimage.mp ha
  · intro he
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hQ e he
    have hmap : edgeEmbedding f g (i, j) = e := Prod.ext hi hj
    apply Finset.mem_map.mpr
    refine ⟨(i, j), ?_, hmap⟩
    apply Finset.mem_preimage.mpr
    simpa only [hmap] using he

@[simp] theorem rows_rename (f g : ℕ ↪ ℕ) (R : Edges) :
    rows (rename f g R) = (rows R).map f := by
  simp [rows, rename, Finset.map_eq_image, Finset.image_image, edgeEmbedding,
    Function.comp_def]

@[simp] theorem cols_rename (f g : ℕ ↪ ℕ) (R : Edges) :
    cols (rename f g R) = (cols R).map g := by
  simp [cols, rename, Finset.map_eq_image, Finset.image_image, edgeEmbedding,
    Function.comp_def]

@[simp] theorem matching_rename (f g : ℕ ↪ ℕ) (R : Edges) :
    IsMatching (rename f g R) ↔ IsMatching R := by
  constructor
  · intro h a ha b hb hab
    apply (edgeEmbedding f g).injective
    apply h _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩) _ (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
    rcases hab with hab | hab
    · exact Or.inl (congrArg f hab)
    · exact Or.inr (congrArg g hab)
  · intro h a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    apply congrArg (edgeEmbedding f g)
    apply h x hx y hy
    rcases hab with hab | hab
    · exact Or.inl (f.injective hab)
    · exact Or.inr (g.injective hab)

theorem rows_subset_reflect (f g : ℕ ↪ ℕ) (M : Edges) (A B : Finset ℕ)
    (h : ∀ i, f i ∈ B ↔ i ∈ A) :
    rows (rename f g M) ⊆ B ↔ rows M ⊆ A := by
  rw [rows_rename]
  constructor
  · intro hm i hi
    exact (h i).mp (hm (Finset.mem_map.mpr ⟨i, hi, rfl⟩))
  · intro hm i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact (h j).mpr (hm hj)

/-- Lower-degree terms of sum_{A subset S} (-1)^|A| b(A,B). -/
def LowerTerm (S B : Finset ℕ) (M : Edges) (z : ℤ) : Prop :=
  IsMatching M ∧ rows M ⊆ B ∧ cols M ⊆ S ∧ z = (-1 : ℤ) ^ M.card

/-- Other degree-|C| injections into T; the original term C is omitted. -/
def UpperTerm (C : Edges) (T : Finset ℕ) (M : Edges) (z : ℤ) : Prop :=
  IsMatching M ∧ rows M ⊆ T ∧ cols M = cols C ∧ M ≠ C ∧ z = -1

def Replacement (C : Edges) (B T : Finset ℕ) (M : Edges) (z : ℤ) : Prop :=
  LowerTerm (cols C) B M z ∨ UpperTerm C T M z

/-- Actual child matching obtained by adjoining a replacement to the fixed P. -/
def Branch (P C : Edges) (B T : Finset ℕ) (Q : Edges) (z : ℤ) : Prop :=
  ∃ M, Replacement C B T M z ∧ IsMatching (P ∪ M) ∧ Q = P ∪ M

theorem matching_rows_card {M : Edges} (h : IsMatching M) : (rows M).card = M.card :=
  Finset.card_image_of_injOn (fun a ha b hb hab => h a ha b hb (Or.inl hab))

theorem matching_cols_card {M : Edges} (h : IsMatching M) : (cols M).card = M.card :=
  Finset.card_image_of_injOn (fun a ha b hb hab => h a ha b hb (Or.inr hab))

theorem lowerTerm_card_lt {C M : Edges} {B : Finset ℕ} {z : ℤ}
    (h : LowerTerm (cols C) B M z) (hB : B.card < C.card) : M.card < C.card := by
  have hle := Finset.card_le_card h.2.1
  rw [matching_rows_card h.1] at hle
  omega

theorem upperTerm_card_eq {C M : Edges} {T : Finset ℕ} {z : ℤ}
    (hc : IsMatching C) (h : UpperTerm C T M z) : M.card = C.card := by
  rw [← matching_cols_card h.1, h.2.2.1, matching_cols_card hc]

theorem term_kinds_disjoint {C M : Edges} {B T : Finset ℕ} {z w : ℤ}
    (hc : IsMatching C) (hB : B.card < C.card)
    (hl : LowerTerm (cols C) B M z) : ¬ UpperTerm C T M w := by
  intro hu
  have hlt := lowerTerm_card_lt hl hB
  have heq := upperTerm_card_eq hc hu
  omega

theorem replacement_cols_subset {C M : Edges} {B T : Finset ℕ} {z : ℤ}
    (h : Replacement C B T M z) : cols M ⊆ cols C := by
  rcases h with h | h
  · exact h.2.2.1
  · rw [h.2.2.1]

/-- Every replacement belongs to an explicit finite grid, so there are finitely many. -/
theorem replacement_subset_grid {C M : Edges} {B T : Finset ℕ} {z : ℤ}
    (h : Replacement C B T M z) : M ⊆ (B ∪ T).product (cols C) := by
  intro e he
  apply Finset.mem_product.mpr
  have hrow : e.1 ∈ rows M := Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hcol : e.2 ∈ cols M := Finset.mem_image.mpr ⟨e, he, rfl⟩
  refine ⟨?_, replacement_cols_subset h hcol⟩
  rcases h with h | h
  · exact Finset.mem_union_left T (h.2.1 hrow)
  · exact Finset.mem_union_right B (h.2.1 hrow)

theorem replacement_mem_finite_family {C M : Edges} {B T : Finset ℕ} {z : ℤ}
    (h : Replacement C B T M z) : M ∈ ((B ∪ T).product (cols C)).powerset :=
  Finset.mem_powerset.mpr (replacement_subset_grid h)

theorem replacement_disjoint {P C M : Edges} {B T : Finset ℕ} {z : ℤ}
    (hPC : Disjoint (cols P) (cols C)) (h : Replacement C B T M z) :
    Disjoint P M := by
  apply Finset.disjoint_left.mpr
  intro e heP heM
  exact Finset.disjoint_left.mp hPC (Finset.mem_image.mpr ⟨e, heP, rfl⟩)
    (replacement_cols_subset h (Finset.mem_image.mpr ⟨e, heM, rfl⟩))

/-- The same child cannot hide two replacement terms when P and C have disjoint columns. -/
theorem replacement_unique {P C M N : Edges} {B T : Finset ℕ} {z w : ℤ}
    (hPC : Disjoint (cols P) (cols C))
    (hm : Replacement C B T M z) (hn : Replacement C B T N w)
    (heq : P ∪ M = P ∪ N) : M = N := by
  have hdM := replacement_disjoint hPC hm
  have hdN := replacement_disjoint hPC hn
  have heq' := congrArg (fun Q => Q \ P) heq
  simpa only [Finset.union_sdiff_cancel_left hdM, Finset.union_sdiff_cancel_left hdN] using heq'

theorem replacement_sign_unique {C M : Edges} {B T : Finset ℕ} {z w : ℤ}
    (hc : IsMatching C) (hB : B.card < C.card)
    (hz : Replacement C B T M z) (hw : Replacement C B T M w) : z = w := by
  rcases hz with hz | hz <;> rcases hw with hw | hw
  · exact hz.2.2.2.trans hw.2.2.2.symm
  · exact (term_kinds_disjoint hc hB hz hw).elim
  · exact (term_kinds_disjoint hc hB hw hz).elim
  · exact hz.2.2.2.2.trans hw.2.2.2.2.symm

theorem branch_sign_unique {P C Q : Edges} {B T : Finset ℕ} {z w : ℤ}
    (hc : IsMatching C) (hB : B.card < C.card)
    (hPC : Disjoint (cols P) (cols C))
    (hz : Branch P C B T Q z) (hw : Branch P C B T Q w) : z = w := by
  obtain ⟨M, hm, _, hM⟩ := hz
  obtain ⟨N, hn, _, hN⟩ := hw
  have heq := replacement_unique hPC hm hn (hM.symm.trans hN)
  subst N
  exact replacement_sign_unique hc hB hm hn

/-- The concrete signed branch never increases matching degree. -/
theorem branch_card_le {P C Q : Edges} {B T : Finset ℕ} {z : ℤ}
    (hc : IsMatching C) (hB : B.card < C.card)
    (hPC : Disjoint (cols P) (cols C)) (h : Branch P C B T Q z) :
    Q.card ≤ (P ∪ C).card := by
  obtain ⟨M, hm, _, rfl⟩ := h
  have hdM := replacement_disjoint hPC hm
  have hdC : Disjoint P C := by
    apply Finset.disjoint_left.mpr
    intro e heP heC
    exact Finset.disjoint_left.mp hPC (Finset.mem_image.mpr ⟨e, heP, rfl⟩)
      (Finset.mem_image.mpr ⟨e, heC, rfl⟩)
  rw [Finset.card_union_of_disjoint hdM, Finset.card_union_of_disjoint hdC]
  rcases hm with hm | hm
  · have hlt := lowerTerm_card_lt hm hB
    omega
  · rw [upperTerm_card_eq hc hm]

theorem lowerTerm_rename_iff (f g : ℕ ↪ ℕ) (C M : Edges)
    (B B' : Finset ℕ) (z : ℤ) (hB : ∀ i, f i ∈ B' ↔ i ∈ B) :
    LowerTerm (cols (rename f g C)) B' (rename f g M) z ↔
      LowerTerm (cols C) B M z := by
  simp only [LowerTerm, matching_rename, rows_subset_reflect f g M B B' hB,
    cols_rename, Finset.map_subset_map, rename_card]

theorem upperTerm_rename_iff (f g : ℕ ↪ ℕ) (C M : Edges)
    (T T' : Finset ℕ) (z : ℤ) (hT : ∀ i, f i ∈ T' ↔ i ∈ T) :
    UpperTerm (rename f g C) T' (rename f g M) z ↔ UpperTerm C T M z := by
  simp only [UpperTerm, matching_rename, rows_subset_reflect f g M T T' hT,
    cols_rename, (Finset.map_injective g).eq_iff, (rename_injective f g).ne_iff]

theorem replacement_rename_iff (f g : ℕ ↪ ℕ) (C M : Edges)
    (B T B' T' : Finset ℕ) (z : ℤ)
    (hB : ∀ i, f i ∈ B' ↔ i ∈ B) (hT : ∀ i, f i ∈ T' ↔ i ∈ T) :
    Replacement (rename f g C) B' T' (rename f g M) z ↔ Replacement C B T M z := by
  exact or_congr (lowerTerm_rename_iff f g C M B B' z hB)
    (upperTerm_rename_iff f g C M T T' z hT)

/-- Two-way correspondence: all retained large branches, not just mapped small ones. -/
theorem branch_rename_iff (f g : ℕ ↪ ℕ) (P C Q : Edges)
    (B T B' T' : Finset ℕ) (z : ℤ)
    (hB : ∀ i, f i ∈ B' ↔ i ∈ B) (hT : ∀ i, f i ∈ T' ↔ i ∈ T) :
    Branch (rename f g P) (rename f g C) B' T' (rename f g Q) z ↔
      Branch P C B T Q z := by
  constructor
  · rintro ⟨M', hm, hmatch, heq⟩
    have hsub : M' ⊆ rename f g Q := by
      rw [heq]
      exact Finset.subset_union_right
    obtain ⟨M, _, hM⟩ := Finset.subset_map_iff.mp hsub
    change M' = rename f g M at hM
    subst M'
    refine ⟨M, (replacement_rename_iff f g C M B T B' T' z hB hT).mp hm, ?_, ?_⟩
    · apply (matching_rename f g (P ∪ M)).mp
      simpa only [rename_union] using hmatch
    · apply rename_injective f g
      simpa only [rename_union] using heq
  · rintro ⟨M, hm, hmatch, rfl⟩
    refine ⟨rename f g M,
      (replacement_rename_iff f g C M B T B' T' z hB hT).mpr hm, ?_, ?_⟩
    · simpa only [rename_union] using (matching_rename f g (P ∪ M)).mpr hmatch
    · exact rename_union f g P M

/-- Surjectivity onto all supported target children, with the actual sign unchanged. -/
theorem retained_branch_has_preimage (f g : ℕ ↪ ℕ) (P C Q' : Edges)
    (B T B' T' : Finset ℕ) (z : ℤ)
    (hB : ∀ i, f i ∈ B' ↔ i ∈ B) (hT : ∀ i, f i ∈ T' ↔ i ∈ T)
    (hQ : ∀ e ∈ Q', e.1 ∈ Set.range f ∧ e.2 ∈ Set.range g)
    (h : Branch (rename f g P) (rename f g C) B' T' Q' z) :
    ∃ Q, rename f g Q = Q' ∧ Branch P C B T Q z := by
  obtain ⟨Q, hmap⟩ := exists_rename_of_supported f g Q' hQ
  refine ⟨Q, hmap, (branch_rename_iff f g P C Q B T B' T' z hB hT).mp ?_⟩
  simpa only [hmap] using h

def freeBefore (U : Finset ℕ) (R : Edges) (a : ℕ) : Finset ℕ :=
  U.filter (fun i => i ≤ a ∧ i ∉ rows R)

def targetRows (U : Finset ℕ) (R C : Edges) (a : ℕ) : Finset ℕ :=
  rows C ∪ U.filter (fun i => a < i ∧ i ∉ rows R)

theorem freeBefore_preimage (f g : ℕ ↪ ℕ) (U U' : Finset ℕ) (R : Edges) (a : ℕ)
    (hf : StrictMono f) (hU : ∀ i, f i ∈ U' ↔ i ∈ U) :
    ∀ i, f i ∈ freeBefore U' (rename f g R) (f a) ↔ i ∈ freeBefore U R a := by
  intro i
  simp only [freeBefore, Finset.mem_filter, rows_rename, Finset.mem_map', hU,
    hf.le_iff_le]

theorem targetRows_preimage (f g : ℕ ↪ ℕ) (U U' : Finset ℕ) (R C : Edges) (a : ℕ)
    (hf : StrictMono f) (hU : ∀ i, f i ∈ U' ↔ i ∈ U) :
    ∀ i, f i ∈ targetRows U' (rename f g R) (rename f g C) (f a) ↔
      i ∈ targetRows U R C a := by
  intro i
  simp only [targetRows, Finset.mem_union, Finset.mem_filter, rows_rename,
    Finset.mem_map', hU, hf.lt_iff_lt]

/-- Compression for the actual B,T formulas, with the source chain supplied. -/
theorem supplied_chain_branch_iff (f g : ℕ ↪ ℕ) (U U' : Finset ℕ)
    (R P C Q : Edges) (a : ℕ) (z : ℤ)
    (hf : StrictMono f) (hU : ∀ i, f i ∈ U' ↔ i ∈ U) :
    Branch (rename f g P) (rename f g C)
      (freeBefore U' (rename f g R) (f a))
      (targetRows U' (rename f g R) (rename f g C) (f a)) (rename f g Q) z ↔
    Branch P C (freeBefore U R a) (targetRows U R C a) Q z := by
  exact branch_rename_iff f g P C Q _ _ _ _ z
    (freeBefore_preimage f g U U' R a hf hU)
    (targetRows_preimage f g U U' R C a hf hU)

def swapEmbedding : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun := Prod.swap
  inj' := Prod.swap_injective

def transpose (R : Edges) : Edges := R.map swapEmbedding

theorem transpose_rename (f g : ℕ ↪ ℕ) (R : Edges) :
    transpose (rename f g R) = rename g f (transpose R) := by
  simp only [transpose, rename, Finset.map_map]
  rfl

def ColumnBranch (P C : Edges) (B T : Finset ℕ) (Q : Edges) (z : ℤ) : Prop :=
  Branch (transpose P) (transpose C) B T (transpose Q) z

theorem columnBranch_rename_iff (f g : ℕ ↪ ℕ) (P C Q : Edges)
    (B T B' T' : Finset ℕ) (z : ℤ)
    (hB : ∀ i, g i ∈ B' ↔ i ∈ B) (hT : ∀ i, g i ∈ T' ↔ i ∈ T) :
    ColumnBranch (rename f g P) (rename f g C) B' T' (rename f g Q) z ↔
      ColumnBranch P C B T Q z := by
  simpa only [ColumnBranch, transpose_rename] using
    branch_rename_iff g f (transpose P) (transpose C) (transpose Q) B T B' T' z hB hT

/-- Row compression in a column rewrite leaves its row-of-the-transpose target sets fixed. -/
theorem columnBranch_row_compression (f : ℕ ↪ ℕ) (P C Q : Edges)
    (B T : Finset ℕ) (z : ℤ) :
    ColumnBranch (rename f (Function.Embedding.refl ℕ) P)
      (rename f (Function.Embedding.refl ℕ) C) B T
      (rename f (Function.Embedding.refl ℕ) Q) z ↔ ColumnBranch P C B T Q z := by
  exact columnBranch_rename_iff f (Function.Embedding.refl ℕ) P C Q B T B T z
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)

/-! Non-vacuity on a true singleton-chain branch, retaining row6 and deleting rows5,7. -/

def gapRow (i : ℕ) : ℕ := if i ≤ 4 then i else 2 * i - 4

theorem gapRow_strictMono : StrictMono gapRow := by
  intro i j hij
  dsimp [gapRow]
  split_ifs <;> omega

def gapEmbedding : ℕ ↪ ℕ := ⟨gapRow, gapRow_strictMono.injective⟩

theorem gap_fixes_old : ∀ i ≤ 4, gapEmbedding i = i := by
  intro i hi
  simp [gapEmbedding, gapRow, hi]

theorem gap_universe_preimage : ∀ i, gapEmbedding i ∈ Finset.Icc 1 7 ↔
    i ∈ Finset.Icc 1 5 := by
  intro i
  simp only [Finset.mem_Icc, gapEmbedding, Function.Embedding.coeFn_mk, gapRow]
  split_ifs <;> omega

theorem singleton_lower_branch : Branch ∅ {(1, 1)} ∅ (Finset.Icc 1 5) ∅ 1 := by
  refine ⟨∅, Or.inl ?_, ?_, by simp⟩
  · simp [LowerTerm, IsMatching, rows, cols]
  · simp [IsMatching]

theorem singleton_retained_branch :
    Branch ∅ {(1, 1)} ∅ (Finset.Icc 1 5) {(5, 1)} (-1) := by
  refine ⟨{(5, 1)}, Or.inr ?_, ?_, by simp⟩
  · simp [UpperTerm, IsMatching, rows, cols]
  · simp [IsMatching]

theorem singleton_compression_iff (Q : Edges) (z : ℤ) :
    Branch ∅ {(1, 1)} ∅ (Finset.Icc 1 7)
      (rename gapEmbedding (Function.Embedding.refl ℕ) Q) z ↔
    Branch ∅ {(1, 1)} ∅ (Finset.Icc 1 5) Q z := by
  have h := branch_rename_iff gapEmbedding (Function.Embedding.refl ℕ)
    ∅ {(1, 1)} Q ∅ (Finset.Icc 1 5) ∅ (Finset.Icc 1 7) z
    (by simp) gap_universe_preimage
  simpa [rename, edgeEmbedding, gapEmbedding, gapRow] using h

theorem singleton_mapped_branch :
    Branch ∅ {(1, 1)} ∅ (Finset.Icc 1 7) {(6, 1)} (-1) := by
  have h := (singleton_compression_iff {(5, 1)} (-1)).mpr singleton_retained_branch
  simpa [rename, edgeEmbedding, gapEmbedding, gapRow] using h

theorem singleton_deleted_branch :
    Branch ∅ {(1, 1)} ∅ (Finset.Icc 1 7) {(5, 1)} (-1) := by
  refine ⟨{(5, 1)}, Or.inr ?_, ?_, by simp⟩
  · simp [UpperTerm, IsMatching, rows, cols]
  · simp [IsMatching]

theorem deleted_branch_not_in_image (Q : Edges) :
    rename gapEmbedding (Function.Embedding.refl ℕ) Q ≠ {(5, 1)} := by
  intro h
  have hm : (5, 1) ∈ rename gapEmbedding (Function.Embedding.refl ℕ) Q := by
    rw [h]
    simp
  obtain ⟨e, _, he⟩ := Finset.mem_map.mp hm
  have he' := congrArg Prod.fst he
  change gapRow e.1 = 5 at he'
  dsimp [gapRow] at he'
  split_ifs at he' <;> omega

theorem singleton_actual_context :
    freeBefore (Finset.Icc 1 5) {(1, 1)} 1 = ∅ ∧
    targetRows (Finset.Icc 1 5) {(1, 1)} {(1, 1)} 1 = Finset.Icc 1 5 := by decide

theorem singleton_large_context :
    freeBefore (Finset.Icc 1 7) {(1, 1)} 1 = ∅ ∧
    targetRows (Finset.Icc 1 7) {(1, 1)} {(1, 1)} 1 = Finset.Icc 1 7 := by decide

theorem singleton_valid_guards :
    IsMatching {(1, 1)} ∧ (∅ : Finset ℕ).card < ({(1, 1)} : Edges).card ∧
    Disjoint (cols ∅) (cols {(1, 1)}) := by
  simp [IsMatching, cols]

end SelfContainedCycle035
