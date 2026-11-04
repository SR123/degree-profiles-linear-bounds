import TerminalReduction

namespace SelfContainedCycle047
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle045 SelfContainedCycle046

/-- The actual southwest order ideal of an edge within the matching. -/
def edgeDownset (R : Edges) (e : ℕ × ℕ) : Edges :=
  R.filter (fun f => f.1 ≤ e.1 ∧ f.2 ≤ e.2)

def edgeHeight (R : Edges) (e : ℕ × ℕ) : ℕ := chainHeight (edgeDownset R e)

def heightLevel (R : Edges) (t : ℕ) : Edges := R.filter (fun e => edgeHeight R e = t)

theorem chainHeight_mono {A B : Edges} (h : A ⊆ B) : chainHeight A ≤ chainHeight B := by
  apply Finset.sup_le
  intro C hC
  obtain ⟨hCA,hc⟩ := (mem_chains C A).mp hC
  exact chain_card_le_height hc (hCA.trans h)

theorem chain_insert_upper {C : Edges} {e : ℕ × ℕ} (hc : IsChain C)
    (hu : ∀ f ∈ C, f.1 < e.1 ∧ f.2 < e.2) : IsChain (insert e C) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with rfl | hCa
  · rcases Finset.mem_insert.mp hb with rfl | hCb
    · exact (hab rfl).elim
    · exact Or.inr (hu b hCb)
  · rcases Finset.mem_insert.mp hb with rfl | hCb
    · exact Or.inl (hu a hCa)
    · exact hc hCa hCb hab

theorem edgeHeight_pos {R : Edges} {e : ℕ × ℕ} (he : e ∈ R) : 0 < edgeHeight R e := by
  have hc : IsChain {e} := by simp [SelfContainedCycle036.IsChain]
  have hs : ({e} : Edges) ⊆ edgeDownset R e := by simp [edgeDownset,he]
  have h := chain_card_le_height hc hs
  simpa [edgeHeight] using h

theorem edgeHeight_le_height (R : Edges) (e : ℕ × ℕ) : edgeHeight R e ≤ chainHeight R :=
  chainHeight_mono (Finset.filter_subset _ _)

/-- A maximum downset chain actually ends at the specified matching edge. -/
theorem exists_chain_ending {R : Edges} {e : ℕ × ℕ} (hm : IsMatching R) (he : e ∈ R) :
    ∃ C, C ⊆ edgeDownset R e ∧ IsChain C ∧ e ∈ C ∧ C.card = edgeHeight R e := by
  obtain ⟨C,hC⟩ := longestChains_nonempty (edgeDownset R e)
  obtain ⟨hmem,hcard⟩ := Finset.mem_filter.mp hC
  obtain ⟨hsub,hchain⟩ := (mem_chains _ _).mp hmem
  refine ⟨C,hsub,hchain,?_,hcard⟩
  by_contra hnot
  have hu : ∀ f ∈ C, f.1 < e.1 ∧ f.2 < e.2 := by
    intro f hf
    obtain ⟨hfR,hfle⟩ := Finset.mem_filter.mp (hsub hf)
    have hne : f ≠ e := fun h => hnot (h ▸ hf)
    have hr : f.1 ≠ e.1 := fun h => hne (hm f hfR e he (Or.inl h))
    have hc : f.2 ≠ e.2 := fun h => hne (hm f hfR e he (Or.inr h))
    exact ⟨lt_of_le_of_ne hfle.1 hr,lt_of_le_of_ne hfle.2 hc⟩
  have hbound := chain_card_le_height (chain_insert_upper hchain hu)
    (Finset.insert_subset (by simp [edgeDownset,he]) hsub)
  rw [Finset.card_insert_of_notMem hnot,hcard] at hbound
  omega

/-- Increasing pairs strictly raise the actual ending-chain height. -/
theorem edgeHeight_strict {R : Edges} {e f : ℕ × ℕ} (hf : f ∈ R)
    (hr : e.1 < f.1) (hc : e.2 < f.2) : edgeHeight R e < edgeHeight R f := by
  obtain ⟨C,hC⟩ := longestChains_nonempty (edgeDownset R e)
  obtain ⟨hmem,hcard⟩ := Finset.mem_filter.mp hC
  obtain ⟨hsub,hchain⟩ := (mem_chains _ _).mp hmem
  have hu : ∀ g ∈ C, g.1 < f.1 ∧ g.2 < f.2 := by
    intro g hg
    have h := (Finset.mem_filter.mp (hsub hg)).2
    exact ⟨h.1.trans_lt hr,h.2.trans_lt hc⟩
  have hnot : f ∉ C := by intro h; have h' := (hu f h).1; omega
  have hCf : C ⊆ edgeDownset R f := by
    intro g hg
    have h := Finset.mem_filter.mp (hsub hg)
    exact Finset.mem_filter.mpr ⟨h.1,(hu g hg).1.le,(hu g hg).2.le⟩
  have hbound := chain_card_le_height (chain_insert_upper hchain hu)
    (Finset.insert_subset (by simp [edgeDownset,hf]) hCf)
  rw [Finset.card_insert_of_notMem hnot,hcard] at hbound
  exact hbound

/-- Each equal-height level is decreasing in column order as its rows increase. -/
theorem level_decreasing {R : Edges} {t : ℕ} {e f : ℕ × ℕ} (hm : IsMatching R)
    (he : e ∈ heightLevel R t) (hf : f ∈ heightLevel R t) (hr : e.1 < f.1) : f.2 < e.2 := by
  obtain ⟨heR,het⟩ := Finset.mem_filter.mp he
  obtain ⟨hfR,hft⟩ := Finset.mem_filter.mp hf
  have hne : e.2 ≠ f.2 := by
    intro h
    have heq := hm e heR f hfR (Or.inr h)
    rw [heq] at hr
    exact (lt_irrefl _ hr)
  by_contra hn
  have hc : e.2 < f.2 := lt_of_le_of_ne (by omega) hne
  have hh := edgeHeight_strict hfR hr hc
  omega

theorem height_le_unused {R : Edges} {N : ℕ} (hm : IsMatching R)
    (hR : R ⊆ grid N N) (ht : chosenRewrite R = .terminal) : chainHeight R ≤ N-R.card := by
  have hp : rowPrefix R N = R := Finset.filter_eq_self.mpr (by
    intro e he
    exact (Finset.mem_Icc.mp (Finset.mem_product.mp (hR he)).1).2)
  have h := ((terminal_iff_prefix_bounds R).mp ht).1 N
  rw [hp,matching_rows_card hm] at h
  exact h

/-- The k-th enumerated label precedes a whenever more than k labels precede a. -/
theorem enum_lt_of_card (S : Finset ℕ) (k : Fin S.card) (a : ℕ)
    (hk : k.val < (S.filter (fun x => x < a)).card) : S.orderEmbOfFin rfl k < a := by
  by_contra hn
  have ha : a ≤ S.orderEmbOfFin rfl k := by omega
  have hsub : S.filter (fun x => x < a) ⊆
      (Finset.Iio k).image (S.orderEmbOfFin rfl) := by
    intro x hx
    obtain ⟨hxS,hxa⟩ := Finset.mem_filter.mp hx
    have hr : x ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    obtain ⟨j,rfl⟩ := hr
    refine Finset.mem_image.mpr ⟨j,Finset.mem_Iio.mpr ?_,rfl⟩
    exact (S.orderEmbOfFin rfl).lt_iff_lt.mp (hxa.trans_le ha)
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Fin.card_Iio] at hcard
  omega

def unusedRows (N : ℕ) (R : Edges) : Finset ℕ := Finset.Icc 1 N \ rows R
def unusedCols (N : ℕ) (R : Edges) : Finset ℕ := Finset.Icc 1 N \ cols R

theorem rows_subset_interval {N K : ℕ} {R : Edges} (hR : R ⊆ grid N K) :
    rows R ⊆ Finset.Icc 1 N := by
  intro i hi
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
  exact (Finset.mem_product.mp (hR he)).1

theorem cols_subset_interval {N K : ℕ} {R : Edges} (hR : R ⊆ grid N K) :
    cols R ⊆ Finset.Icc 1 K := by
  intro j hj
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
  exact (Finset.mem_product.mp (hR he)).2

theorem unusedRows_card {N K : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N K) :
    (unusedRows N R).card = N-R.card := by
  rw [unusedRows,Finset.card_sdiff_of_subset (rows_subset_interval hR),matching_rows_card hm]
  simp

theorem unusedCols_card {N K : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N K) :
    (unusedCols K R).card = K-R.card := by
  rw [unusedCols,Finset.card_sdiff_of_subset (cols_subset_interval hR),matching_cols_card hm]
  simp

theorem height_le_free_rows {N : ℕ} {R : Edges} (hm : IsMatching R)
    (hR : R ⊆ grid N N) (ht : chosenRewrite R = .terminal) :
    chainHeight R ≤ (unusedRows N R).card := by
  rw [unusedRows_card hm hR]; exact height_le_unused hm hR ht

theorem height_le_free_cols {N : ℕ} {R : Edges} (hm : IsMatching R)
    (hR : R ⊆ grid N N) (ht : chosenRewrite R = .terminal) :
    chainHeight R ≤ (unusedCols N R).card := by
  rw [unusedCols_card hm hR]; exact height_le_unused hm hR ht

/-- Actual first-h unused labels, with zero-based indices corresponding to height t+1. -/
def rowAnchor {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) : Fin (chainHeight R) ↪o ℕ :=
  (unusedRows N R).orderEmbOfCardLe (height_le_free_rows hm hR ht)

def colAnchor {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) : Fin (chainHeight R) ↪o ℕ :=
  (unusedCols N R).orderEmbOfCardLe (height_le_free_cols hm hR ht)

theorem rowAnchor_mem {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) :
    rowAnchor hm hR ht t ∈ unusedRows N R := Finset.orderEmbOfCardLe_mem _ _ _

theorem colAnchor_mem {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) :
    colAnchor hm hR ht t ∈ unusedCols N R := Finset.orderEmbOfCardLe_mem _ _ _

/-- Count unused rows strictly before an occupied row, using the actual prefix. -/
theorem unusedRows_before {N K : ℕ} {R : Edges} {e : ℕ × ℕ}
    (hR : R ⊆ grid N K) (he : e ∈ R) :
    ((unusedRows N R).filter (fun i => i < e.1)).card =
      e.1 - (rows (rowPrefix R e.1)).card := by
  have hused : e.1 ∈ rows R := Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hset : (unusedRows N R).filter (fun i => i < e.1) =
      freeBefore (Finset.Icc 1 N) R e.1 := by
    ext i
    simp only [unusedRows,freeBefore,Finset.mem_filter,Finset.mem_sdiff]
    constructor
    · intro h; exact ⟨h.1.1,h.2.le,h.1.2⟩
    · intro h
      have hne : i ≠ e.1 := fun heq => h.2.2 (heq ▸ hused)
      exact ⟨⟨h.1,h.2.2⟩,lt_of_le_of_ne h.2.1 hne⟩
  rw [hset,freeBefore_card R e.1 N]
  · exact (Finset.mem_Icc.mp (Finset.mem_product.mp (hR he)).1).2
  · intro f hf
    exact (Finset.mem_Icc.mp (Finset.mem_product.mp (hR hf)).1).1

/-- Column version derived by transposing the concrete prefix, not the normalizer. -/
theorem unusedCols_before {N K : ℕ} {R : Edges} {e : ℕ × ℕ}
    (hR : R ⊆ grid N K) (he : e ∈ R) :
    ((unusedCols K R).filter (fun j => j < e.2)).card =
      e.2 - (cols (columnPrefix R e.2)).card := by
  have he' : swapEmbedding e ∈ transpose R := Finset.mem_map.mpr ⟨e,he,rfl⟩
  have h := unusedRows_before (transpose_subset_grid hR) he'
  simpa only [unusedRows,unusedCols,rows_transpose,rowPrefix_transpose,swapEmbedding,
    Function.Embedding.coeFn_mk] using h

/-- The anchor for a level strictly precedes every row in that level. -/
theorem rowAnchor_lt {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) {e : ℕ × ℕ}
    (he : e ∈ heightLevel R (t.val+1)) : rowAnchor hm hR ht t < e.1 := by
  obtain ⟨heR,het⟩ := Finset.mem_filter.mp he
  have hh : edgeHeight R e ≤ chainHeight (rowPrefix R e.1) :=
    chainHeight_mono (by
      intro f hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1,(Finset.mem_filter.mp hf).2.1⟩)
  have hb := ((terminal_iff_prefix_bounds R).mp ht).1 e.1
  apply enum_lt_of_card (unusedRows N R) ⟨t.val,lt_of_lt_of_le t.isLt (height_le_free_rows hm hR ht)⟩ e.1
  rw [unusedRows_before hR heR]
  change t.val < e.1 - (rows (rowPrefix R e.1)).card
  omega

theorem colAnchor_lt {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) {e : ℕ × ℕ}
    (he : e ∈ heightLevel R (t.val+1)) : colAnchor hm hR ht t < e.2 := by
  obtain ⟨heR,het⟩ := Finset.mem_filter.mp he
  have hh : edgeHeight R e ≤ chainHeight (columnPrefix R e.2) :=
    chainHeight_mono (by
      intro f hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1,(Finset.mem_filter.mp hf).2.2⟩)
  have hb := ((terminal_iff_prefix_bounds R).mp ht).2 e.2
  apply enum_lt_of_card (unusedCols N R) ⟨t.val,lt_of_lt_of_le t.isLt (height_le_free_cols hm hR ht)⟩ e.2
  rw [unusedCols_before hR heR]
  change t.val < e.2 - (cols (columnPrefix R e.2)).card
  omega

theorem level_matching {R : Edges} (hm : IsMatching R) (t : ℕ) : IsMatching (heightLevel R t) :=
  matching_subset hm (Finset.filter_subset _ _)

theorem levels_disjoint (R : Edges) {s t : ℕ} (hst : s ≠ t) :
    Disjoint (heightLevel R s) (heightLevel R t) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact hst ((Finset.mem_filter.mp he).2.symm.trans (Finset.mem_filter.mp hf).2)

/-- Actual height levels partition all matching edges; there is no assumed decomposition. -/
theorem levels_cover (R : Edges) :
    Finset.univ.biUnion (fun t : Fin (chainHeight R) => heightLevel R (t.val+1)) = R := by
  ext e
  constructor
  · intro he
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp ht).1
  · intro he
    have hp := edgeHeight_pos he
    have hb := edgeHeight_le_height R e
    refine Finset.mem_biUnion.mpr ⟨⟨edgeHeight R e-1,by omega⟩,Finset.mem_univ _,?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨he,by dsimp; omega⟩

theorem levels_total_card (R : Edges) :
    (∑ t : Fin (chainHeight R), (heightLevel R (t.val+1)).card) = R.card := by
  rw [← Finset.card_biUnion,levels_cover]
  intro s _ t _ hst
  apply levels_disjoint R
  intro h
  apply hst
  apply Fin.ext
  omega

theorem level_rows_disjoint {R : Edges} (hm : IsMatching R) {s t : ℕ} (hst : s ≠ t) :
    Disjoint (rows (heightLevel R s)) (rows (heightLevel R t)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hi
  obtain ⟨f,hf,hfi⟩ := Finset.mem_image.mp hj
  have heq := hm e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
    (Or.inl (hei.trans hfi.symm))
  exact Finset.disjoint_left.mp (levels_disjoint R hst) he (heq ▸ hf)

theorem level_cols_disjoint {R : Edges} (hm : IsMatching R) {s t : ℕ} (hst : s ≠ t) :
    Disjoint (cols (heightLevel R s)) (cols (heightLevel R t)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hi
  obtain ⟨f,hf,hfi⟩ := Finset.mem_image.mp hj
  have heq := hm e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
    (Or.inr (hei.trans hfi.symm))
  exact Finset.disjoint_left.mp (levels_disjoint R hst) he (heq ▸ hf)

def rowBlock {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) : Finset ℕ :=
  insert (rowAnchor hm hR ht t) (rows (heightLevel R (t.val+1)))

def colBlock {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) : Finset ℕ :=
  insert (colAnchor hm hR ht t) (cols (heightLevel R (t.val+1)))

theorem rowAnchor_not_level {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) (u : ℕ) :
    rowAnchor hm hR ht t ∉ rows (heightLevel R u) := by
  intro h
  have hnot := (Finset.mem_sdiff.mp (rowAnchor_mem hm hR ht t)).2
  exact hnot (Finset.image_subset_image (Finset.filter_subset _ _) h)

theorem colAnchor_not_level {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) (u : ℕ) :
    colAnchor hm hR ht t ∉ cols (heightLevel R u) := by
  intro h
  have hnot := (Finset.mem_sdiff.mp (colAnchor_mem hm hR ht t)).2
  exact hnot (Finset.image_subset_image (Finset.filter_subset _ _) h)

theorem rowBlock_card {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) :
    (rowBlock hm hR ht t).card = (heightLevel R (t.val+1)).card+1 := by
  rw [rowBlock,Finset.card_insert_of_notMem (rowAnchor_not_level hm hR ht t _),
    matching_rows_card (level_matching hm _)]

theorem colBlock_card {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) :
    (colBlock hm hR ht t).card = (heightLevel R (t.val+1)).card+1 := by
  rw [colBlock,Finset.card_insert_of_notMem (colAnchor_not_level hm hR ht t _),
    matching_cols_card (level_matching hm _)]

theorem paired_blocks_card {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) :
    (rowBlock hm hR ht t).card = (colBlock hm hR ht t).card := by
  rw [rowBlock_card,colBlock_card]

theorem rowBlocks_disjoint {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) {s t : Fin (chainHeight R)} (hst : s ≠ t) :
    Disjoint (rowBlock hm hR ht s) (rowBlock hm hR ht t) := by
  rw [rowBlock,rowBlock,Finset.disjoint_insert_left,Finset.disjoint_insert_right]
  refine ⟨?_,rowAnchor_not_level hm hR ht t _,level_rows_disjoint hm ?_⟩
  · simp only [Finset.mem_insert,not_or]
    exact ⟨fun h => hst ((rowAnchor hm hR ht).injective h),rowAnchor_not_level hm hR ht s _⟩
  · intro h; apply hst; apply Fin.ext; omega

theorem colBlocks_disjoint {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) {s t : Fin (chainHeight R)} (hst : s ≠ t) :
    Disjoint (colBlock hm hR ht s) (colBlock hm hR ht t) := by
  rw [colBlock,colBlock,Finset.disjoint_insert_left,Finset.disjoint_insert_right]
  refine ⟨?_,colAnchor_not_level hm hR ht t _,level_cols_disjoint hm ?_⟩
  · simp only [Finset.mem_insert,not_or]
    exact ⟨fun h => hst ((colAnchor hm hR ht).injective h),colAnchor_not_level hm hR ht s _⟩
  · intro h; apply hst; apply Fin.ext; omega

theorem rowBlock_subset {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) :
    rowBlock hm hR ht t ⊆ Finset.Icc 1 N := by
  apply Finset.insert_subset
  · exact (Finset.mem_sdiff.mp (rowAnchor_mem hm hR ht t)).1
  · exact rows_subset_interval ((Finset.filter_subset _ _).trans hR)

theorem colBlock_subset {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) :
    colBlock hm hR ht t ⊆ Finset.Icc 1 N := by
  apply Finset.insert_subset
  · exact (Finset.mem_sdiff.mp (colAnchor_mem hm hR ht t)).1
  · exact cols_subset_interval ((Finset.filter_subset _ _).trans hR)

theorem rowAnchor_is_min {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) {i : ℕ}
    (hi : i ∈ rowBlock hm hR ht t) : rowAnchor hm hR ht t ≤ i := by
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact le_rfl
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact (rowAnchor_lt hm hR ht t he).le

theorem colAnchor_is_min {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) (t : Fin (chainHeight R)) {j : ℕ}
    (hj : j ∈ colBlock hm hR ht t) : colAnchor hm hR ht t ≤ j := by
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact le_rfl
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact (colAnchor_lt hm hR ht t he).le

theorem rowBlocks_total_card {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) :
    (Finset.univ.biUnion (rowBlock hm hR ht)).card = R.card + chainHeight R := by
  rw [Finset.card_biUnion (fun s _ t _ hst => rowBlocks_disjoint hm hR ht hst)]
  simp_rw [rowBlock_card]
  rw [Finset.sum_add_distrib,levels_total_card]
  simp

theorem colBlocks_total_card {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) :
    (Finset.univ.biUnion (colBlock hm hR ht)).card = R.card + chainHeight R := by
  rw [Finset.card_biUnion (fun s _ t _ hst => colBlocks_disjoint hm hR ht hst)]
  simp_rw [colBlock_card]
  rw [Finset.sum_add_distrib,levels_total_card]
  simp

/-- The constructed paired blocks leave equally many unused labels on either side. -/
theorem complements_card_eq {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) :
    ((Finset.Icc 1 N) \ Finset.univ.biUnion (rowBlock hm hR ht)).card =
      ((Finset.Icc 1 N) \ Finset.univ.biUnion (colBlock hm hR ht)).card := by
  have hr : Finset.univ.biUnion (rowBlock hm hR ht) ⊆ Finset.Icc 1 N := by
    intro i hi
    obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hi
    exact rowBlock_subset hm hR ht t hit
  have hc : Finset.univ.biUnion (colBlock hm hR ht) ⊆ Finset.Icc 1 N := by
    intro i hi
    obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hi
    exact colBlock_subset hm hR ht t hit
  rw [Finset.card_sdiff_of_subset hr,Finset.card_sdiff_of_subset hc,
    rowBlocks_total_card,colBlocks_total_card]

theorem blocks_fit_square {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal) : R.card + chainHeight R ≤ N := by
  have hsub : Finset.univ.biUnion (rowBlock hm hR ht) ⊆ Finset.Icc 1 N := by
    intro i hi
    obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hi
    exact rowBlock_subset hm hR ht t hit
  have h := Finset.card_le_card hsub
  rw [rowBlocks_total_card] at h
  simpa using h

/-- Empty input gives no levels or blocks, for every ambient square. -/
theorem empty_blocks (N : ℕ) :
    Finset.univ.biUnion (rowBlock (N:=N) (R:=∅) (by simp [IsMatching])
      (Finset.empty_subset _) empty_terminal) = ∅ := by
  have h : chainHeight (∅ : Edges) = 0 := le_antisymm (chainHeight_le_card ∅) (Nat.zero_le _)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨t,_,_⟩ := Finset.mem_biUnion.mp hi
  have ht := t.isLt
  omega

def exampleMatching : Edges := {(3,5),(4,3),(6,6)}

theorem example_matching : IsMatching exampleMatching := by decide
theorem example_grid : exampleMatching ⊆ grid 6 6 := by decide
theorem example_terminal : chosenRewrite exampleMatching = .terminal := by decide

theorem example_levels :
    chainHeight exampleMatching = 2 ∧
    heightLevel exampleMatching 1 = {(3,5),(4,3)} ∧
    heightLevel exampleMatching 2 = {(6,6)} := by decide

/-- A genuine multi-edge decreasing level and a second increasing-chain level. -/
theorem example_anchors :
    rowAnchor example_matching example_grid example_terminal ⟨0,by decide⟩ = 1 ∧
    rowAnchor example_matching example_grid example_terminal ⟨1,by decide⟩ = 2 ∧
    colAnchor example_matching example_grid example_terminal ⟨0,by decide⟩ = 1 ∧
    colAnchor example_matching example_grid example_terminal ⟨1,by decide⟩ = 2 := by
  simp only [rowAnchor,colAnchor,Finset.orderEmbOfCardLe,RelEmbedding.coe_trans,
    Function.comp_apply,Finset.orderEmbOfFin_apply,Fin.castLEOrderEmb_apply,Fin.getElem_fin,Fin.coe_castLE]
  have hr : unusedRows 6 exampleMatching = {1,2,5} := by decide
  have hc : unusedCols 6 exampleMatching = {1,2,4} := by decide
  have sr : (unusedRows 6 exampleMatching).sort (· ≤ ·) = [1,2,5] := by
    rw [hr]
    norm_num [Finset.sort_insert]
  have sc : (unusedCols 6 exampleMatching).sort (· ≤ ·) = [1,2,4] := by
    rw [hc]
    norm_num [Finset.sort_insert]
  simp [sr,sc]

theorem example_blocks :
    rowBlock example_matching example_grid example_terminal ⟨0,by decide⟩ = {1,3,4} ∧
    colBlock example_matching example_grid example_terminal ⟨0,by decide⟩ = {1,3,5} ∧
    rowBlock example_matching example_grid example_terminal ⟨1,by decide⟩ = {2,6} ∧
    colBlock example_matching example_grid example_terminal ⟨1,by decide⟩ = {2,6} := by
  simp only [rowBlock,colBlock,example_anchors.1,example_anchors.2.1,
    example_anchors.2.2.1,example_anchors.2.2.2]
  decide

/-- The selected example leaves different concrete labels, but equal complementary cardinalities. -/
theorem example_complements :
    (Finset.Icc 1 6 \ Finset.univ.biUnion
      (rowBlock example_matching example_grid example_terminal)) = {5} ∧
    (Finset.Icc 1 6 \ Finset.univ.biUnion
      (colBlock example_matching example_grid example_terminal)) = {4} := by
  have hu : (Finset.univ : Finset (Fin (chainHeight exampleMatching))) =
      {⟨0,by decide⟩,⟨1,by decide⟩} := by decide
  rw [hu]
  simp only [Finset.biUnion_insert,Finset.singleton_biUnion,example_blocks.1,
    example_blocks.2.1,example_blocks.2.2.1,example_blocks.2.2.2]
  decide

end SelfContainedCycle047
