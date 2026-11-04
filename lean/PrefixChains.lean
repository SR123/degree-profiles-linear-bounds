import SignedBranches
import TokenPaths
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Max

/-! Actual increasing-chain maxima and first failed prefixes under tail compression.
The lexicographic tie choice among longest chains is deliberately not implemented here.
-/

namespace SelfContainedCycle036

open SelfContainedCycle035

def IncreasingPair (e e' : ℕ × ℕ) : Prop :=
  (e.1 < e'.1 ∧ e.2 < e'.2) ∨ (e'.1 < e.1 ∧ e'.2 < e.2)

instance (e e' : ℕ × ℕ) : Decidable (IncreasingPair e e') := by
  unfold IncreasingPair
  infer_instance

def IsChain (C : Edges) : Prop := (C : Set (ℕ × ℕ)).Pairwise IncreasingPair

instance (C : Edges) : Decidable (IsChain C) := by
  unfold IsChain
  infer_instance

def chains (R : Edges) : Finset Edges := R.powerset.filter IsChain

@[simp] theorem mem_chains (C R : Edges) : C ∈ chains R ↔ C ⊆ R ∧ IsChain C := by
  simp [chains]

def chainHeight (R : Edges) : ℕ := (chains R).sup Finset.card

theorem chain_isMatching {C : Edges} (h : IsChain C) : IsMatching C := by
  intro e he e' he' hs
  by_contra hne
  have hi := h he he' hne
  rcases hs with hs | hs <;> rcases hi with hi | hi <;> rcases hi with ⟨h₁, h₂⟩ <;> omega

theorem chainHeight_le_card (R : Edges) : chainHeight R ≤ R.card := by
  apply Finset.sup_le
  intro C hC
  exact Finset.card_le_card ((mem_chains C R).mp hC).1

theorem chain_card_le_height {C R : Edges} (hc : IsChain C) (hC : C ⊆ R) :
    C.card ≤ chainHeight R := Finset.le_sup ((mem_chains C R).mpr ⟨hC, hc⟩)

theorem increasingPair_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (e e' : ℕ × ℕ) :
    IncreasingPair (edgeEmbedding f g e) (edgeEmbedding f g e') ↔ IncreasingPair e e' := by
  simp [IncreasingPair, edgeEmbedding, hf.lt_iff_lt, hg.lt_iff_lt]

theorem chain_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g) (C : Edges) :
    IsChain (rename f g C) ↔ IsChain C := by
  constructor
  · intro h x hx y hy hxy
    apply (increasingPair_rename f g hf hg x y).mp
    exact h (Finset.mem_map.mpr ⟨x, hx, rfl⟩) (Finset.mem_map.mpr ⟨y, hy, rfl⟩)
      (fun he => hxy ((edgeEmbedding f g).injective he))
  · intro h x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact (increasingPair_rename f g hf hg a b).mpr
      (h ha hb (fun he => hxy (congrArg (edgeEmbedding f g) he)))

def renameEmbedding (f g : ℕ ↪ ℕ) : Edges ↪ Edges := ⟨rename f g, rename_injective f g⟩

theorem chains_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g) (R : Edges) :
    chains (rename f g R) = (chains R).map (renameEmbedding f g) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hsub, hchain⟩ := (mem_chains C (rename f g R)).mp hC
    obtain ⟨D, hD, hCD⟩ := Finset.subset_map_iff.mp hsub
    change C = rename f g D at hCD
    subst C
    exact Finset.mem_map.mpr ⟨D, (mem_chains D R).mpr
      ⟨hD, (chain_rename f g hf hg D).mp hchain⟩, rfl⟩
  · intro hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_map.mp hC
    obtain ⟨hsub, hchain⟩ := (mem_chains D R).mp hD
    apply (mem_chains _ _).mpr
    exact ⟨Finset.map_subset_map.mpr hsub, (chain_rename f g hf hg D).mpr hchain⟩

theorem chainHeight_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g) (R : Edges) :
    chainHeight (rename f g R) = chainHeight R := by
  simp only [chainHeight, chains_rename f g hf hg, Finset.sup_map]
  simp [Function.comp_def, renameEmbedding]

def longestChains (R : Edges) : Finset Edges :=
  (chains R).filter (fun C => C.card = chainHeight R)

theorem longestChains_nonempty (R : Edges) : (longestChains R).Nonempty := by
  have he : (∅ : Edges) ∈ chains R := by simp [chains, IsChain]
  obtain ⟨C, hC, hmax⟩ := Finset.exists_mem_eq_sup (chains R) ⟨∅, he⟩ Finset.card
  exact ⟨C, Finset.mem_filter.mpr ⟨hC, hmax.symm⟩⟩

theorem longestChains_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g) (R : Edges) :
    longestChains (rename f g R) = (longestChains R).map (renameEmbedding f g) := by
  simp only [longestChains, chains_rename f g hf hg, Finset.filter_map,
    chainHeight_rename f g hf hg]
  simp [Function.comp_def, renameEmbedding]

def rowPrefix (R : Edges) (a : ℕ) : Edges := R.filter (fun e => e.1 ≤ a)
def columnPrefix (R : Edges) (a : ℕ) : Edges := R.filter (fun e => e.2 ≤ a)

theorem rowPrefix_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges) (a : ℕ) :
    rowPrefix (rename f g R) (f a) = rename f g (rowPrefix R a) := by
  simp only [rowPrefix, rename, Finset.filter_map]
  simp [Function.comp_def, edgeEmbedding, hf.le_iff_le]

theorem columnPrefix_rename (f g : ℕ ↪ ℕ) (hg : StrictMono g) (R : Edges) (a : ℕ) :
    columnPrefix (rename f g R) (g a) = rename f g (columnPrefix R a) := by
  simp only [columnPrefix, rename, Finset.filter_map]
  simp [Function.comp_def, edgeEmbedding, hg.le_iff_le]

theorem mem_prefixRows (R : Edges) (a i : ℕ) :
    i ∈ rows (rowPrefix R a) ↔ i ∈ rows R ∧ i ≤ a := by
  simp only [rows, rowPrefix, Finset.mem_image, Finset.mem_filter]
  aesop

theorem freeBefore_interval (R : Edges) (a N : ℕ) (ha : a ≤ N) :
    freeBefore (Finset.Icc 1 N) R a = Finset.Icc 1 a \ rows (rowPrefix R a) := by
  ext i
  simp only [freeBefore, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, mem_prefixRows]
  by_cases hi : i ∈ rows R <;> simp_all
  omega

theorem freeBefore_card (R : Edges) (a N : ℕ) (ha : a ≤ N)
    (positive : ∀ e ∈ R, 0 < e.1) :
    (freeBefore (Finset.Icc 1 N) R a).card = a - (rows (rowPrefix R a)).card := by
  have hsub : rows (rowPrefix R a) ⊆ Finset.Icc 1 a := by
    intro i hi
    obtain ⟨hR, hia⟩ := (mem_prefixRows R a i).mp hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hR
    exact Finset.mem_Icc.mpr ⟨positive e he, hia⟩
  rw [freeBefore_interval R a N ha, Finset.card_sdiff_of_subset hsub]
  simp

def RowFails (R : Edges) (a : ℕ) : Prop :=
  a - (rows (rowPrefix R a)).card < chainHeight (rowPrefix R a)

def ColumnFails (R : Edges) (a : ℕ) : Prop :=
  a - (cols (columnPrefix R a)).card < chainHeight (columnPrefix R a)

instance (R : Edges) (a : ℕ) : Decidable (RowFails R a) := by unfold RowFails; infer_instance
instance (R : Edges) (a : ℕ) : Decidable (ColumnFails R a) := by unfold ColumnFails; infer_instance

/-- The strict small-B guard in the signed branch module follows from an actual failure. -/
theorem failed_longest_chain_guard {R C : Edges} {a N : ℕ}
    (ha : a ≤ N) (positive : ∀ e ∈ R, 0 < e.1)
    (hfail : RowFails R a) (hC : C ∈ longestChains (rowPrefix R a)) :
    (freeBefore (Finset.Icc 1 N) R a).card < C.card := by
  have hmax := (Finset.mem_filter.mp hC).2
  rw [freeBefore_card R a N ha positive, hmax]
  exact hfail

theorem complement_columns_disjoint {R C : Edges} (hm : IsMatching R) (hC : C ⊆ R) :
    Disjoint (cols (R \ C)) (cols C) := by
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hj
  obtain ⟨e', he', heq'⟩ := Finset.mem_image.mp hj'
  have heR := (Finset.mem_sdiff.mp he).1
  have hnot := (Finset.mem_sdiff.mp he).2
  have hee' := hm e heR e' (hC he') (Or.inr (heq.trans heq'.symm))
  exact hnot (hee' ▸ he')

/-- Degree control for actual failure/longest-chain data, with the former guards discharged. -/
theorem actual_row_branch_card_le {R C Q : Edges} {a N : ℕ} {z : ℤ}
    (hm : IsMatching R) (ha : a ≤ N) (positive : ∀ e ∈ R, 0 < e.1)
    (hfail : RowFails R a) (hC : C ∈ longestChains (rowPrefix R a))
    (hb : Branch (R \ C) C (freeBefore (Finset.Icc 1 N) R a)
      (targetRows (Finset.Icc 1 N) R C a) Q z) : Q.card ≤ R.card := by
  obtain ⟨hsub, hchain⟩ := (mem_chains _ _).mp (Finset.mem_filter.mp hC).1
  have hCR : C ⊆ R := hsub.trans (Finset.filter_subset _ _)
  have hbound := branch_card_le (chain_isMatching hchain)
    (failed_longest_chain_guard ha positive hfail hC) (complement_columns_disjoint hm hCR) hb
  simpa only [Finset.sdiff_union_of_subset hCR] using hbound

theorem rowFails_bound {R : Edges} {a : ℕ} (h : RowFails R a) : a < 2 * R.card := by
  have hu : (rows (rowPrefix R a)).card ≤ R.card :=
    Finset.card_image_le.trans (Finset.card_filter_le R _)
  have hc : chainHeight (rowPrefix R a) ≤ R.card :=
    (chainHeight_le_card _).trans (Finset.card_filter_le R _)
  exact SelfContainedCycle034.failed_prefix_lt_twice hu hc h

theorem columnFails_bound {R : Edges} {a : ℕ} (h : ColumnFails R a) : a < 2 * R.card := by
  have hu : (cols (columnPrefix R a)).card ≤ R.card :=
    Finset.card_image_le.trans (Finset.card_filter_le R _)
  have hc : chainHeight (columnPrefix R a) ≤ R.card :=
    (chainHeight_le_card _).trans (Finset.card_filter_le R _)
  exact SelfContainedCycle034.failed_prefix_lt_twice hu hc h

theorem rowFails_old {R : Edges} {a n d : ℕ} (h : RowFails R a)
    (hd : R.card ≤ d) (hn : 2 * d ≤ n) : a < n := by
  have hbound := rowFails_bound h
  omega

/-- At a fixed old prefix, an embedding has no gap in the prefix count. -/
theorem rowFails_fixed_prefix (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (R : Edges) (a : ℕ) (ha : f a = a) :
    RowFails (rename f g R) a ↔ RowFails R a := by
  unfold RowFails
  conv_lhs => rw [← ha]
  rw [rowPrefix_rename f g hf, rows_rename, Finset.card_map,
    chainHeight_rename f g hf hg, ha]

theorem columnFails_fixed_prefix (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (R : Edges) (a : ℕ) (ha : g a = a) :
    ColumnFails (rename f g R) a ↔ ColumnFails R a := by
  unfold ColumnFails
  conv_lhs => rw [← ha]
  rw [columnPrefix_rename f g hg, cols_rename, Finset.card_map,
    chainHeight_rename f g hf hg, ha]

/-- The size hypothesis removes every possibly failing prefix outside the fixed old part. -/
theorem rowFails_tail_compression (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (R : Edges) (n d : ℕ) (fixOld : ∀ i ≤ n, f i = i)
    (hd : R.card ≤ d) (hn : 2 * d ≤ n) (a : ℕ) :
    RowFails (rename f g R) a ↔ RowFails R a := by
  by_cases ha : a ≤ n
  · exact rowFails_fixed_prefix f g hf hg R a (fixOld a ha)
  · have hs : ¬ RowFails R a := by
      intro h
      have hold := rowFails_old h hd hn
      omega
    have hb : ¬ RowFails (rename f g R) a := by
      intro h
      have hcard : (rename f g R).card ≤ d := by simpa using hd
      have hold := rowFails_old h hcard hn
      omega
    exact iff_of_false hb hs

theorem columnFails_row_compression (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges) (a : ℕ) :
    ColumnFails (rename f (Function.Embedding.refl ℕ) R) a ↔ ColumnFails R a :=
  columnFails_fixed_prefix f (Function.Embedding.refl ℕ) hf strictMono_id R a rfl

def rowFailures (R : Edges) : Finset ℕ := (Finset.range (2 * R.card)).filter (RowFails R)
def columnFailures (R : Edges) : Finset ℕ := (Finset.range (2 * R.card)).filter (ColumnFails R)

@[simp] theorem mem_rowFailures (R : Edges) (a : ℕ) : a ∈ rowFailures R ↔ RowFails R a := by
  simp only [rowFailures, Finset.mem_filter, Finset.mem_range]
  exact and_iff_right_of_imp rowFails_bound

@[simp] theorem mem_columnFailures (R : Edges) (a : ℕ) : a ∈ columnFailures R ↔ ColumnFails R a := by
  simp only [columnFailures, Finset.mem_filter, Finset.mem_range]
  exact and_iff_right_of_imp columnFails_bound

theorem rowFailures_tail_compression (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (R : Edges) (n d : ℕ) (fixOld : ∀ i ≤ n, f i = i)
    (hd : R.card ≤ d) (hn : 2 * d ≤ n) :
    rowFailures (rename f g R) = rowFailures R := by
  ext a
  simp only [mem_rowFailures]
  exact rowFails_tail_compression f g hf hg R n d fixOld hd hn a

theorem columnFailures_row_compression (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges) :
    columnFailures (rename f (Function.Embedding.refl ℕ) R) = columnFailures R := by
  ext a
  simp only [mem_columnFailures]
  exact columnFails_row_compression f hf R a

def firstRowFailure (R : Edges) : WithTop ℕ := (rowFailures R).min
def firstColumnFailure (R : Edges) : WithTop ℕ := (columnFailures R).min

theorem firstRowFailure_tail_compression (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (R : Edges) (n d : ℕ) (fixOld : ∀ i ≤ n, f i = i)
    (hd : R.card ≤ d) (hn : 2 * d ≤ n) :
    firstRowFailure (rename f g R) = firstRowFailure R := by
  simp only [firstRowFailure, rowFailures_tail_compression f g hf hg R n d fixOld hd hn]

theorem firstColumnFailure_row_compression (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges) :
    firstColumnFailure (rename f (Function.Embedding.refl ℕ) R) = firstColumnFailure R := by
  simp only [firstColumnFailure, columnFailures_row_compression f hf R]

/-- Old row prefixes are literally unchanged, not merely isomorphic. -/
theorem old_rowPrefix_eq (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges)
    (n a : ℕ) (fixOld : ∀ i ≤ n, f i = i) (ha : a ≤ n) :
    rowPrefix (rename f (Function.Embedding.refl ℕ) R) a = rowPrefix R a := by
  have hp := rowPrefix_rename f (Function.Embedding.refl ℕ) hf R a
  rw [fixOld a ha] at hp
  rw [hp]
  ext e
  constructor
  · intro he
    obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp he
    have hxa : x.1 ≤ a := (Finset.mem_filter.mp hx).2
    have hfix : edgeEmbedding f (Function.Embedding.refl ℕ) x = x := by
      exact Prod.ext (fixOld x.1 (le_trans hxa ha)) rfl
    rw [hfix] at hxe
    simpa only [hxe] using hx
  · intro he
    have hea : e.1 ≤ a := (Finset.mem_filter.mp he).2
    apply Finset.mem_map.mpr
    exact ⟨e, he, Prod.ext (fixOld e.1 (le_trans hea ha)) rfl⟩

theorem old_row_longestChains_eq (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges)
    (n a : ℕ) (fixOld : ∀ i ≤ n, f i = i) (ha : a ≤ n) :
    longestChains (rowPrefix (rename f (Function.Embedding.refl ℕ) R) a) =
      longestChains (rowPrefix R a) := by
  rw [old_rowPrefix_eq f hf R n a fixOld ha]

theorem column_longestChains_map (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges) (a : ℕ) :
    longestChains (columnPrefix (rename f (Function.Embedding.refl ℕ) R) a) =
      (longestChains (columnPrefix R a)).map (renameEmbedding f (Function.Embedding.refl ℕ)) := by
  have hp := columnPrefix_rename f (Function.Embedding.refl ℕ) strictMono_id R a
  change columnPrefix (rename f (Function.Embedding.refl ℕ) R) a =
    rename f (Function.Embedding.refl ℕ) (columnPrefix R a) at hp
  rw [hp, longestChains_rename f (Function.Embedding.refl ℕ) hf strictMono_id]

inductive FailureChoice where
  | row (a : ℕ)
  | column (a : ℕ)
  | terminal
  deriving DecidableEq, Repr

def chooseFailure (R : Edges) : FailureChoice :=
  if hr : (rowFailures R).Nonempty then .row ((rowFailures R).min' hr)
  else if hc : (columnFailures R).Nonempty then .column ((columnFailures R).min' hc)
  else .terminal

theorem chooseFailure_congr (R S : Edges) (hr : rowFailures R = rowFailures S)
    (hc : columnFailures R = columnFailures S) : chooseFailure R = chooseFailure S := by
  simp only [chooseFailure, hr, hc]

/-- The actual row-priority/column/terminal decision is preserved. -/
theorem chooseFailure_tail_compression (f : ℕ ↪ ℕ) (hf : StrictMono f)
    (R : Edges) (n d : ℕ) (fixOld : ∀ i ≤ n, f i = i)
    (hd : R.card ≤ d) (hn : 2 * d ≤ n) :
    chooseFailure (rename f (Function.Embedding.refl ℕ) R) = chooseFailure R := by
  apply chooseFailure_congr
  · exact rowFailures_tail_compression f (Function.Embedding.refl ℕ) hf strictMono_id
      R n d fixOld hd hn
  · exact columnFailures_row_compression f hf R

/-! Kernel-checked examples: both orientations, a positive terminal, and a real tie. -/

theorem row_example :
    chooseFailure {(1, 1), (5, 3)} = .row 1 := by decide

theorem column_example :
    chooseFailure {(3, 1), (5, 3)} = .column 1 := by decide

theorem terminal_example :
    chooseFailure {(3, 3), (5, 5)} = .terminal := by decide

theorem tied_longest_example :
    longestChains {(3, 2), (5, 1)} = {{(3, 2)}, {(5, 1)}} := by decide

theorem column_example_compressed :
    chooseFailure (rename gapEmbedding (Function.Embedding.refl ℕ) {(3, 1), (5, 3)}) =
      .column 1 := by decide

theorem tied_example_compressed :
    longestChains (rename gapEmbedding (Function.Embedding.refl ℕ) {(3, 2), (5, 1)}) =
      {{(3, 2)}, {(6, 1)}} := by decide

/-- Outside n>=2d, adding unused tail labels really can remove a failed prefix. -/
theorem outside_range_failure_changes :
    firstRowFailure {(3, 1), (4, 2), (5, 3)} = (5 : WithTop ℕ) ∧
    firstRowFailure (rename gapEmbedding (Function.Embedding.refl ℕ)
      {(3, 1), (4, 2), (5, 3)}) = ⊤ := by decide

end SelfContainedCycle036
