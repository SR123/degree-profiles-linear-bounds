import PrefixChains
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort

namespace SelfContainedCycle037

open SelfContainedCycle035 SelfContainedCycle036

def FirstRowAt (R : Edges) (a : ℕ) : Prop :=
  RowFails R a ∧ ∀ b < a, ¬ RowFails R b

theorem prefix_zero_eq_empty (R : Edges) (positive : ∀ e ∈ R, 0 < e.1) :
    rowPrefix R 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he, hzero⟩ := Finset.mem_filter.mp he
  have hp := positive e he
  omega

theorem not_rowFails_zero (R : Edges) (positive : ∀ e ∈ R, 0 < e.1) :
    ¬ RowFails R 0 := by
  have hc := chainHeight_le_card (∅ : Edges)
  simp only [Finset.card_empty] at hc
  simp only [RowFails, prefix_zero_eq_empty R positive]
  omega

/-- Adding the next prefix position can add at most its own row label. -/
theorem prefix_rows_card_step (R : Edges) (a : ℕ) :
    (rows (rowPrefix R (a+1))).card ≤ (rows (rowPrefix R a)).card + 1 := by
  have hs : rows (rowPrefix R (a+1)) ⊆ insert (a+1) (rows (rowPrefix R a)) := by
    intro i hi
    obtain ⟨hR, hia⟩ := (mem_prefixRows R (a+1) i).mp hi
    by_cases hi' : i = a+1
    · exact Finset.mem_insert.mpr (Or.inl hi')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_prefixRows R a i).mpr ⟨hR, by omega⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

/-- The unused-position count cannot decrease at the next prefix. -/
theorem unused_prefix_mono_step (R : Edges) (a : ℕ) :
    a - (rows (rowPrefix R a)).card ≤ (a+1) - (rows (rowPrefix R (a+1))).card := by
  have h := prefix_rows_card_step R a
  omega

/-- All maximum chains, including ties, end at the first failed row. -/
theorem first_failed_longest_has_endpoint {R C : Edges} {a : ℕ}
    (positive : ∀ e ∈ R, 0 < e.1) (hfirst : FirstRowAt R a)
    (hC : C ∈ longestChains (rowPrefix R a)) : ∃ e ∈ C, e.1 = a := by
  obtain ⟨hfail, hprior⟩ := hfirst
  have ha : 0 < a := by
    by_contra h
    have hz : a = 0 := by omega
    exact not_rowFails_zero R positive (hz ▸ hfail)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  simp only [Nat.succ_eq_add_one] at hfail hprior hC
  obtain ⟨hchains, hmax⟩ := Finset.mem_filter.mp hC
  obtain ⟨hsub, hc⟩ := (mem_chains _ _).mp hchains
  by_contra hnone
  have hsub' : C ⊆ rowPrefix R b := by
    intro e he
    obtain ⟨heR, hea⟩ := Finset.mem_filter.mp (hsub he)
    have hne : e.1 ≠ b+1 := fun h => hnone ⟨e, he, h⟩
    exact Finset.mem_filter.mpr ⟨heR, by omega⟩
  have hheight := chain_card_le_height hc hsub'
  have hu := unused_prefix_mono_step R b
  apply hprior b (by omega)
  unfold RowFails at hfail ⊢
  omega

/-- Bridge from the actual finite minimum; no first-failure witness is assumed. -/
theorem min_row_failure_is_first (R : Edges) (h : (rowFailures R).Nonempty) :
    FirstRowAt R ((rowFailures R).min' h) := by
  constructor
  · exact (mem_rowFailures _ _).mp (Finset.min'_mem _ h)
  · intro b hb hfail
    have hmin := Finset.min'_le (rowFailures R) b ((mem_rowFailures R b).mpr hfail)
    omega

theorem selected_row_longest_has_endpoint (R C : Edges)
    (positive : ∀ e ∈ R, 0 < e.1) (h : (rowFailures R).Nonempty)
    (hC : C ∈ longestChains (rowPrefix R ((rowFailures R).min' h))) :
    ∃ e ∈ C, e.1 = (rowFailures R).min' h :=
  first_failed_longest_has_endpoint positive (min_row_failure_is_first R h) hC


/-- Python's pair order, made explicit; ordinary product order is not lexicographic. -/
abbrev LexEdge := ℕ ×ₗ ℕ

def lexEmbedding : (ℕ × ℕ) ↪ LexEdge := ⟨toLex, fun _ _ h => h⟩

def chainCode (C : Edges) : List LexEdge := (C.map lexEmbedding).sort

theorem chainCode_injective : Function.Injective chainCode := by
  intro C D h
  have hsets := congrArg List.toFinset h
  simp only [chainCode, Finset.sort_toFinset] at hsets
  exact Finset.map_injective lexEmbedding hsets

def lexRename (f g : ℕ ↪ ℕ) : LexEdge ↪ LexEdge where
  toFun e := toLex (edgeEmbedding f g (ofLex e))
  inj' := fun _ _ h => (edgeEmbedding f g).injective h

theorem lexRename_strictMono (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (lexRename f g) := by
  intro e e' h
  simp only [Prod.Lex.lt_iff] at h ⊢
  change f e.1 < f e'.1 ∨ f e.1 = f e'.1 ∧ g e.2 < g e'.2
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (hf h)
  · exact Or.inr ⟨congrArg f h, hg h'⟩

theorem chainCode_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g) (C : Edges) :
    chainCode (rename f g C) = (chainCode C).map (lexRename f g) := by
  unfold chainCode
  rw [((lexRename_strictMono f g hf hg).strictMonoOn (C.map lexEmbedding)).map_finsetSort]
  congr 1
  simp only [rename, Finset.map_map]
  rfl

theorem chainCode_order_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (C D : Edges) :
    chainCode (rename f g C) ≤ chainCode (rename f g D) ↔ chainCode C ≤ chainCode D := by
  rw [chainCode_rename f g hf hg, chainCode_rename f g hf hg]
  have hm : StrictMono (List.map (lexRename f g)) := by
    intro l l' h
    exact List.map_lt (fun _ _ h => lexRename_strictMono f g hf hg h) h
  exact hm.le_iff_le

/-- The actual lexicographic maximum among all longest increasing chains. -/
noncomputable def chosenLongest (R : Edges) : Edges :=
  Classical.choose (Finset.exists_max_image (longestChains R) chainCode (longestChains_nonempty R))

theorem chosenLongest_spec (R : Edges) :
    chosenLongest R ∈ longestChains R ∧
      ∀ C ∈ longestChains R, chainCode C ≤ chainCode (chosenLongest R) :=
  Classical.choose_spec (Finset.exists_max_image (longestChains R) chainCode (longestChains_nonempty R))

theorem chosenLongest_unique (R C : Edges) (hC : C ∈ longestChains R)
    (hmax : ∀ D ∈ longestChains R, chainCode D ≤ chainCode C) : chosenLongest R = C := by
  apply chainCode_injective
  exact le_antisymm (hmax _ (chosenLongest_spec R).1) ((chosenLongest_spec R).2 C hC)

/-- Naturality of the defined selector, proved from its finite maximum construction. -/
theorem chosenLongest_rename (f g : ℕ ↪ ℕ) (hf : StrictMono f) (hg : StrictMono g) (R : Edges) :
    chosenLongest (rename f g R) = rename f g (chosenLongest R) := by
  apply chosenLongest_unique
  · rw [longestChains_rename f g hf hg]
    exact Finset.mem_map.mpr ⟨_, (chosenLongest_spec R).1, rfl⟩
  · intro D hD
    rw [longestChains_rename f g hf hg] at hD
    obtain ⟨C, hC, rfl⟩ := Finset.mem_map.mp hD
    exact (chainCode_order_rename f g hf hg C _).mpr ((chosenLongest_spec R).2 C hC)

theorem chosen_first_row_has_endpoint (R : Edges)
    (positive : ∀ e ∈ R, 0 < e.1) (h : (rowFailures R).Nonempty) :
    ∃ e ∈ chosenLongest (rowPrefix R ((rowFailures R).min' h)),
      e.1 = (rowFailures R).min' h :=
  selected_row_longest_has_endpoint R _ positive h (chosenLongest_spec _).1

theorem chosen_old_row_eq (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges)
    (n a : ℕ) (fixOld : ∀ i ≤ n, f i = i) (ha : a ≤ n) :
    chosenLongest (rowPrefix (rename f (Function.Embedding.refl ℕ) R) a) =
      chosenLongest (rowPrefix R a) := by
  rw [old_rowPrefix_eq f hf R n a fixOld ha]


@[simp] theorem transpose_transpose (R : Edges) : transpose (transpose R) = R := by
  simp only [transpose, Finset.map_map]
  have h : swapEmbedding.trans swapEmbedding = Function.Embedding.refl (ℕ × ℕ) := by
    ext e <;> rfl
  rw [h, Finset.map_refl]

@[simp] theorem transpose_card (R : Edges) : (transpose R).card = R.card := Finset.card_map _

theorem transpose_injective : Function.Injective transpose := by
  intro R S h
  simpa only [transpose_transpose] using congrArg transpose h

theorem chain_transpose (C : Edges) : IsChain (transpose C) ↔ IsChain C := by
  have forward : ∀ D : Edges, IsChain D → IsChain (transpose D) := by
    intro D h e he e' he' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp he'
    have hxy := h hx hy (fun h => hne (congrArg swapEmbedding h))
    rcases hxy with hxy | hxy
    · exact Or.inl ⟨hxy.2, hxy.1⟩
    · exact Or.inr ⟨hxy.2, hxy.1⟩
  exact ⟨fun h => by simpa using forward (transpose C) h, forward C⟩

def transposeEmbedding : Edges ↪ Edges := ⟨transpose, transpose_injective⟩

theorem chains_transpose (R : Edges) : chains (transpose R) = (chains R).map transposeEmbedding := by
  ext C
  constructor
  · intro hC
    obtain ⟨hs, hc⟩ := (mem_chains _ _).mp hC
    obtain ⟨D, hD, hCD⟩ := Finset.subset_map_iff.mp hs
    change C = transpose D at hCD
    subst C
    exact Finset.mem_map.mpr ⟨D, (mem_chains _ _).mpr ⟨hD, (chain_transpose D).mp hc⟩, rfl⟩
  · intro hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_map.mp hC
    obtain ⟨hs, hc⟩ := (mem_chains _ _).mp hD
    exact (mem_chains _ _).mpr ⟨Finset.map_subset_map.mpr hs, (chain_transpose D).mpr hc⟩

theorem chainHeight_transpose (R : Edges) : chainHeight (transpose R) = chainHeight R := by
  simp only [chainHeight, chains_transpose, Finset.sup_map]
  simp [Function.comp_def, transposeEmbedding]

theorem rowPrefix_transpose (R : Edges) (a : ℕ) :
    rowPrefix (transpose R) a = transpose (columnPrefix R a) := by
  simp only [rowPrefix, transpose, Finset.filter_map]
  rfl

theorem rows_transpose (R : Edges) : rows (transpose R) = cols R := by
  ext i
  simp [rows, cols, transpose, swapEmbedding]

theorem rowFails_transpose (R : Edges) (a : ℕ) : RowFails (transpose R) a ↔ ColumnFails R a := by
  simp only [RowFails, ColumnFails, rowPrefix_transpose, rows_transpose, chainHeight_transpose]

theorem rowFailures_transpose (R : Edges) : rowFailures (transpose R) = columnFailures R := by
  ext a
  simp only [mem_rowFailures, mem_columnFailures, rowFails_transpose]

def FirstColumnAt (R : Edges) (a : ℕ) : Prop := ColumnFails R a ∧ ∀ b < a, ¬ ColumnFails R b

theorem firstColumnAt_iff (R : Edges) (a : ℕ) :
    FirstColumnAt R a ↔ FirstRowAt (transpose R) a := by
  simp only [FirstColumnAt, FirstRowAt, rowFails_transpose]

/-- Column-oriented selection sorts the transposed edges, as in the concrete normalizer. -/
noncomputable def chosenColumnChain (R : Edges) (a : ℕ) : Edges :=
  transpose (chosenLongest (rowPrefix (transpose R) a))

theorem chosen_column_has_endpoint (R : Edges) (a : ℕ)
    (positive : ∀ e ∈ R, 0 < e.2) (hfirst : FirstColumnAt R a) :
    ∃ e ∈ chosenColumnChain R a, e.2 = a := by
  have hp : ∀ e ∈ transpose R, 0 < e.1 := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
    exact positive x hx
  obtain ⟨e, he, hea⟩ := first_failed_longest_has_endpoint hp
    ((firstColumnAt_iff R a).mp hfirst) (chosenLongest_spec _).1
  exact ⟨swapEmbedding e, Finset.mem_map.mpr ⟨e, he, rfl⟩, hea⟩

/-- Ties in transposed tuples remain unchanged when original rows are compressed. -/
theorem chosen_column_row_compression (f : ℕ ↪ ℕ) (hf : StrictMono f) (R : Edges) (a : ℕ) :
    chosenColumnChain (rename f (Function.Embedding.refl ℕ) R) a =
      rename f (Function.Embedding.refl ℕ) (chosenColumnChain R a) := by
  unfold chosenColumnChain
  rw [transpose_rename]
  have hp := rowPrefix_rename (Function.Embedding.refl ℕ) f strictMono_id (transpose R) a
  change rowPrefix (rename (Function.Embedding.refl ℕ) f (transpose R)) a = _ at hp
  rw [hp, chosenLongest_rename (Function.Embedding.refl ℕ) f strictMono_id hf, transpose_rename]


theorem chainCode_singleton_lt {e e' : ℕ × ℕ} (h : e.1 < e'.1) :
    chainCode {e} < chainCode {e'} := by
  simp only [chainCode, Finset.map_singleton, Finset.sort_singleton]
  exact List.Lex.rel (Prod.Lex.toLex_lt_toLex.mpr (Or.inl h))

/-- The two genuinely competing singleton chains are separated by tuple lexicographic order. -/
theorem genuine_tie_choice : chosenLongest {(3, 2), (5, 1)} = {(5, 1)} := by
  apply chosenLongest_unique
  · rw [tied_longest_example]
    decide
  · intro D hD
    rw [tied_longest_example] at hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl
    · exact (chainCode_singleton_lt (by decide)).le
    · exact le_refl _

theorem genuine_tie_compression :
    chosenLongest (rename gapEmbedding (Function.Embedding.refl ℕ) {(3, 2), (5, 1)}) = {(6, 1)} := by
  rw [chosenLongest_rename gapEmbedding (Function.Embedding.refl ℕ) gapRow_strictMono strictMono_id,
    genuine_tie_choice]
  decide

/-- A transposed tie chooses by column first; the row-primary choice is different. -/
theorem column_tie_choice : chosenColumnChain {(3, 2), (5, 1)} 2 = {(3, 2)} := by
  have hp : rowPrefix (transpose {(3, 2), (5, 1)}) 2 = {(1, 5), (2, 3)} := by decide
  have hc : chosenLongest {(1, 5), (2, 3)} = {(2, 3)} := by
    apply chosenLongest_unique
    · decide
    · intro D hD
      have hl : longestChains {(1, 5), (2, 3)} = {{(1, 5)}, {(2, 3)}} := by decide
      rw [hl] at hD
      simp only [Finset.mem_insert, Finset.mem_singleton] at hD
      rcases hD with rfl | rfl
      · exact (chainCode_singleton_lt (by decide)).le
      · exact le_refl _
  rw [chosenColumnChain, hp, hc]
  decide

theorem first_failure_with_tie :
    FirstRowAt {(2, 2), (3, 1), (4, 3)} 4 ∧
    longestChains (rowPrefix {(2, 2), (3, 1), (4, 3)} 4) =
      {{(2, 2), (4, 3)}, {(3, 1), (4, 3)}} := by
  constructor
  · constructor
    · decide
    · intro b hb
      interval_cases b <;> decide
  · decide

/-- Positivity is essential: row zero is outside the intended universe. -/
theorem zero_label_boundary : RowFails {(0, 1)} 0 := by decide


inductive ChosenRewrite where
  | row (a : ℕ) (C : Edges)
  | column (a : ℕ) (C : Edges)
  | terminal
  deriving DecidableEq

noncomputable def chosenRewrite (R : Edges) : ChosenRewrite :=
  if hr : (rowFailures R).Nonempty then
    let a := (rowFailures R).min' hr
    .row a (chosenLongest (rowPrefix R a))
  else if hc : (columnFailures R).Nonempty then
    let a := (columnFailures R).min' hc
    .column a (chosenColumnChain R a)
  else .terminal

def renameChoice (f g : ℕ ↪ ℕ) : ChosenRewrite → ChosenRewrite
  | .row a C => .row a (rename f g C)
  | .column a C => .column a (rename f g C)
  | .terminal => .terminal

/-- Full first-failure, orientation, and lexicographic chain choice commute with tail compression. -/
theorem chosenRewrite_tail_compression (f : ℕ ↪ ℕ) (hf : StrictMono f)
    (R : Edges) (n d : ℕ) (fixOld : ∀ i ≤ n, f i = i)
    (hd : R.card ≤ d) (hn : 2 * d ≤ n) :
    chosenRewrite (rename f (Function.Embedding.refl ℕ) R) =
      renameChoice f (Function.Embedding.refl ℕ) (chosenRewrite R) := by
  have hr := rowFailures_tail_compression f (Function.Embedding.refl ℕ) hf strictMono_id R n d
    fixOld hd hn
  have hc := columnFailures_row_compression f hf R
  simp only [chosenRewrite, hr, hc]
  split_ifs with hr' hc'
  · simp only [renameChoice]
    have hfirst := min_row_failure_is_first R hr'
    have ha := rowFails_old hfirst.1 hd hn
    have hp := rowPrefix_rename f (Function.Embedding.refl ℕ) hf R ((rowFailures R).min' hr')
    rw [fixOld _ (Nat.le_of_lt ha)] at hp
    rw [hp, chosenLongest_rename f (Function.Embedding.refl ℕ) hf strictMono_id]
  · simp only [renameChoice, chosen_column_row_compression f hf]
  · rfl

/-- The previous-prefix hypothesis is needed: a later failed prefix can have an old maximum. -/
theorem nonfirst_endpoint_counterexample :
    RowFails {(1, 2), (2, 1)} 2 ∧
    {(1, 2)} ∈ longestChains (rowPrefix {(1, 2), (2, 1)} 2) ∧
    ¬ (∃ e ∈ ({(1, 2)} : Edges), e.1 = 2) := by decide


theorem longestChains_transpose (R : Edges) :
    longestChains (transpose R) = (longestChains R).map transposeEmbedding := by
  simp only [longestChains, chains_transpose, Finset.filter_map, chainHeight_transpose]
  simp [Function.comp_def, transposeEmbedding]

theorem chosen_column_mem_longest (R : Edges) (a : ℕ) :
    chosenColumnChain R a ∈ longestChains (columnPrefix R a) := by
  have h : transpose (chosenLongest (rowPrefix (transpose R) a)) ∈
      (longestChains (rowPrefix (transpose R) a)).map transposeEmbedding :=
    Finset.mem_map.mpr ⟨_, (chosenLongest_spec _).1, rfl⟩
  rw [← longestChains_transpose, rowPrefix_transpose, transpose_transpose] at h
  simpa only [chosenColumnChain, rowPrefix_transpose] using h

theorem min_column_failure_is_first (R : Edges) (h : (columnFailures R).Nonempty) :
    FirstColumnAt R ((columnFailures R).min' h) := by
  constructor
  · exact (mem_columnFailures _ _).mp (Finset.min'_mem _ h)
  · intro b hb hfail
    have hmin := Finset.min'_le (columnFailures R) b ((mem_columnFailures R b).mpr hfail)
    omega

theorem chosen_first_column_has_endpoint (R : Edges)
    (positive : ∀ e ∈ R, 0 < e.2) (h : (columnFailures R).Nonempty) :
    ∃ e ∈ chosenColumnChain R ((columnFailures R).min' h),
      e.2 = (columnFailures R).min' h :=
  chosen_column_has_endpoint R _ positive (min_column_failure_is_first R h)

end SelfContainedCycle037
