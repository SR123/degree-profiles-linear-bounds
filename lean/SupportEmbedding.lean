import PathCompression

namespace SelfContainedCycle042
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle039 SelfContainedCycle040 SelfContainedCycle041

/-- Appended row interval, with cardinality exactly L, including L=0. -/
def tailRows (n L : ℕ) : Finset ℕ := Finset.Icc (n+1) (n+L)

@[simp] theorem tailRows_card (n L : ℕ) : (tailRows n L).card = L := by
  simp [tailRows]

theorem enum_bounds {n L : ℕ} {S : Finset ℕ} (hS : S ⊆ tailRows n L) (a : Fin S.card) :
    n < S.orderEmbOfFin rfl a ∧ S.orderEmbOfFin rfl a ≤ n+L := by
  have h := Finset.mem_Icc.mp (hS (S.orderEmbOfFin_mem rfl a))
  exact ⟨h.1,h.2⟩

/-- Fix the old prefix, enumerate the selected rows, and move the infinite tail beyond the ambient rectangle. -/
def supportMap (n L : ℕ) (S : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i ≤ n then i
  else if hk : i ≤ n+S.card then S.orderEmbOfFin rfl ⟨i-n-1, by omega⟩
  else n+L+(i-(n+S.card))

theorem supportMap_old (n L : ℕ) (S : Finset ℕ) (i : ℕ) (hi : i ≤ n) :
    supportMap n L S i = i := by simp [supportMap,hi]

theorem supportMap_middle (n L : ℕ) (S : Finset ℕ) (i : ℕ)
    (hi : n < i) (hk : i ≤ n+S.card) :
    supportMap n L S i = S.orderEmbOfFin rfl ⟨i-n-1, by omega⟩ := by
  simp [supportMap, show ¬ i ≤ n by omega, hk]

theorem supportMap_tail (n L : ℕ) (S : Finset ℕ) (i : ℕ) (hi : n+S.card < i) :
    supportMap n L S i = n+L+(i-(n+S.card)) := by
  simp [supportMap, show ¬ i ≤ n by omega, show ¬ i ≤ n+S.card by omega]

theorem supportMap_strictMono {n L : ℕ} {S : Finset ℕ} (hS : S ⊆ tailRows n L) :
    StrictMono (supportMap n L S) := by
  intro i j hij
  by_cases hi : i ≤ n
  · rw [supportMap_old n L S i hi]
    by_cases hj : j ≤ n
    · rw [supportMap_old n L S j hj]; exact hij
    · by_cases hjk : j ≤ n+S.card
      · rw [supportMap_middle n L S j (by omega) hjk]
        have hb := enum_bounds hS (⟨j-n-1, by omega⟩ : Fin S.card)
        omega
      · rw [supportMap_tail n L S j (by omega)]; omega
  · by_cases hik : i ≤ n+S.card
    · rw [supportMap_middle n L S i (by omega) hik]
      by_cases hjk : j ≤ n+S.card
      · rw [supportMap_middle n L S j (by omega) hjk]
        apply (S.orderEmbOfFin rfl).strictMono
        change i-n-1 < j-n-1
        omega
      · rw [supportMap_tail n L S j (by omega)]
        have hb := enum_bounds hS (⟨i-n-1, by omega⟩ : Fin S.card)
        omega
    · rw [supportMap_tail n L S i (by omega), supportMap_tail n L S j (by omega)]
      omega

def supportEmbedding {n L : ℕ} (S : Finset ℕ) (hS : S ⊆ tailRows n L) : ℕ ↪ ℕ :=
  ⟨supportMap n L S, (supportMap_strictMono hS).injective⟩

theorem supportEmbedding_old {n L : ℕ} (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    ∀ i ≤ n, supportEmbedding S hS i = i := supportMap_old n L S

theorem supportEmbedding_preimage {n L : ℕ} (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    ∀ i, supportEmbedding S hS i ∈ Finset.Icc 1 (n+L) ↔ i ∈ Finset.Icc 1 (n+S.card) := by
  intro i
  change supportMap n L S i ∈ _ ↔ _
  by_cases hi : i ≤ n
  · rw [supportMap_old n L S i hi]; simp only [Finset.mem_Icc]; omega
  · by_cases hk : i ≤ n+S.card
    · rw [supportMap_middle n L S i (by omega) hk]
      have hb := enum_bounds hS (⟨i-n-1, by omega⟩ : Fin S.card)
      simp only [Finset.mem_Icc]; omega
    · rw [supportMap_tail n L S i (by omega)]
      simp only [Finset.mem_Icc]; omega

/-- Every selected row is attained, and every compressed appended row is selected. -/
theorem supportEmbedding_image {n L : ℕ} (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (tailRows n S.card).map (supportEmbedding S hS) = S := by
  ext j
  constructor
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
    change supportMap n L S i ∈ S
    rw [supportMap_middle n L S i hlo hhi]
    exact S.orderEmbOfFin_mem rfl _
  · intro hj
    have hr : j ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hj
    obtain ⟨a,ha⟩ := hr
    refine Finset.mem_map.mpr ⟨n+a.val+1, Finset.mem_Icc.mpr ⟨by omega,by omega⟩, ?_⟩
    change supportMap n L S (n+a.val+1) = j
    rw [supportMap_middle n L S (n+a.val+1) (by omega) (by omega)]
    have hi : (⟨n+a.val+1-n-1, by omega⟩ : Fin S.card) = a := by apply Fin.ext; change n+a.val+1-n-1 = a.val; omega
    rw [hi]; exact ha

/-- No existential embedding premise remains in the all-subsets geometric statement. -/
theorem every_support_embedding (n L : ℕ) (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    ∃ f : ℕ ↪ ℕ, StrictMono f ∧ (∀ i ≤ n, f i = i) ∧
      (tailRows n S.card).map f = S ∧
      (∀ i, f i ∈ Finset.Icc 1 (n+L) ↔ i ∈ Finset.Icc 1 (n+S.card)) :=
  ⟨supportEmbedding S hS, supportMap_strictMono hS, supportEmbedding_old S hS,
    supportEmbedding_image S hS, supportEmbedding_preimage S hS⟩

theorem old_matching_fixed {n L m : ℕ} (S : Finset ℕ) (hS : S ⊆ tailRows n L)
    (R : Edges) (hR : R ⊆ grid n m) : rowRename (supportEmbedding S hS) R = R := by
  have fixed : ∀ e ∈ R, edgeEmbedding (supportEmbedding S hS) (Function.Embedding.refl ℕ) e = e := by
    intro e he
    have hi := (Finset.mem_Icc.mp (Finset.mem_product.mp (hR he)).1).2
    exact Prod.ext (supportEmbedding_old S hS e.1 hi) rfl
  ext e
  constructor
  · intro he
    obtain ⟨x,hx,hxe⟩ := Finset.mem_map.mp he
    rw [fixed x hx] at hxe
    exact hxe ▸ hx
  · intro he
    exact Finset.mem_map.mpr ⟨e,he,fixed e he⟩

theorem grid_row_mono {n N m : ℕ} (h : n ≤ N) : grid n m ⊆ grid N m := by
  intro e he
  obtain ⟨hr,hc⟩ := Finset.mem_product.mp he
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hr
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hl,hu.trans h⟩,hc⟩

/-- The coefficient for k appended rows used in their entirety. -/
noncomputable def coefficient (n m : ℕ) (R : Edges) (k : ℕ) : ℤ :=
  ∑ xs ∈ historyPaths (n+k) m n R (tailRows n k), pathWeight xs

/-- The signed fiber sum depends only on |S|, with the embedding actually constructed. -/
theorem fiber_sum_by_card {n L m d : ℕ} (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (∑ xs ∈ historyPaths (n+L) m n R S, pathWeight xs) = coefficient n m R S.card := by
  have hh := historyPaths_sum_eq (supportEmbedding S hS) (supportMap_strictMono hS)
    (supportEmbedding_old S hS) (supportEmbedding_preimage S hS) R hm
    (hR.trans (grid_row_mono (Nat.le_add_right n S.card))) hd hn (tailRows n S.card)
  rw [old_matching_fixed S hS R hR, supportEmbedding_image S hS] at hh
  exact hh.symm


theorem appended_rows_subset {n L m : ℕ} (R : Edges) (hR : R ⊆ grid (n+L) m) :
    (rows R).filter (n < ·) ⊆ tailRows n L := by
  intro i hi
  obtain ⟨hir,hni⟩ := Finset.mem_filter.mp hi
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hir
  have hu := (Finset.mem_Icc.mp (Finset.mem_product.mp (hR he)).1).2
  exact Finset.mem_Icc.mpr ⟨hni,by omega⟩

theorem pathHistory_subset {n L m : ℕ} (xs : List (Edges × ℤ)) (R : Edges)
    (hR : R ⊆ grid (n+L) m) (hp : ValidPath (n+L) m R xs) :
    pathHistory n R xs ⊆ tailRows n L := by
  induction xs generalizing R with
  | nil => exact appended_rows_subset R hR
  | cons x xs ih =>
    exact Finset.union_subset (appended_rows_subset R hR)
      (ih x.1 (chosenBranch_closed hR hp.1).2 hp.2)

noncomputable def histories (n L d : ℕ) : Finset (Finset ℕ) :=
  (tailRows n L).powerset.filter (fun S => S.card ≤ d)

theorem pathHistory_mem_histories {n L m d : ℕ} (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (xs : List (Edges × ℤ)) (hx : xs ∈ allPaths (n+L) m R) :
    pathHistory n R xs ∈ histories n L d := by
  have hR' := hR.trans (grid_row_mono (Nat.le_add_right n L))
  have hp := (mem_allPaths_iff R xs hm hR').mp hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (pathHistory_subset xs R hR' hp),
    (validPath_history_bound R xs hm hd hn hp).trans hd⟩

/-- Partition the actual finite path sum by its whole encountered history. -/
theorem normalizer_eq_history_sum {n L m d : ℕ} (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hd : R.card ≤ d) (hn : 2*d ≤ n) :
    normalizer (n+L) m R = ∑ S ∈ histories n L d, coefficient n m R S.card := by
  classical
  rw [normalizer_eq_allPaths_sum]
  have hf := Finset.sum_fiberwise_of_maps_to (pathHistory_mem_histories (L:=L) R hm hR hd hn) pathWeight
  calc
    (∑ xs ∈ allPaths (n+L) m R, pathWeight xs) =
        ∑ S ∈ histories n L d, ∑ xs ∈ historyPaths (n+L) m n R S, pathWeight xs := hf.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      exact fiber_sum_by_card R hm hR hd hn S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)

theorem histories_card_fiber (n L d k : ℕ) (hk : k ≤ d) :
    (histories n L d).filter (fun S => S.card = k) = (tailRows n L).powersetCard k := by
  ext S
  simp only [histories, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hS,_⟩,hcard⟩; exact ⟨hS,hcard⟩
  · rintro ⟨hS,hcard⟩; exact ⟨⟨hS,by omega⟩,hcard⟩

/-- A finite counting identity, applied below with the constructed coefficient. -/
theorem sum_histories_by_card (n L d : ℕ) (c : ℕ → ℤ) :
    (∑ S ∈ histories n L d, c S.card) = ∑ k ∈ Finset.range (d+1), (L.choose k : ℤ) * c k := by
  classical
  have hmaps : ∀ S ∈ histories n L d, S.card ∈ Finset.range (d+1) := by
    intro S hS
    have hcard := (Finset.mem_filter.mp hS).2
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps c]
  apply Finset.sum_congr rfl
  intro k hk
  rw [histories_card_fiber n L d k (by have := Finset.mem_range.mp hk; omega)]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, tailRows_card]

/-- The unmarked integral binomial identity, with all geometric and path inputs discharged. -/
theorem normalizer_binomial {n m d : ℕ} (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hd : R.card ≤ d) (hn : 2*d ≤ n) (L : ℕ) :
    normalizer (n+L) m R = ∑ k ∈ Finset.range (d+1), (L.choose k : ℤ) * coefficient n m R k := by
  rw [normalizer_eq_history_sum R hm hR hd hn, sum_histories_by_card]


@[simp] theorem tailRows_zero (n : ℕ) : tailRows n 0 = ∅ := by
  simp [tailRows]

/-- The construction covers an empty selected subset without an exceptional assumption. -/
theorem supportMap_empty (n L i : ℕ) :
    supportMap n L ∅ i = if i ≤ n then i else L+i := by
  by_cases hi : i ≤ n
  · simp [supportMap_old n L ∅ i hi,hi]
  · rw [supportMap_tail n L ∅ i (by simpa using (show n < i by omega)), if_neg hi]
    simp only [Finset.card_empty, Nat.add_zero]
    omega

/-- In the old rectangle, the entire appended history is empty. -/
theorem zero_historyPaths {n m : ℕ} (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid n m) :
    historyPaths n m n R ∅ = allPaths n m R := by
  classical
  ext xs
  simp only [historyPaths, Finset.mem_filter, and_iff_left_iff_imp]
  intro hx
  have hp := (mem_allPaths_iff R xs hm hR).mp hx
  have hs := pathHistory_subset (L:=0) xs R hR hp
  rw [tailRows_zero] at hs
  exact Finset.subset_empty.mp hs

theorem coefficient_zero {n m : ℕ} (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid n m) :
    coefficient n m R 0 = normalizer n m R := by
  unfold coefficient
  rw [Nat.add_zero, tailRows_zero, zero_historyPaths R hm hR]
  exact (normalizer_eq_allPaths_sum n m R).symm

/-- No coefficient beyond the input degree can contribute in the stable old prefix. -/
theorem coefficient_gt_degree {n m d k : ℕ} (R : Edges) (hm : IsMatching R)
    (hR : R ⊆ grid n m) (hd : R.card ≤ d) (hn : 2*d ≤ n) (hk : d < k) :
    coefficient n m R k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro xs hx
  obtain ⟨hp,hh⟩ := Finset.mem_filter.mp hx
  have hR' := hR.trans (grid_row_mono (Nat.le_add_right n k))
  have hv := (mem_allPaths_iff R xs hm hR').mp hp
  have hc := (validPath_history_bound R xs hm hd hn hv).trans hd
  rw [hh, tailRows_card] at hc
  omega

/-- An actual nonidentity support with gaps and a checked infinite-tail boundary. -/
theorem sparse_embedding_example :
    supportMap 4 4 {6,8} 0 = 0 ∧ supportMap 4 4 {6,8} 4 = 4 ∧
    supportMap 4 4 {6,8} 5 = 6 ∧ supportMap 4 4 {6,8} 6 = 8 ∧
    supportMap 4 4 {6,8} 7 = 9 ∧ supportMap 4 4 {6,8} 8 = 10 := by
  norm_num [supportMap, Finset.orderEmbOfFin_apply, Finset.sort_insert]
  decide

theorem sparse_image_and_preimage :
    (tailRows 4 2).map (supportEmbedding {6,8} (by decide : ({6,8}:Finset ℕ) ⊆ tailRows 4 4)) = {6,8} ∧
    (∀ i, supportEmbedding {6,8} (by decide : ({6,8}:Finset ℕ) ⊆ tailRows 4 4) i ∈ Finset.Icc 1 8 ↔
      i ∈ Finset.Icc 1 6) := by
  exact ⟨supportEmbedding_image {6,8} (by decide), supportEmbedding_preimage {6,8} (by decide)⟩

/-- A nonempty matching instantiates the identity for every L, not only sampled sizes. -/
theorem singleton_binomial_all_L (L : ℕ) :
    normalizer (2+L) 2 {(1,1)} = coefficient 2 2 {(1,1)} 0 +
      (L:ℤ) * coefficient 2 2 {(1,1)} 1 := by
  have h := normalizer_binomial (n:=2) (m:=2) (d:=1) {(1,1)}
    (by decide) (by decide) (by decide) (by decide) L
  simpa [Finset.sum_range_succ] using h

end SelfContainedCycle042
