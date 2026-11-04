import ChainChoice

namespace SelfContainedCycle038

open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037

instance (R : Edges) : Decidable (IsMatching R) := by unfold IsMatching; infer_instance
instance (C M : Edges) (T : Finset ℕ) (z : ℤ) : Decidable (UpperTerm C T M z) := by
  unfold UpperTerm
  infer_instance
instance (S B : Finset ℕ) (M : Edges) (z : ℤ) : Decidable (LowerTerm S B M z) := by
  unfold LowerTerm
  infer_instance

/-- A removed variable precedes every added variable already by coordinate sum. -/
def SumDominates (C M : Edges) : Prop :=
  ∃ e ∈ C \ M, ∀ x ∈ M \ C, e.1 + e.2 < x.1 + x.2

/-- The first missing chain edge is coordinatewise no later than any new injection edge. -/
theorem upperTerm_sumDominates {R C M : Edges} {U : Finset ℕ} {a : ℕ} {z : ℤ}
    (hc : IsChain C) (hprefix : ∀ e ∈ C, e.1 ≤ a)
    (hm : UpperTerm C (targetRows U R C a) M z) : SumDominates C M := by
  have hcard := upperTerm_card_eq (chain_isMatching hc) hm
  have hne : (C \ M).Nonempty := by
    by_contra h
    have hsub : C ⊆ M := Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hm.2.2.2.1 heq.symm
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image (C \ M) Prod.fst hne
  have heC := (Finset.mem_sdiff.mp he).1
  have heM := (Finset.mem_sdiff.mp he).2
  have earlier_kept : ∀ y ∈ C, y.1 < e.1 → y ∈ M := by
    intro y hy hye
    by_contra hyM
    have hle := hmin y (Finset.mem_sdiff.mpr ⟨hy, hyM⟩)
    omega
  refine ⟨e, he, ?_⟩
  intro x hx
  obtain ⟨hxM, hxC⟩ := Finset.mem_sdiff.mp hx
  have hrow : e.1 ≤ x.1 := by
    by_contra h
    have hxe : x.1 < e.1 := by omega
    have hxrows : x.1 ∈ rows M := Finset.mem_image.mpr ⟨x, hxM, rfl⟩
    have hxT := hm.2.1 hxrows
    rcases Finset.mem_union.mp hxT with hxrowsC | hxlarge
    · obtain ⟨y, hyC, hyx⟩ := Finset.mem_image.mp hxrowsC
      have hyM := earlier_kept y hyC (by omega)
      have hxy := hm.1 x hxM y hyM (Or.inl hyx.symm)
      exact hxC (hxy ▸ hyC)
    · have hl := (Finset.mem_filter.mp hxlarge).2.1
      have heBound := hprefix e heC
      omega
  have hcol : e.2 ≤ x.2 := by
    by_contra h
    have hxe : x.2 < e.2 := by omega
    have hxcols : x.2 ∈ cols M := Finset.mem_image.mpr ⟨x, hxM, rfl⟩
    rw [hm.2.2.1] at hxcols
    obtain ⟨y, hyC, hyx⟩ := Finset.mem_image.mp hxcols
    have hne : y ≠ e := by intro h; subst y; omega
    have hi := hc hyC heC hne
    have hyrow : y.1 < e.1 := by rcases hi with hi | hi <;> omega
    have hyM := earlier_kept y hyC hyrow
    have hxy := hm.1 x hxM y hyM (Or.inr hyx.symm)
    exact hxC (hxy ▸ hyC)
  have hne : x ≠ e := fun h => heM (h ▸ hxM)
  have hdiff : x.1 ≠ e.1 ∨ x.2 ≠ e.2 := by
    by_contra h
    push_neg at h
    exact hne (Prod.ext h.1 h.2)
  rcases hdiff with hdiff | hdiff <;> omega


def edgeWeight (G : Edges) (H : ℕ) (e : ℕ × ℕ) : ℕ :=
  (G.card + 1) ^ (H - (e.1 + e.2))

def weightSum (G : Edges) (H : ℕ) (R : Edges) : ℕ := ∑ e ∈ R, edgeWeight G H e

/-- A concrete integer weight witnesses strictness; equal-sum tie choices are immaterial. -/
theorem sumDominates_weight_lt {C M G : Edges} {H : ℕ}
    (hM : M ⊆ G) (hG : ∀ e ∈ G, e.1 + e.2 ≤ H)
    (hd : SumDominates C M) : weightSum G H M < weightSum G H C := by
  obtain ⟨e, he, hemin⟩ := hd
  have hepos : 0 < edgeWeight G H e := pow_pos (by omega) _
  have hsumnew : (∑ x ∈ M \ C, edgeWeight G H x) < edgeWeight G H e := by
    by_cases hnew : (M \ C).Nonempty
    · obtain ⟨x, hx⟩ := hnew
      have hex := hemin x hx
      have hxH := hG x (hM (Finset.mem_sdiff.mp hx).1)
      have hk : 0 < H - (e.1 + e.2) := by omega
      have hpoint : ∀ y ∈ M \ C,
          edgeWeight G H y ≤ (G.card + 1) ^ (H - (e.1 + e.2) - 1) := by
        intro y hy
        have hey := hemin y hy
        unfold edgeWeight
        apply pow_le_pow_right' (by omega)
        omega
      have hsum := Finset.sum_le_sum hpoint
      have hcard : (M \ C).card < G.card + 1 := by
        have hc := Finset.card_le_card ((Finset.sdiff_subset : M \ C ⊆ M).trans hM)
        omega
      have hpower : 0 < (G.card + 1) ^ (H - (e.1 + e.2) - 1) := pow_pos (by omega) _
      have hprod := Nat.mul_lt_mul_of_pos_right hcard hpower
      have heq : H - (e.1 + e.2) = (H - (e.1 + e.2) - 1) + 1 := by omega
      simp only [Finset.sum_const, nsmul_eq_mul] at hsum
      unfold edgeWeight
      rw [heq, pow_succ']
      exact hsum.trans_lt hprod
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hnew
      simpa only [hz, Finset.sum_empty] using hepos
  have hsumold : edgeWeight G H e ≤ ∑ x ∈ C \ M, edgeWeight G H x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) he
  have hlt := hsumnew.trans_le hsumold
  have hCeq := Finset.sum_inter_add_sum_diff C M (edgeWeight G H)
  have hMeq := Finset.sum_inter_add_sum_diff M C (edgeWeight G H)
  rw [Finset.inter_comm M C] at hMeq
  unfold weightSum
  omega


/-- Adjoining the unchanged context does not hide the dominating removed edge. -/
theorem sumDominates_union {P C M : Edges} (hPC : Disjoint P C) (hd : SumDominates C M) :
    SumDominates (P ∪ C) (P ∪ M) := by
  obtain ⟨e, he, hmin⟩ := hd
  obtain ⟨heC, heM⟩ := Finset.mem_sdiff.mp he
  have heP : e ∉ P := fun h => Finset.disjoint_left.mp hPC h heC
  refine ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right P heC, ?_⟩, ?_⟩
  · simpa only [Finset.mem_union, not_or] using And.intro heP heM
  · intro x hx
    obtain ⟨hxPM, hxPC⟩ := Finset.mem_sdiff.mp hx
    have hxP : x ∉ P := fun h => hxPC (Finset.mem_union_left C h)
    have hxC : x ∉ C := fun h => hxPC (Finset.mem_union_right P h)
    have hxM := (Finset.mem_union.mp hxPM).resolve_left hxP
    exact hmin x (Finset.mem_sdiff.mpr ⟨hxM, hxC⟩)

def rank (G : Edges) (H : ℕ) (R : Edges) : ℕ :=
  R.card * (weightSum G H G + 1) + weightSum G H R

theorem weightSum_mono {R G : Edges} (H : ℕ) (hR : R ⊆ G) :
    weightSum G H R ≤ weightSum G H G := Finset.sum_le_sum_of_subset hR

theorem rank_lt_of_card_lt {R Q G : Edges} {H : ℕ}
    (hQ : Q ⊆ G) (hcard : Q.card < R.card) : rank G H Q < rank G H R := by
  have hw := weightSum_mono H hQ
  have hmul : (Q.card + 1) * (weightSum G H G + 1) ≤ R.card * (weightSum G H G + 1) :=
    Nat.mul_le_mul_right _ hcard
  unfold rank
  nlinarith

theorem rank_lt_of_equal_card {R Q G : Edges} {H : ℕ}
    (hcard : Q.card = R.card) (hw : weightSum G H Q < weightSum G H R) :
    rank G H Q < rank G H R := by
  simp only [rank, hcard]
  omega

/-- Strict decrease for the actual supplied-chain row branch, with the genuine prefix guard. -/
theorem row_branch_rank_lt {R C Q G : Edges} {U : Finset ℕ} {a H : ℕ} {z : ℤ}
    (hm : IsMatching R) (hc : IsChain C) (hCR : C ⊆ R)
    (hprefix : ∀ e ∈ C, e.1 ≤ a) (hB : (freeBefore U R a).card < C.card)
    (hQ : Q ⊆ G) (hG : ∀ e ∈ G, e.1 + e.2 ≤ H)
    (hb : Branch (R \ C) C (freeBefore U R a) (targetRows U R C a) Q z) :
    rank G H Q < rank G H R := by
  obtain ⟨M, hrep, _, rfl⟩ := hb
  have hPC := complement_columns_disjoint hm hCR
  have hdisjM := replacement_disjoint hPC hrep
  have hdisjC : Disjoint (R \ C) C := Finset.sdiff_disjoint
  have hRc : (R \ C).card + C.card = R.card := by
    rw [← Finset.card_union_of_disjoint hdisjC, Finset.sdiff_union_of_subset hCR]
  rcases hrep with hl | hu
  · have hcM := lowerTerm_card_lt hl hB
    have hcard : ((R \ C) ∪ M).card < R.card := by
      rw [Finset.card_union_of_disjoint hdisjM]
      omega
    exact rank_lt_of_card_lt hQ hcard
  · have hcM := upperTerm_card_eq (chain_isMatching hc) hu
    have hcard : ((R \ C) ∪ M).card = R.card := by
      rw [Finset.card_union_of_disjoint hdisjM, hcM, hRc]
    have hdom := sumDominates_union hdisjC (upperTerm_sumDominates hc hprefix hu)
    rw [Finset.sdiff_union_of_subset hCR] at hdom
    exact rank_lt_of_equal_card hcard (sumDominates_weight_lt hQ hG hdom)


@[simp] theorem weightSum_transpose (G R : Edges) (H : ℕ) :
    weightSum (transpose G) H (transpose R) = weightSum G H R := by
  unfold weightSum
  rw [transpose, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  simp [edgeWeight, swapEmbedding, Nat.add_comm]

@[simp] theorem rank_transpose (G R : Edges) (H : ℕ) :
    rank (transpose G) H (transpose R) = rank G H R := by
  simp [rank]

theorem matching_transpose (R : Edges) : IsMatching (transpose R) ↔ IsMatching R := by
  have fw : ∀ S : Edges, IsMatching S → IsMatching (transpose S) := by
    intro S hs e he e' he' hcoord
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp he'
    have hxy : x = y := hs x hx y hy (by rcases hcoord with h | h; exact Or.inr h; exact Or.inl h)
    exact congrArg swapEmbedding hxy
  exact ⟨fun h => by simpa using fw (transpose R) h, fw R⟩

def grid (N K : ℕ) : Edges := (Finset.Icc 1 N).product (Finset.Icc 1 K)

@[simp] theorem transpose_grid (N K : ℕ) : transpose (grid N K) = grid K N := by
  ext e
  simp [grid, transpose, swapEmbedding, Finset.mem_map, Prod.ext_iff, and_comm, and_left_comm, and_assoc]

theorem grid_sum_bound (N K : ℕ) : ∀ e ∈ grid N K, e.1 + e.2 ≤ N + K := by
  intro e he
  obtain ⟨hr, hc⟩ := Finset.mem_product.mp he
  have hr' := (Finset.mem_Icc.mp hr).2
  have hc' := (Finset.mem_Icc.mp hc).2
  omega

theorem grid_positive {R : Edges} {N K : ℕ} (hR : R ⊆ grid N K) : ∀ e ∈ R, 0 < e.1 := by
  intro e he
  exact (Finset.mem_Icc.mp (Finset.mem_product.mp (hR he)).1).1

/-- All first-failure maximum-chain rewrites, a relation containing the deterministic row choice. -/
def RowReduction (N : ℕ) (R Q : Edges) : Prop :=
  ∃ a C z, FirstRowAt R a ∧ C ∈ longestChains (rowPrefix R a) ∧
    Branch (R \ C) C (freeBefore (Finset.Icc 1 N) R a)
      (targetRows (Finset.Icc 1 N) R C a) Q z

theorem branch_subset_grid {R C Q : Edges} {N K a : ℕ} {z : ℤ}
    (hR : R ⊆ grid N K) (hC : C ⊆ R)
    (hb : Branch (R \ C) C (freeBefore (Finset.Icc 1 N) R a)
      (targetRows (Finset.Icc 1 N) R C a) Q z) : Q ⊆ grid N K := by
  obtain ⟨M, hm, _, rfl⟩ := hb
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hR (Finset.mem_sdiff.mp he).1
  · have hcol := replacement_cols_subset hm (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    obtain ⟨c, hc, hce⟩ := Finset.mem_image.mp hcol
    have hcG := Finset.mem_product.mp (hR (hC hc))
    refine Finset.mem_product.mpr ⟨?_, by simpa only [hce] using hcG.2⟩
    have herow : e.1 ∈ rows M := Finset.mem_image.mpr ⟨e, he, rfl⟩
    rcases hm with hl | hu
    · exact (Finset.mem_filter.mp (hl.2.1 herow)).1
    · rcases Finset.mem_union.mp (hu.2.1 herow) with heC | heLarge
      · obtain ⟨c', hc', hce'⟩ := Finset.mem_image.mp heC
        have hcG' := Finset.mem_product.mp (hR (hC hc'))
        simpa only [hce'] using hcG'.1
      · exact (Finset.mem_filter.mp heLarge).1

theorem rowReduction_closed {R Q : Edges} {N K : ℕ}
    (hR : R ⊆ grid N K) (h : RowReduction N R Q) : IsMatching Q ∧ Q ⊆ grid N K := by
  obtain ⟨a, C, z, _, hC, hb⟩ := h
  have hCR : C ⊆ R := ((mem_chains _ _).mp (Finset.mem_filter.mp hC).1).1.trans
    (Finset.filter_subset _ _)
  refine ⟨?_, branch_subset_grid hR hCR hb⟩
  obtain ⟨M, _, hm, rfl⟩ := hb
  exact hm

theorem rowReduction_rank_lt {R Q : Edges} {N K : ℕ}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (h : RowReduction N R Q) :
    rank (grid N K) (N + K) Q < rank (grid N K) (N + K) R := by
  obtain ⟨a, C, z, hf, hC, hb⟩ := h
  obtain ⟨hsub, hc⟩ := (mem_chains _ _).mp (Finset.mem_filter.mp hC).1
  have hCR : C ⊆ R := hsub.trans (Finset.filter_subset _ _)
  have positive := grid_positive hR
  obtain ⟨e, he, hea⟩ := first_failed_longest_has_endpoint positive hf hC
  have heG := Finset.mem_product.mp (hR (hCR he))
  have ha : a ≤ N := by simpa only [hea] using (Finset.mem_Icc.mp heG.1).2
  exact row_branch_rank_lt hm hc hCR (fun e he => (Finset.mem_filter.mp (hsub he)).2)
    (failed_longest_chain_guard ha positive hf.1 hC) (branch_subset_grid hR hCR hb)
    (grid_sum_bound N K) hb


/-- The same relation allows either orientation; row priority is a subrelation. -/
def Reduction (N K : ℕ) (R Q : Edges) : Prop :=
  RowReduction N R Q ∨ RowReduction K (transpose R) (transpose Q)

theorem transpose_subset_grid {R : Edges} {N K : ℕ} (hR : R ⊆ grid N K) :
    transpose R ⊆ grid K N := by
  rw [← transpose_grid]
  exact Finset.map_subset_map.mpr hR

theorem reduction_closed {R Q : Edges} {N K : ℕ}
    (hR : R ⊆ grid N K) (h : Reduction N K R Q) : IsMatching Q ∧ Q ⊆ grid N K := by
  rcases h with h | h
  · exact rowReduction_closed hR h
  · have hs := rowReduction_closed (transpose_subset_grid hR) h
    refine ⟨(matching_transpose Q).mp hs.1, ?_⟩
    simpa only [transpose_transpose] using transpose_subset_grid hs.2

theorem reduction_rank_lt {R Q : Edges} {N K : ℕ}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (h : Reduction N K R Q) :
    rank (grid N K) (N + K) Q < rank (grid N K) (N + K) R := by
  rcases h with h | h
  · exact rowReduction_rank_lt hm hR h
  · have hlt := rowReduction_rank_lt ((matching_transpose R).mpr hm) (transpose_subset_grid hR) h
    rw [← transpose_grid N K, Nat.add_comm K N, rank_transpose, rank_transpose] at hlt
    exact hlt

abbrev MatchingState (N K : ℕ) := {R : Edges // IsMatching R ∧ R ⊆ grid N K}

/-- Termination is proved by an explicit natural-number rank, not assumed. -/
theorem reduction_wellFounded (N K : ℕ) :
    WellFounded (fun Q R : MatchingState N K => Reduction N K R.val Q.val) := by
  apply (measure (fun R : MatchingState N K => rank (grid N K) (N+K) R.val)).wf.mono
  intro Q R h
  exact reduction_rank_lt R.property.1 R.property.2 h

/-- Actual branch selected by the row-priority and lexicographic rule from Cycle037. -/
def ChosenBranch (N K : ℕ) (R Q : Edges) (z : ℤ) : Prop :=
  match chosenRewrite R with
  | .row a C => Branch (R \ C) C (freeBefore (Finset.Icc 1 N) R a)
      (targetRows (Finset.Icc 1 N) R C a) Q z
  | .column a C => ColumnBranch (R \ C) C (freeBefore (Finset.Icc 1 K) (transpose R) a)
      (targetRows (Finset.Icc 1 K) (transpose R) (transpose C) a) Q z
  | .terminal => False

theorem transpose_sdiff (R C : Edges) : transpose (R \ C) = transpose R \ transpose C :=
  Finset.map_sdiff _ _

/-- Direct adapter from the defined deterministic selector to the proved reduction relation. -/
theorem chosenBranch_is_reduction {R Q : Edges} {N K : ℕ} {z : ℤ}
    (hb : ChosenBranch N K R Q z) : Reduction N K R Q := by
  unfold ChosenBranch chosenRewrite at hb
  split_ifs at hb with hr hc
  · exact Or.inl ⟨_, _, z, min_row_failure_is_first R hr, (chosenLongest_spec _).1, hb⟩
  · apply Or.inr
    let a := (columnFailures R).min' hc
    refine ⟨a, chosenLongest (rowPrefix (transpose R) a), z, ?_, (chosenLongest_spec _).1, ?_⟩
    · exact (firstColumnAt_iff R a).mp (min_column_failure_is_first R hc)
    · simpa only [ColumnBranch, chosenColumnChain, transpose_transpose, transpose_sdiff] using hb
  · exact hb.elim

theorem chosenBranch_closed {R Q : Edges} {N K : ℕ} {z : ℤ}
    (hR : R ⊆ grid N K) (hb : ChosenBranch N K R Q z) :
    IsMatching Q ∧ Q ⊆ grid N K := reduction_closed hR (chosenBranch_is_reduction hb)

theorem chosenBranch_rank_lt {R Q : Edges} {N K : ℕ} {z : ℤ}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hb : ChosenBranch N K R Q z) :
    rank (grid N K) (N+K) Q < rank (grid N K) (N+K) R :=
  reduction_rank_lt hm hR (chosenBranch_is_reduction hb)

theorem chosenBranch_wellFounded (N K : ℕ) :
    WellFounded (fun Q R : MatchingState N K => ∃ z, ChosenBranch N K R.val Q.val z) := by
  apply (reduction_wellFounded N K).mono
  intro Q R h
  obtain ⟨z, hz⟩ := h
  exact chosenBranch_is_reduction hz


/-- A genuine same-degree row branch, strictly moving the matched row. -/
theorem row_upper_nonvacuous : RowReduction 2 {(1, 1)} {(2, 1)} := by
  refine ⟨1, {(1,1)}, -1, ?_, ?_, ?_⟩
  · constructor
    · decide
    · intro b hb
      have hb0 : b = 0 := by omega
      subst b
      decide
  · decide
  · refine ⟨{(2,1)}, Or.inr ?_, ?_, ?_⟩ <;> decide

/-- The transposed same-degree step is also an actual first-failure rewrite. -/
theorem column_upper_nonvacuous : Reduction 2 2 {(2, 1)} {(2, 2)} := by
  apply Or.inr
  refine ⟨1, {(1,2)}, -1, ?_, ?_, ?_⟩
  · constructor
    · decide
    · intro b hb
      have hb0 : b = 0 := by omega
      subst b
      decide
  · decide
  · refine ⟨{(2,2)}, Or.inr ?_, ?_, ?_⟩ <;> decide

theorem degree_drop_nonvacuous : RowReduction 2 {(1, 1)} ∅ := by
  refine ⟨1, {(1,1)}, 1, ?_, ?_, ?_⟩
  · constructor
    · decide
    · intro b hb
      have hb0 : b = 0 := by omega
      subst b
      decide
  · decide
  · refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide

theorem nonvacuous_ranks :
    rank (grid 2 2) 4 {(2,2)} < rank (grid 2 2) 4 {(2,1)} ∧
    rank (grid 2 2) 4 {(2,1)} < rank (grid 2 2) 4 {(1,1)} ∧
    rank (grid 2 2) 4 ∅ < rank (grid 2 2) 4 {(1,1)} := by decide

/-- Merely preserving degree does not imply termination: the increasing-chain condition matters. -/
theorem nonchain_reverses_domination :
    ¬ IsChain {(1,2), (2,1)} ∧
    UpperTerm {(1,2), (2,1)} {1,2} {(1,1), (2,2)} (-1) ∧
    rank (grid 2 2) 4 {(1,2), (2,1)} < rank (grid 2 2) 4 {(1,1), (2,2)} := by decide


theorem chosen_singleton_example : chosenRewrite {(1,1)} = .row 1 {(1,1)} := by
  have hf : rowFailures {(1,1)} = {1} := by decide
  have hp : rowPrefix {(1,1)} 1 = {(1,1)} := by decide
  have hc : chosenLongest {(1,1)} = {(1,1)} := by
    apply chosenLongest_unique
    · decide
    · intro D hD
      have hl : longestChains {(1,1)} = {{(1,1)}} := by decide
      rw [hl] at hD
      have hD' := Finset.mem_singleton.mp hD
      subst D
      exact le_refl _
  unfold chosenRewrite
  simp only [hf, Finset.singleton_nonempty, ↓reduceDIte, Finset.min'_singleton]
  rw [hp, hc]

theorem actual_chosen_upper_nonvacuous : ChosenBranch 2 2 {(1,1)} {(2,1)} (-1) := by
  rw [ChosenBranch, chosen_singleton_example]
  refine ⟨{(2,1)}, Or.inr ?_, ?_, ?_⟩ <;> decide

theorem actual_chosen_lower_nonvacuous : ChosenBranch 2 2 {(1,1)} ∅ 1 := by
  rw [ChosenBranch, chosen_singleton_example]
  refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide


/-- An actual infinite sequence of selected signed rewrites from a valid rectangle is impossible. -/
theorem no_infinite_chosen_run (N K : ℕ) (run : ℕ → Edges)
    (hm : IsMatching (run 0)) (hG : run 0 ⊆ grid N K)
    (hstep : ∀ t, ∃ z, ChosenBranch N K (run t) (run (t+1)) z) : False := by
  have hvalid : ∀ t, IsMatching (run t) ∧ run t ⊆ grid N K := by
    intro t
    induction t with
    | zero => exact ⟨hm, hG⟩
    | succ t ih =>
      obtain ⟨z, hz⟩ := hstep t
      exact chosenBranch_closed ih.2 hz
  have hdecrease : ∀ t, rank (grid N K) (N+K) (run (t+1)) < rank (grid N K) (N+K) (run t) := by
    intro t
    obtain ⟨z, hz⟩ := hstep t
    exact chosenBranch_rank_lt (hvalid t).1 (hvalid t).2 hz
  have hbound : ∀ t, rank (grid N K) (N+K) (run t) + t ≤ rank (grid N K) (N+K) (run 0) := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      have ht := hdecrease t
      omega
  have hbad := hbound (rank (grid N K) (N+K) (run 0) + 1)
  omega

end SelfContainedCycle038
