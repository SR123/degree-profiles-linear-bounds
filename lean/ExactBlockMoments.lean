import BlockPermutations

namespace SelfContainedCycle049
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle045 SelfContainedCycle047 SelfContainedCycle048

/-- A bijection is determined by its values away from one point. -/
theorem equiv_eq_of_agree_except_one {A B : Type*} (f g : A ≃ B) (a : A)
    (h : ∀ i, i ≠ a → f i = g i) : f = g := by
  apply Equiv.ext
  intro i
  by_cases hi : i=a
  · subst i
    let j := f.symm (g a)
    have hj : f j = g a := f.apply_symm_apply (g a)
    by_cases hja : j=a
    · simpa only [hja] using hj
    · have he := (h j hja).symm.trans hj
      exact (hja (g.injective he)).elim
  · exact h i hi

/-- At most one unused domain label suffices to recover a finite bijection. -/
theorem equiv_eq_of_agree_used {A B : Finset ℕ} (f g : A ≃ B) (U : Finset ℕ)
    (hcard : (A \ U).card ≤ 1) (h : ∀ i : A, (i:ℕ) ∈ U → f i = g i) : f=g := by
  classical
  by_cases ha : (A \ U).Nonempty
  · obtain ⟨a,ha⟩ := ha
    have hamem := (Finset.mem_sdiff.mp ha).1
    apply equiv_eq_of_agree_except_one f g ⟨a,hamem⟩
    intro i hi
    apply h
    by_contra hin
    have hieq : (i:ℕ)=a := Finset.card_le_one.mp hcard
      (i:ℕ) (Finset.mem_sdiff.mpr ⟨i.property,hin⟩) a ha
    exact hi (Subtype.ext hieq)
  · apply Equiv.ext
    intro i
    apply h
    by_contra hin
    exact ha ⟨i,Finset.mem_sdiff.mpr ⟨i.property,hin⟩⟩

section Actual
variable {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal)

/-- A nonzero actual finite signed sum has a genuine containing permutation. -/
theorem containing_choice_of_nonzero (P : Edges) (hv : blockMoment hm hR ht P ≠ 0) :
    ∃ σ : Choices hm hR ht, P ⊆ blockPermutation hm hR ht σ := by
  obtain ⟨σ,_,hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have he := (mul_ne_zero_iff.mp hσ).2
  by_cases hs : P ⊆ blockPermutation hm hR ht σ
  · exact ⟨σ,hs⟩
  · simp [permutationEval,hs] at he

theorem matching_grid_of_nonzero (P : Edges) (hv : blockMoment hm hR ht P ≠ 0) :
    IsMatching P ∧ P ⊆ grid N N := by
  obtain ⟨σ,hσ⟩ := containing_choice_of_nonzero hm hR ht P hv
  exact ⟨matching_subset (blockPermutation_matching hm hR ht σ) hσ,
    hσ.trans (blockPermutation_grid hm hR ht σ)⟩

/-- Nonzero moments leave at most one unused row in every actual block. -/
theorem unused_card_le_one_of_nonzero (P : Edges) (hv : blockMoment hm hR ht P ≠ 0)
    (t : Fin (chainHeight R)) : (rowBlock hm hR ht t \ rows P).card ≤ 1 := by
  by_contra hn
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < (rowBlock hm hR ht t \ rows P).card by omega)
  have ha' := Finset.mem_sdiff.mp ha
  have hb' := Finset.mem_sdiff.mp hb
  exact hv (blockMoment_zero_of_two_unused hm hR ht t ⟨a,ha'.1⟩ ⟨b,hb'.1⟩
    (fun h => hab (congrArg Subtype.val h)) P ha'.2 hb'.2)

/-- Exact recovery uses real assigned edges and the one-unused-row bound. -/
theorem choices_eq_of_containing (P : Edges)
    (hcard : ∀ t, (rowBlock hm hR ht t \ rows P).card ≤ 1)
    (σ τ : Choices hm hR ht) (hσ : P ⊆ blockPermutation hm hR ht σ)
    (hτ : P ⊆ blockPermutation hm hR ht τ) : σ=τ := by
  funext t
  apply equiv_eq_of_agree_used (σ t) (τ t) (rows P) (hcard t)
  intro i hi
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hi
  have hpair : ((i:ℕ),e.2) ∈ P := by simpa only [← hei] using he
  have hs := (blockPermutation_at_block hm hR ht σ t i e.2).mp (hσ hpair)
  have hu := (blockPermutation_at_block hm hR ht τ t i e.2).mp (hτ hpair)
  apply (baseBlock hm hR ht t).injective
  exact Subtype.ext (hs.trans hu.symm)

/-- A unique containing choice contributes exactly once, with its actual sign. -/
theorem moment_eq_weight_of_unique (P : Edges) (σ : Choices hm hR ht)
    (hσ : P ⊆ blockPermutation hm hR ht σ)
    (hu : ∀ τ : Choices hm hR ht, P ⊆ blockPermutation hm hR ht τ → τ=σ) :
    blockMoment hm hR ht P = blockWeight hm hR ht σ := by
  classical
  unfold blockMoment
  rw [Finset.sum_eq_single σ]
  · simp [permutationEval,hσ]
  · intro τ _ hτ
    have hn : ¬ P ⊆ blockPermutation hm hR ht τ := fun h => hτ (hu τ h)
    simp [permutationEval,hn]
  · intro hn; exact (hn (Finset.mem_univ _)).elim

theorem unique_choice_of_nonzero (P : Edges) (hv : blockMoment hm hR ht P ≠ 0) :
    ∃! σ : Choices hm hR ht, P ⊆ blockPermutation hm hR ht σ := by
  obtain ⟨σ,hσ⟩ := containing_choice_of_nonzero hm hR ht P hv
  exact ⟨σ,hσ,fun τ hτ => choices_eq_of_containing hm hR ht P
    (unused_card_le_one_of_nonzero hm hR ht P hv) τ σ hτ hσ⟩

theorem blockWeight_isUnit (σ : Choices hm hR ht) : IsUnit (blockWeight hm hR ht σ) := by
  unfold blockWeight
  refine ⟨∏ t, Equiv.Perm.sign (σ t), ?_⟩
  simp

/-- All nonzero moments are integer units; this includes but does not assume degree r. -/
theorem nonzero_moment_isUnit (P : Edges) (hv : blockMoment hm hR ht P ≠ 0) :
    IsUnit (blockMoment hm hR ht P) := by
  obtain ⟨σ,hσ,hu⟩ := unique_choice_of_nonzero hm hR ht P hv
  rw [moment_eq_weight_of_unique hm hR ht P σ hσ hu]
  exact blockWeight_isUnit hm hR ht σ

theorem nonzero_iff_unique_choice (P : Edges) : blockMoment hm hR ht P ≠ 0 ↔
    ∃! σ : Choices hm hR ht, P ⊆ blockPermutation hm hR ht σ := by
  constructor
  · exact unique_choice_of_nonzero hm hR ht P
  · rintro ⟨σ,hσ,hu⟩
    rw [moment_eq_weight_of_unique hm hR ht P σ hσ hu]
    exact blockWeight_nonzero hm hR ht σ

/-- A nonzero signed block moment has precisely one signed contribution. -/
theorem moment_zero_or_one_or_neg_one (P : Edges) :
    blockMoment hm hR ht P = 0 ∨ blockMoment hm hR ht P = 1 ∨
      blockMoment hm hR ht P = -1 := by
  by_cases hv : blockMoment hm hR ht P = 0
  · exact Or.inl hv
  · exact Or.inr (Int.isUnit_iff.mp (nonzero_moment_isUnit hm hR ht P hv))

/-- Occupied row sets in different actual blocks are disjoint. -/
theorem occupied_blocks_disjoint (P : Edges) :
    ((Finset.univ : Finset (Fin (chainHeight R))) : Set (Fin (chainHeight R))).PairwiseDisjoint
      (fun t => rowBlock hm hR ht t ∩ rows P) := by
  intro s _ t _ hst
  exact (rowBlocks_disjoint hm hR ht hst).mono Finset.inter_subset_left Finset.inter_subset_left

theorem occupied_union_subset (P : Edges) :
    Finset.univ.biUnion (fun t => rowBlock hm hR ht t ∩ rows P) ⊆ rows P := by
  intro i hi
  obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hi
  exact (Finset.mem_inter.mp hit).2

theorem occupied_sum_le (P : Edges) :
    (∑ t : Fin (chainHeight R), (rowBlock hm hR ht t ∩ rows P).card) ≤ P.card := by
  rw [← Finset.card_biUnion (occupied_blocks_disjoint hm hR ht P)]
  exact (Finset.card_le_card (occupied_union_subset hm hR ht P)).trans
    (Finset.card_image_le (s:=P) (f:=Prod.fst))

theorem occupied_card_ge_of_nonzero (P : Edges) (hv : blockMoment hm hR ht P ≠ 0)
    (t : Fin (chainHeight R)) :
    (heightLevel R (t.val+1)).card ≤ (rowBlock hm hR ht t ∩ rows P).card := by
  have hc := Finset.card_sdiff_add_card_inter (rowBlock hm hR ht t) (rows P)
  rw [rowBlock_card] at hc
  have h := unused_card_le_one_of_nonzero hm hR ht P hv t
  omega

/-- In exact degree |R| every block has exactly its level's number of occupied rows. -/
theorem exact_degree_occupied_card (P : Edges) (hc : P.card = R.card)
    (hv : blockMoment hm hR ht P ≠ 0) (t : Fin (chainHeight R)) :
    (rowBlock hm hR ht t ∩ rows P).card = (heightLevel R (t.val+1)).card := by
  have hle := occupied_card_ge_of_nonzero hm hR ht P hv
  have hs : (∑ s : Fin (chainHeight R), (heightLevel R (s.val+1)).card) =
      ∑ s : Fin (chainHeight R), (rowBlock hm hR ht s ∩ rows P).card := by
    apply le_antisymm
    · exact Finset.sum_le_sum (fun s _ => hle s)
    · rw [levels_total_card]
      exact hc ▸ occupied_sum_le hm hR ht P
  exact ((Finset.sum_eq_sum_iff_of_le (fun s _ => hle s)).mp hs t (Finset.mem_univ t)).symm

/-- At exact degree no occupied row lies in the fixed complementary part. -/
theorem exact_degree_rows_covered (P : Edges) (hc : P.card = R.card)
    (hv : blockMoment hm hR ht P ≠ 0) :
    Finset.univ.biUnion (fun t => rowBlock hm hR ht t ∩ rows P) = rows P := by
  apply Finset.eq_of_subset_of_card_le (occupied_union_subset hm hR ht P)
  rw [Finset.card_biUnion (occupied_blocks_disjoint hm hR ht P)]
  simp_rw [exact_degree_occupied_card hm hR ht P hc hv]
  rw [levels_total_card, matching_rows_card (matching_grid_of_nonzero hm hR ht P hv).1,hc]

/-- Exact-degree support lies in the paired blocks, with no complementary edge. -/
theorem exact_degree_edge_support (P : Edges) (hc : P.card = R.card)
    (hv : blockMoment hm hR ht P ≠ 0) {e : ℕ × ℕ} (he : e ∈ P) :
    ∃ t : Fin (chainHeight R), e.1 ∈ rowBlock hm hR ht t ∧ e.2 ∈ colBlock hm hR ht t := by
  have hr : e.1 ∈ rows P := Finset.mem_image.mpr ⟨e,he,rfl⟩
  rw [← exact_degree_rows_covered hm hR ht P hc hv] at hr
  obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hr
  have hi := (Finset.mem_inter.mp hit).1
  obtain ⟨σ,hσ⟩ := containing_choice_of_nonzero hm hR ht P hv
  have hj := (blockPermutation_at_block hm hR ht σ t ⟨e.1,hi⟩ e.2).mp (hσ he)
  refine ⟨t,hi,?_⟩
  rw [← hj]
  exact (baseBlock hm hR ht t (σ t ⟨e.1,hi⟩)).property

/-- Each exact-degree block leaves exactly one row for its unique completion. -/
theorem exact_degree_one_unused (P : Edges) (hc : P.card = R.card)
    (hv : blockMoment hm hR ht P ≠ 0) (t : Fin (chainHeight R)) :
    (rowBlock hm hR ht t \ rows P).card = 1 := by
  have h := Finset.card_sdiff_add_card_inter (rowBlock hm hR ht t) (rows P)
  rw [rowBlock_card,exact_degree_occupied_card hm hR ht P hc hv] at h
  omega

/-- Non-vacuity of the equivalence and unit theorem for every actual terminal R. -/
theorem unique_choice_nonvacuity :
    ∃ P : Edges, (∃! σ : Choices hm hR ht, P ⊆ blockPermutation hm hR ht σ) ∧
      blockMoment hm hR ht P = 1 := by
  refine ⟨blockPermutation hm hR ht (identityChoice hm hR ht), ?_,
    blockMoment_identity_full hm hR ht⟩
  apply (nonzero_iff_unique_choice hm hR ht _).mp
  rw [blockMoment_identity_full]
  decide
end Actual

end SelfContainedCycle049
