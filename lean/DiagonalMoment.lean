import ExactBlockMoments
import Mathlib.Algebra.CharP.Two

namespace SelfContainedCycle050
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle045 SelfContainedCycle046
open SelfContainedCycle047 SelfContainedCycle048 SelfContainedCycle049

/-- The unique edge at an occupied row exists from the actual finite support. -/
theorem exists_edge_at_row (M : Edges) (i : rows M) : ∃ j, ((i:ℕ),j) ∈ M := by
  obtain ⟨e,he,hi⟩ := Finset.mem_image.mp i.property
  exact ⟨e.2,by simpa only [← hi] using he⟩

noncomputable def matchingImage (M : Edges) (i : rows M) : cols M :=
  ⟨Classical.choose (exists_edge_at_row M i),
    Finset.mem_image.mpr ⟨_,Classical.choose_spec (exists_edge_at_row M i),rfl⟩⟩

theorem matchingImage_mem (M : Edges) (i : rows M) :
    ((i:ℕ),(matchingImage M i:ℕ)) ∈ M :=
  Classical.choose_spec (exists_edge_at_row M i)

theorem matchingImage_at_edge {M : Edges} (hm : IsMatching M) {e : ℕ × ℕ} (he : e ∈ M) :
    (matchingImage M ⟨e.1,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩:ℕ) = e.2 := by
  exact congrArg Prod.snd (hm _ (matchingImage_mem M _) e he (Or.inl rfl))

theorem matchingImage_bijective {M : Edges} (hm : IsMatching M) :
    Function.Bijective (matchingImage M) := by
  constructor
  · intro i j hij
    apply Subtype.ext
    exact congrArg Prod.fst (hm _ (matchingImage_mem M i) _ (matchingImage_mem M j)
      (Or.inr (congrArg Subtype.val hij)))
  · intro j
    obtain ⟨e,he,hj⟩ := Finset.mem_image.mp j.property
    refine ⟨⟨e.1,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩,Subtype.ext ?_⟩
    exact (matchingImage_at_edge hm he).trans hj

/-- A matching gives a genuine equivalence of its occupied rows and columns. -/
noncomputable def matchingEquiv (M : Edges) (hm : IsMatching M) : rows M ≃ cols M :=
  Equiv.ofBijective (matchingImage M) (matchingImage_bijective hm)

theorem matchingEquiv_graph (M : Edges) (hm : IsMatching M) :
    bijectionGraph (matchingEquiv M hm) = M := by
  ext e
  constructor
  · intro he
    obtain ⟨i,rfl⟩ := (mem_bijectionGraph _ _).mp he
    exact matchingImage_mem M i
  · intro he
    apply (mem_bijectionGraph _ _).mpr
    refine ⟨⟨e.1,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩,Prod.ext rfl ?_⟩
    exact matchingImage_at_edge hm he

noncomputable def supportedEquiv (M : Edges) (hm : IsMatching M) (A B : Finset ℕ)
    (hr : rows M = A) (hc : cols M = B) : A ≃ B := by
  subst A; subst B
  exact matchingEquiv M hm

theorem supportedEquiv_graph (M : Edges) (hm : IsMatching M) (A B : Finset ℕ)
    (hr : rows M = A) (hc : cols M = B) :
    bijectionGraph (supportedEquiv M hm A B hr hc) = M := by
  subst A; subst B
  exact matchingEquiv_graph M hm

section Actual
variable {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal)

/-- Complete each level by its actual unused anchor pair. -/
def diagonalBlock (t : Fin (chainHeight R)) : Edges :=
  insert (rowAnchor hm hR ht t,colAnchor hm hR ht t) (heightLevel R (t.val+1))

theorem diagonalBlock_matching (t : Fin (chainHeight R)) :
    IsMatching (diagonalBlock hm hR ht t) := by
  intro e he f hf h
  rcases Finset.mem_insert.mp he with he | he
  · subst e
    rcases Finset.mem_insert.mp hf with hf | hf
    · exact hf.symm
    · rcases h with h | h
      · dsimp only at h
        exact (rowAnchor_not_level hm hR ht t (t.val+1)
          (h.symm ▸ Finset.mem_image.mpr ⟨f,hf,rfl⟩)).elim
      · dsimp only at h
        exact (colAnchor_not_level hm hR ht t (t.val+1)
          (h.symm ▸ Finset.mem_image.mpr ⟨f,hf,rfl⟩)).elim
  · rcases Finset.mem_insert.mp hf with hf | hf
    · subst f
      rcases h with h | h
      · dsimp only at h
        exact (rowAnchor_not_level hm hR ht t (t.val+1)
          (h ▸ Finset.mem_image.mpr ⟨e,he,rfl⟩)).elim
      · dsimp only at h
        exact (colAnchor_not_level hm hR ht t (t.val+1)
          (h ▸ Finset.mem_image.mpr ⟨e,he,rfl⟩)).elim
    · exact level_matching hm _ e he f hf h

theorem diagonalBlock_rows (t : Fin (chainHeight R)) :
    rows (diagonalBlock hm hR ht t) = rowBlock hm hR ht t := by
  simp [diagonalBlock,rows,rowBlock]

theorem diagonalBlock_cols (t : Fin (chainHeight R)) :
    cols (diagonalBlock hm hR ht t) = colBlock hm hR ht t := by
  simp [diagonalBlock,cols,colBlock]

noncomputable def diagonalEquiv (t : Fin (chainHeight R)) :
    rowBlock hm hR ht t ≃ colBlock hm hR ht t :=
  supportedEquiv (diagonalBlock hm hR ht t) (diagonalBlock_matching hm hR ht t)
    _ _ (diagonalBlock_rows hm hR ht t) (diagonalBlock_cols hm hR ht t)

theorem diagonalEquiv_graph (t : Fin (chainHeight R)) :
    bijectionGraph (diagonalEquiv hm hR ht t) = diagonalBlock hm hR ht t :=
  supportedEquiv_graph _ _ _ _ _ _

noncomputable def diagonalChoice : Choices hm hR ht := fun t =>
  (diagonalEquiv hm hR ht t).trans (baseBlock hm hR ht t).symm

theorem diagonalChoice_compatibility (t : Fin (chainHeight R)) (i : rowBlock hm hR ht t) :
    baseBlock hm hR ht t (diagonalChoice hm hR ht t i) = diagonalEquiv hm hR ht t i := by
  simp [diagonalChoice,Equiv.trans_apply]


/-- The actual globally assembled diagonal choice contains every edge of R. -/
theorem diagonalChoice_contains : R ⊆ blockPermutation hm hR ht (diagonalChoice hm hR ht) := by
  intro e he
  have hl : e ∈ Finset.univ.biUnion (fun t : Fin (chainHeight R) => heightLevel R (t.val+1)) := by
    rw [levels_cover]; exact he
  obtain ⟨t,_,het⟩ := Finset.mem_biUnion.mp hl
  have hi : e.1 ∈ rowBlock hm hR ht t :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e,het,rfl⟩)
  apply (blockPermutation_at_block hm hR ht _ t ⟨e.1,hi⟩ e.2).mpr
  rw [diagonalChoice_compatibility]
  apply (graph_pair_mem (diagonalEquiv hm hR ht t) ⟨e.1,hi⟩ e.2).mp
  rw [diagonalEquiv_graph]
  exact Finset.mem_insert_of_mem het

/-- The sole row of an actual block unused by R is its anchor. -/
theorem rowBlock_sdiff_rows (t : Fin (chainHeight R)) :
    rowBlock hm hR ht t \ rows R = {rowAnchor hm hR ht t} := by
  ext i
  simp only [Finset.mem_sdiff,rowBlock,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hi,hn⟩
    rcases hi with h | h
    · exact h
    · exact (hn (Finset.image_subset_image (Finset.filter_subset _ _) h)).elim
  · intro hi
    subst i
    exact ⟨Or.inl rfl,(Finset.mem_sdiff.mp (rowAnchor_mem hm hR ht t)).2⟩

theorem colBlock_sdiff_cols (t : Fin (chainHeight R)) :
    colBlock hm hR ht t \ cols R = {colAnchor hm hR ht t} := by
  ext i
  simp only [Finset.mem_sdiff,colBlock,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hi,hn⟩
    rcases hi with h | h
    · exact h
    · exact (hn (Finset.image_subset_image (Finset.filter_subset _ _) h)).elim
  · intro hi
    subst i
    exact ⟨Or.inl rfl,(Finset.mem_sdiff.mp (colAnchor_mem hm hR ht t)).2⟩

theorem diagonalChoice_unique (σ : Choices hm hR ht)
    (hσ : R ⊆ blockPermutation hm hR ht σ) : σ = diagonalChoice hm hR ht := by
  apply choices_eq_of_containing hm hR ht R _ σ _ hσ (diagonalChoice_contains hm hR ht)
  intro t
  rw [rowBlock_sdiff_rows]
  simp

/-- The diagonal is an actual single sign contribution, with no nonzero premise. -/
theorem diagonal_moment_eq_weight :
    blockMoment hm hR ht R = blockWeight hm hR ht (diagonalChoice hm hR ht) :=
  moment_eq_weight_of_unique hm hR ht R _ (diagonalChoice_contains hm hR ht)
    (diagonalChoice_unique hm hR ht)

theorem diagonal_moment_isUnit : IsUnit (blockMoment hm hR ht R) := by
  rw [diagonal_moment_eq_weight]
  exact blockWeight_isUnit hm hR ht _

theorem diagonal_moment_nonzero : blockMoment hm hR ht R ≠ 0 := by
  rw [diagonal_moment_eq_weight]
  exact blockWeight_nonzero hm hR ht _

theorem diagonal_moment_sign : blockMoment hm hR ht R = 1 ∨ blockMoment hm hR ht R = -1 :=
  Int.isUnit_iff.mp (diagonal_moment_isUnit hm hR ht)

/-- In every nontrivial characteristic, the actual diagonal remains nonzero. -/
theorem diagonal_moment_cast_nonzero {F : Type*} [CommRing F] [Nontrivial F] :
    (blockMoment hm hR ht R : F) ≠ 0 := by
  rcases diagonal_moment_sign hm hR ht with h | h
  · simp [h]
  · simp [h]


/-- The selected local bijection really is the completed level bijection. -/
theorem diagonal_selectedBijection (t : Fin (chainHeight R)) :
    selectedBijection hm hR ht (diagonalChoice hm hR ht) (some t) = diagonalEquiv hm hR ht t := by
  apply Equiv.ext
  intro i
  exact diagonalChoice_compatibility hm hR ht t i

/-- Exact global graph, including the same fixed complementary bijection as Cycle048. -/
theorem diagonal_global_graph :
    blockPermutation hm hR ht (diagonalChoice hm hR ht) =
      bijectionGraph (orderedBijection _ _ (complements_card_eq hm hR ht)) ∪
        Finset.univ.biUnion (diagonalBlock hm hR ht) := by
  ext e
  rw [blockPermutation,mem_joinGraphs]
  constructor
  · rintro ⟨t,he⟩
    cases t with
    | none => exact Finset.mem_union_left _ he
    | some t =>
      rw [diagonal_selectedBijection,diagonalEquiv_graph] at he
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,he⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · exact ⟨none,he⟩
    · obtain ⟨t,_,het⟩ := Finset.mem_biUnion.mp he
      refine ⟨some t,?_⟩
      rw [diagonal_selectedBijection,diagonalEquiv_graph]
      exact het

/-- Anchors have the specified partners in the actual global permutation. -/
theorem diagonal_anchor_mem (t : Fin (chainHeight R)) :
    (rowAnchor hm hR ht t,colAnchor hm hR ht t) ∈
      blockPermutation hm hR ht (diagonalChoice hm hR ht) := by
  rw [diagonal_global_graph]
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨t,Finset.mem_univ _,Finset.mem_insert_self _ _⟩)

theorem diagonal_moment_cast_isUnit {F : Type*} [CommRing F] :
    IsUnit (blockMoment hm hR ht R : F) := by
  exact (diagonal_moment_isUnit hm hR ht).map (Int.castRingHom F)

/-- Integral signs survive characteristic two and give an exact unit diagonal. -/
theorem diagonal_moment_char_two {F : Type*} [CommRing F] [CharP F 2] :
    (blockMoment hm hR ht R : F) = 1 := by
  rcases diagonal_moment_sign hm hR ht with h | h
  · simp [h]
  · simp [h,CharTwo.neg_eq]

end Actual

/-- Actual multi-level diagonal graphs, with the non-identical complementary labels retained. -/
theorem example_diagonal_blocks :
    diagonalBlock example_matching example_grid example_terminal ⟨0,by decide⟩ =
      {(1,1),(3,5),(4,3)} ∧
    diagonalBlock example_matching example_grid example_terminal ⟨1,by decide⟩ =
      {(2,2),(6,6)} := by
  simp only [diagonalBlock,example_anchors.1,example_anchors.2.1,
    example_anchors.2.2.1,example_anchors.2.2.2,example_levels.2.1,example_levels.2.2]
  decide

/-- The example keeps its actual unequal-label complementary edge. -/
theorem example_complement_edge :
    (5,4) ∈ blockPermutation example_matching example_grid example_terminal
      (diagonalChoice example_matching example_grid example_terminal) := by
  have hi : 5 ∈ rowPart example_matching example_grid example_terminal none := by
    change 5 ∈ Finset.Icc 1 6 \ Finset.univ.biUnion
      (rowBlock example_matching example_grid example_terminal)
    rw [example_complements.1]
    decide
  apply (blockPermutation_at_complement example_matching example_grid example_terminal
    _ ⟨5,hi⟩ 4).mpr
  have hj := (orderedBijection _ _ (complements_card_eq example_matching example_grid example_terminal)
    ⟨5,hi⟩).property
  exact Finset.mem_singleton.mp ((Finset.ext_iff.mp example_complements.2 _).mp hj)

/-- The assembled six-edge permutation is identified exactly, not just by cardinality. -/
theorem example_global_graph :
    blockPermutation example_matching example_grid example_terminal
      (diagonalChoice example_matching example_grid example_terminal) =
      {(1,1),(2,2),(3,5),(4,3),(5,4),(6,6)} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    have ha := diagonal_anchor_mem example_matching example_grid example_terminal ⟨0,by decide⟩
    have hb := diagonal_anchor_mem example_matching example_grid example_terminal ⟨1,by decide⟩
    simp only [example_anchors.1,example_anchors.2.2.1] at ha
    simp only [example_anchors.2.1,example_anchors.2.2.2] at hb
    exact ⟨ha,hb,diagonalChoice_contains _ _ _ (by decide),
      diagonalChoice_contains _ _ _ (by decide),example_complement_edge,
      diagonalChoice_contains _ _ _ (by decide)⟩
  · rw [blockPermutation_card]
    decide

/-- The example's true degree-three moment, not its degree-six full permutation moment. -/
theorem example_diagonal_nonvacuity :
    IsUnit (blockMoment example_matching example_grid example_terminal exampleMatching) ∧
    (blockMoment example_matching example_grid example_terminal exampleMatching : ZMod 2) = 1 ∧
    blockMoment example_matching example_grid example_terminal ∅ = 0 := by
  refine ⟨diagonal_moment_isUnit _ _ _,diagonal_moment_char_two _ _ _,?_⟩
  exact blockMoment_below_degree _ _ _ ∅ (by decide)

/-- A closed nonempty one-level instance also meets the real terminality premises. -/
theorem singleton_diagonal_nonvacuity :
    ∃ (hm : IsMatching {(2,2)}) (hR : {(2,2)} ⊆ grid 2 2)
      (ht : chosenRewrite {(2,2)} = .terminal),
      (blockMoment hm hR ht {(2,2)} : ZMod 2) = 1 ∧ blockMoment hm hR ht ∅ = 0 := by
  refine ⟨by decide,by decide,by decide,diagonal_moment_char_two _ _ _,?_⟩
  exact blockMoment_below_degree _ _ _ ∅ (by decide)

/-- The empty input has an actual unit diagonal too, in every square. -/
theorem empty_diagonal_nonvacuity (N : ℕ) :
    IsUnit (blockMoment (N:=N) (R:=∅) (by simp [IsMatching])
      (Finset.empty_subset _) empty_terminal ∅) := diagonal_moment_isUnit _ _ _

end SelfContainedCycle050
