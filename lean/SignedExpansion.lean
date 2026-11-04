import DesignRewrite

namespace SelfContainedCycle057
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037 SelfContainedCycle038
open SelfContainedCycle040 SelfContainedCycle045 SelfContainedCycle046 SelfContainedCycle053
open SelfContainedCycle055 SelfContainedCycle056

/-- Finite signed expansion, derived from the actual degree-bounded design recurrence. -/
theorem mixed_powerset_expansion {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (P : Edges) (T B X Y : Finset ℕ)
    (hT : T⊆Finset.Icc 1 n) (hB : B⊆Finset.Icc 1 n) (hTB : Disjoint T B)
    (hcover : ∀ i∈Finset.Icc 1 n, i∉rows P → i∈T∪B) (hP : P⊆grid n m)
    (hXY : Disjoint X Y) (hS : X∪Y ⊆ Finset.Icc 1 m)
    (hPC : Disjoint (cols P) (X∪Y)) (hd : P.card+(X∪Y).card≤d) :
    mixedSum ψ P (Finset.Icc 1 n) T B X Y =
      ∑ A ∈ X.powerset, (-1:F)^A.card * mixedSum ψ P (Finset.Icc 1 n) T B ∅ (Y∪A) := by
  classical
  induction X using Finset.induction_on generalizing Y with
  | empty => simp
  | @insert j X hjX ih =>
    obtain ⟨hjY,hXY0⟩ := Finset.disjoint_insert_left.mp hXY
    have hjS : j∉X∪Y := by simpa only [Finset.mem_union,not_or] using And.intro hjX hjY
    have hsub : X∪Y ⊆ insert j X∪Y := Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
    have hS0 := hsub.trans hS
    have hPC0 : Disjoint (cols P) (X∪Y) := Finset.disjoint_of_subset_right hsub hPC
    have hj : j∈Finset.Icc 1 m := hS (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
    have hjP : j∉cols P := fun h => Finset.disjoint_left.mp hPC h
      (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
    have hcard : (insert j X∪Y).card=(X∪Y).card+1 := by
      rw [Finset.insert_union,Finset.card_insert_of_notMem hjS]
    have hd0 : P.card+(X∪Y).card≤d := by omega
    have hstep := mixed_design_step hψ P T B X Y hT hB hTB hcover hP hS0 j hj hjS hjP (by omega)
    have hXY1 : Disjoint X (insert j Y) := Finset.disjoint_insert_right.mpr ⟨hjX,hXY0⟩
    have he : X∪insert j Y=insert j X∪Y := by rw [Finset.union_insert,Finset.insert_union]
    have h1 := ih Y hXY0 hS0 hPC0 hd0
    have h2 := ih (insert j Y) hXY1 (he.symm ▸ hS) (he.symm ▸ hPC) (he.symm ▸ hd)
    rw [eq_sub_of_add_eq hstep,h1,h2,Finset.sum_powerset_insert hjX]
    have hs : (∑ A ∈ X.powerset, (-1:F)^(insert j A).card *
        mixedSum ψ P (Finset.Icc 1 n) T B ∅ (Y∪insert j A)) =
        -(∑ A ∈ X.powerset, (-1:F)^A.card * mixedSum ψ P (Finset.Icc 1 n) T B ∅ (insert j Y∪A)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro A hA
      have hjA : j∉A := fun h => hjX (Finset.mem_powerset.mp hA h)
      rw [Finset.card_insert_of_notMem hjA,pow_succ,Finset.union_insert,Finset.insert_union]
      ring
    rw [hs,sub_eq_add_neg]


/-- A constant row mask gives precisely the full injection family. -/
theorem maskedTerms_rows (U S T : Finset ℕ) (hT : T⊆U) :
    maskedTerms U S (fun e => e.1∈T) = fullTerms S T := by
  classical
  ext M
  rw [mem_maskedTerms,mem_fullTerms]
  constructor
  · rintro ⟨hm,_,hc,ha⟩
    refine ⟨hm,?_,hc⟩
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact ha e he
  · rintro ⟨hm,hr,hc⟩
    exact ⟨hm,hr.trans hT,hc,fun e he => hr (Finset.mem_image.mpr ⟨e,he,rfl⟩)⟩

theorem mixedSum_left {F : Type*} [CommRing F] (ψ : Edges → F)
    (P : Edges) (U T B S : Finset ℕ) (hT : T⊆U) :
    mixedSum ψ P U T B S ∅ = ∑ M ∈ fullTerms S T, ψ (P∪M) := by
  classical
  unfold mixedSum
  simp only [Finset.union_empty]
  rw [maskedTerms_congr U S _ (fun e => e.1∈T) (by intros; simp_all),maskedTerms_rows U S T hT]

theorem mixedSum_right {F : Type*} [CommRing F] (ψ : Edges → F)
    (P : Edges) (U T B S : Finset ℕ) (hB : B⊆U) :
    mixedSum ψ P U T B ∅ S = ∑ M ∈ fullTerms S B, ψ (P∪M) := by
  classical
  unfold mixedSum
  simp only [Finset.empty_union,Finset.notMem_empty,ite_false]
  rw [maskedTerms_rows U S B hB]

/-- Fibers by covered columns, including the empty matching, have no multiplicity loss. -/
theorem lowerTerms_cols_fiber (S B A : Finset ℕ) (hA : A⊆S) :
    (lowerTerms S B).filter (fun M => cols M=A) = fullTerms A B := by
  ext M
  simp only [Finset.mem_filter,mem_lowerTerms,mem_fullTerms]
  constructor
  · rintro ⟨⟨hm,hr,_⟩,hc⟩; exact ⟨hm,hr,hc⟩
  · rintro ⟨hm,hr,hc⟩; exact ⟨⟨hm,hr,hc ▸ hA⟩,hc⟩

/-- Regroup the powerset expansion into the actual lower signed injection sum. -/
theorem lower_signed_fibers {F : Type*} [CommRing F] (ψ : Edges → F)
    (P : Edges) (S B : Finset ℕ) :
    (∑ A ∈ S.powerset, (-1:F)^A.card * ∑ M ∈ fullTerms A B, ψ (P∪M)) =
      ∑ M ∈ lowerTerms S B, (-1:F)^M.card * ψ (P∪M) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := cols)
    (s := lowerTerms S B) (t := S.powerset)
    (fun M hM => Finset.mem_powerset.mpr ((mem_lowerTerms _ _ _).mp hM).2.2)
    (fun M => (-1:F)^M.card * ψ (P∪M))]
  apply Finset.sum_congr rfl
  intro A hA
  rw [lowerTerms_cols_fiber S B A (Finset.mem_powerset.mp hA),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M hM
  obtain ⟨hm,_,hc⟩ := (mem_fullTerms _ _ _).mp hM
  rw [← matching_cols_card hm,hc]

/-- The full signed injection identity follows from design equations, over any commutative ring. -/
theorem design_inclusion_exclusion {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (P : Edges) (T B S : Finset ℕ)
    (hT : T⊆Finset.Icc 1 n) (hB : B⊆Finset.Icc 1 n) (hTB : Disjoint T B)
    (hcover : ∀ i∈Finset.Icc 1 n, i∉rows P → i∈T∪B) (hP : P⊆grid n m)
    (hS : S⊆Finset.Icc 1 m) (hPC : Disjoint (cols P) S) (hd : P.card+S.card≤d) :
    (∑ M ∈ fullTerms S T, ψ (P∪M)) =
      ∑ M ∈ lowerTerms S B, (-1:F)^M.card * ψ (P∪M) := by
  classical
  have h := mixed_powerset_expansion hψ P T B S ∅ hT hB hTB hcover hP
    (Finset.disjoint_empty_right _) (by simpa) (by simpa) (by simpa)
  simp only [Finset.empty_union,mixedSum_left ψ P _ T B S hT,
    mixedSum_right ψ P _ T B _ hB] at h
  exact h.trans (lower_signed_fibers ψ P S B)


/-- The actual row sets cover every row not used by the fixed complement. -/
theorem actual_design_cover {R C : Edges} (U : Finset ℕ) (a : ℕ) :
    ∀ i∈U, i∉rows (R\C) → i∈targetRows U R C a ∪ freeBefore U R a := by
  intro i hi hp
  by_cases hr : i∈rows R
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hr
    have heC : e∈C := by
      by_contra hn
      exact hp (Finset.mem_image.mpr ⟨e,Finset.mem_sdiff.mpr ⟨he,hn⟩,rfl⟩)
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,heC,rfl⟩))
  · by_cases hia : i≤a
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,hia,hr⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi,by omega,hr⟩))

/-- Solve for the original matching using the actual complement and row sets. -/
theorem actual_design_solved {F : Type*} [CommRing F] {n m d a : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) {R C : Edges} (hm : IsMatching R) (hR : R⊆grid n m)
    (hC : C⊆R) (hd : R.card≤d) :
    ψ R = (∑ M ∈ lowerTerms (cols C) (freeBefore (Finset.Icc 1 n) R a),
        (-1:F)^M.card * ψ ((R\C)∪M)) -
      ∑ M ∈ (fullTerms (cols C) (targetRows (Finset.Icc 1 n) R C a)).erase C,
        ψ ((R\C)∪M) := by
  classical
  have hT : targetRows (Finset.Icc 1 n) R C a ⊆ Finset.Icc 1 n := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_product.mp (hR (hC he))).1
    · exact (Finset.mem_filter.mp hi).1
  have hB : freeBefore (Finset.Icc 1 n) R a ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
  have hS : cols C⊆Finset.Icc 1 m := by
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_product.mp (hR (hC he))).2
  have hdeg : (R\C).card+(cols C).card≤d := by
    rw [matching_cols_card (matching_subset hm hC),Finset.card_sdiff_of_subset hC]
    have := Finset.card_le_card hC
    omega
  have h := design_inclusion_exclusion hψ (R\C) _ _ (cols C) hT hB
    (actual_free_target_disjoint hC _ _).symm (actual_design_cover _ a)
    ((Finset.sdiff_subset).trans hR) hS (complement_columns_disjoint hm hC) hdeg
  have hs := Finset.add_sum_erase
    (fullTerms (cols C) (targetRows (Finset.Icc 1 n) R C a))
    (fun M => ψ ((R\C)∪M)) (original_mem_full hm hC _ a)
  dsimp only at hs
  rw [Finset.sdiff_union_of_subset hC,h] at hs
  exact eq_sub_of_add_eq hs

/-- Removing colliding terms changes no sum for an arbitrary design. -/
theorem design_sum_filter {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (P : Edges) (A : Finset Edges) (w : Edges → F) :
    (∑ M ∈ A.filter (fun M => IsMatching (P∪M)), w M * ψ (P∪M)) =
      ∑ M ∈ A, w M * ψ (P∪M) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M hM
  split_ifs with hm
  · rfl
  · simp [hψ.1 _ hm]

/-- The actual signed pair enumeration is compatible with every design. -/
theorem design_rowPairs_sum {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (P C : Edges) (B T : Finset ℕ)
    (hC : IsMatching C) (hB : B.card<C.card) :
    (∑ v ∈ rowPairs P C B T, (v.2:F) * ψ (P∪v.1)) =
      (∑ M ∈ lowerTerms (cols C) B, (-1:F)^M.card * ψ (P∪M)) -
      ∑ M ∈ (fullTerms (cols C) T).erase C, ψ (P∪M) := by
  classical
  rw [rowPairs,Finset.sum_union (rowPair_families_disjoint P C B T hC hB)]
  rw [Finset.sum_image (fun M _ K _ h => congrArg Prod.fst h),
    Finset.sum_image (fun M _ K _ h => congrArg Prod.fst h)]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
  rw [design_sum_filter hψ,design_sum_filter hψ]
  simp [sub_eq_add_neg,Finset.sum_neg_distrib]

/-- A selected row rewrite preserves every degree-bounded design, without a rewrite premise. -/
theorem row_children_design {F : Type*} [CommRing F] {n m d a : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) {R C : Edges} (hm : IsMatching R) (hR : R⊆grid n m)
    (hd : R.card≤d) (hc : chosenRewrite R=.row a C) :
    ψ R = ∑ v ∈ children n m R, (v.2:F)*ψ v.1 := by
  classical
  obtain ⟨hC,hB⟩ := row_choice_data hR hc
  rw [children_row_eq hR hc,Finset.sum_image
    (adjoin_injOn _ _ _ _ (complement_columns_disjoint hm hC))]
  rw [design_rowPairs_sum hψ (R\C) C _ _ (matching_subset hm hC) hB]
  exact actual_design_solved hψ hm hR hC hd

/-- The design equations transpose; no equivariance of the deterministic normalizer is assumed. -/
theorem design_transpose {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsDesign n m d ψ) : IsDesign m n d (fun P => ψ (transpose P)) := by
  have hins : ∀ P i j, transpose (insert (i,j) P)=insert (j,i) (transpose P) := by
    intro P i j
    simp [transpose,Finset.map_insert,swapEmbedding]
  refine ⟨?_,?_,?_⟩
  · intro P hm
    exact h.1 (transpose P) (fun ht => hm ((matching_transpose P).mp ht))
  · intro P hP hd i hi
    have hc : (transpose P).card+1 ≤ d := by simpa using hd
    simpa only [hins] using h.2.2 (transpose P) (transpose_subset_grid hP) hc i hi
  · intro P hP hd j hj
    have hc : (transpose P).card+1 ≤ d := by simpa using hd
    simpa only [hins] using h.2.1 (transpose P) (transpose_subset_grid hP) hc j hj

/-- Every actual selected nonterminal rewrite preserves every degree-bounded design. -/
theorem chosen_children_design {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) {R : Edges} (hm : IsMatching R) (hR : R⊆grid n m)
    (hd : R.card≤d) (hnt : chosenRewrite R≠.terminal) :
    ψ R = ∑ v ∈ children n m R, (v.2:F)*ψ v.1 := by
  classical
  cases hc : chosenRewrite R with
  | terminal => exact (hnt hc).elim
  | row a C => exact row_children_design hψ hm hR hd hc
  | column a C =>
    have h := row_children_design (design_transpose hψ) ((matching_transpose R).mpr hm)
      (transpose_subset_grid hR) (by simpa using hd) (column_choice_transposes hc)
    rw [← children_column_transpose hR hc,Finset.sum_image signedTranspose_injective.injOn] at h
    simpa only [signedTranspose,transpose_transpose] using h


/-- The actual terminal expansion is valid for every bounded design, not only permutation evaluations. -/
theorem design_leaf_expansion {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (R : Edges) (hm : IsMatching R) (hR : R⊆grid n m)
    (hd : R.card≤d) :
    ψ R = ∑ T ∈ terminalFamily n m, (leafCoeff n m R T:F)*ψ T := by
  classical
  induction R using (measure (fun R => rank (grid n m) (n+m) R)).wf.induction with
  | h R ih =>
    by_cases ht : chosenRewrite R = .terminal
    · have hmem := (mem_terminalFamily n m R).mpr ⟨hR,hm,ht⟩
      simp_rw [leafCoeff_terminal n m R _ ht]
      simp [hmem]
    · calc
        ψ R = ∑ x ∈ children n m R, (x.2:F)*ψ x.1 :=
          chosen_children_design hψ hm hR hd ht
        _ = ∑ x ∈ children n m R, (x.2:F)*
            (∑ T ∈ terminalFamily n m, (leafCoeff n m x.1 T:F)*ψ T) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hcl := child_closed hR hx
          rw [ih x.1 (child_rank_lt hm hR hx) hcl.1 hcl.2 ((child_card_le hm hR hx).trans hd)]
        _ = ∑ T ∈ terminalFamily n m, (leafCoeff n m R T:F)*ψ T := by
          simp_rw [Finset.mul_sum,← mul_assoc]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro T hT
          rw [leafCoeff_recursion R T hm hR,if_neg ht,Int.cast_sum,Finset.sum_mul]
          simp only [Int.cast_mul]

/-- Only terminals within the permitted degree are evaluated. -/
theorem design_leaf_expansion_bounded {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (R : Edges) (hm : IsMatching R) (hR : R⊆grid n m)
    (hd : R.card≤d) :
    ψ R = ∑ T ∈ (terminalFamily n m).filter (fun T => T.card≤d),
      (leafCoeff n m R T:F)*ψ T := by
  classical
  rw [design_leaf_expansion hψ R hm hR hd,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  split_ifs with hTd
  · rfl
  · rw [leafCoeff_eq_zero_above_degree R T hm hR (by omega),Int.cast_zero,zero_mul]

/-- Agreement on actual degree-bounded terminal matchings determines a design on the whole grid. -/
theorem design_determined_by_terminals {F : Type*} [CommRing F] {n m d : ℕ} {ψ ν : Edges → F}
    (hψ : IsDesign n m d ψ) (hν : IsDesign n m d ν)
    (ht : ∀ T∈terminalFamily n m, T.card≤d → ψ T=ν T)
    (R : Edges) (hR : R⊆grid n m) (hd : R.card≤d) : ψ R=ν R := by
  classical
  by_cases hm : IsMatching R
  · rw [design_leaf_expansion_bounded hψ R hm hR hd,design_leaf_expansion_bounded hν R hm hR hd]
    apply Finset.sum_congr rfl
    intro T hT
    obtain ⟨hT,hdT⟩ := Finset.mem_filter.mp hT
    rw [ht T hT hdT]
  · rw [hψ.1 R hm,hν.1 R hm]

/-- Non-vacuity: the normalized proper rectangular degree-two design satisfies the full expansion. -/
theorem four_by_eight_expansion (R : Edges) (hm : IsMatching R) (hR : R⊆grid 4 8)
    (hd : R.card≤2) :
    (rectCoefficient 4 8 R : ZMod 2) =
      ∑ T ∈ (terminalFamily 4 8).filter (fun T => T.card≤2),
        (leafCoeff 4 8 R T:ZMod 2)*(rectCoefficient 4 8 T:ZMod 2) :=
  design_leaf_expansion_bounded four_by_eight_design.2 R hm hR hd

end SelfContainedCycle057
