import CharacteristicTransfer

namespace SelfContainedCycle045
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle039 SelfContainedCycle040

/-- Integer evaluation of a matching monomial at an actual permutation edge set. -/
def permutationEval (π R : Edges) : ℤ := if R ⊆ π then 1 else 0

@[simp] theorem permutationEval_empty (π : Edges) : permutationEval π ∅ = 1 := by
  simp [permutationEval]

theorem permutationEval_union (π P M : Edges) :
    permutationEval π (P ∪ M) = permutationEval π P * permutationEval π M := by
  simp only [permutationEval, Finset.union_subset_iff]
  split_ifs <;> simp_all

theorem matching_subset {π M : Edges} (hπ : IsMatching π) (h : M ⊆ π) : IsMatching M := by
  intro e he f hf hef
  exact hπ e (h he) f (h hf) hef

/-- All lower injection terms, without introducing an abstract identity as a premise. -/
def lowerTerms (S B : Finset ℕ) : Finset Edges :=
  ((B.product S).powerset).filter IsMatching

/-- All full-column injection terms, including the original chain. -/
def fullTerms (S T : Finset ℕ) : Finset Edges :=
  ((T.product S).powerset).filter (fun M => IsMatching M ∧ cols M = S)

def lowerEval (π : Edges) (S B : Finset ℕ) : ℤ :=
  ∑ M ∈ lowerTerms S B, (-1:ℤ)^M.card * permutationEval π M

def fullEval (π : Edges) (S T : Finset ℕ) : ℤ :=
  ∑ M ∈ fullTerms S T, permutationEval π M

/-- The concrete edges of a permutation eligible for a lower injection. -/
def selected (π : Edges) (S B : Finset ℕ) : Edges := π ∩ B.product S

/-- Actual evaluated lower terms are exactly all subsets of the selected permutation edges. -/
theorem lower_filter_eq (π : Edges) (hπ : IsMatching π) (S B : Finset ℕ) :
    (lowerTerms S B).filter (fun M => M ⊆ π) = (selected π S B).powerset := by
  ext M
  simp only [lowerTerms, Finset.mem_filter, Finset.mem_powerset, selected, Finset.subset_inter_iff]
  constructor
  · rintro ⟨⟨hB,_⟩,hP⟩; exact ⟨hP,hB⟩
  · rintro ⟨hP,hB⟩; exact ⟨⟨hB,matching_subset hπ hP⟩,hP⟩

theorem lowerEval_eq_powerset (π : Edges) (hπ : IsMatching π) (S B : Finset ℕ) :
    lowerEval π S B = ∑ M ∈ (selected π S B).powerset, (-1:ℤ)^M.card := by
  rw [← lower_filter_eq π hπ S B, Finset.sum_filter]
  unfold lowerEval
  apply Finset.sum_congr rfl
  intro M hM
  simp only [permutationEval]
  split_ifs <;> simp

/-- Column restriction of the actual permutation, used for the unique full injection. -/
def columnSlice (π : Edges) (S : Finset ℕ) : Edges := π.filter (fun e => e.2 ∈ S)

theorem columnSlice_subset (π : Edges) (S : Finset ℕ) : columnSlice π S ⊆ π := Finset.filter_subset _ _

theorem columnSlice_cols (π : Edges) (S : Finset ℕ) (hS : S ⊆ cols π) :
    cols (columnSlice π S) = S := by
  ext j
  simp only [cols, columnSlice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨e,⟨_,he⟩,rfl⟩; exact he
  · intro hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp (hS hj)
    exact ⟨e,⟨he,hj⟩,rfl⟩

/-- A permutation has a unique submatching with prescribed covered columns. -/
theorem subset_eq_columnSlice {π M : Edges} (hπ : IsMatching π) (S : Finset ℕ)
    (hM : M ⊆ π) (hc : cols M = S) : M = columnSlice π S := by
  apply Finset.Subset.antisymm
  · intro e he
    exact Finset.mem_filter.mpr ⟨hM he,hc ▸ Finset.mem_image.mpr ⟨e,he,rfl⟩⟩
  · intro e he
    obtain ⟨heP,heS⟩ := Finset.mem_filter.mp he
    rw [← hc] at heS
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp heS
    have heq := hπ f (hM hf) e heP (Or.inr hfe)
    simpa only [heq] using hf

theorem subset_product_iff (M : Edges) (B S : Finset ℕ) :
    M ⊆ B.product S ↔ rows M ⊆ B ∧ cols M ⊆ S := by
  constructor
  · intro h
    constructor <;> intro i hi <;> obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    · exact (Finset.mem_product.mp (h he)).1
    · exact (Finset.mem_product.mp (h he)).2
  · rintro ⟨hr,hc⟩ e he
    exact Finset.mem_product.mpr ⟨hr (Finset.mem_image.mpr ⟨e,he,rfl⟩),hc (Finset.mem_image.mpr ⟨e,he,rfl⟩)⟩

/-- The contributing full injection family is either its actual unique member or empty. -/
theorem full_filter_eq (π : Edges) (hπ : IsMatching π) (S T : Finset ℕ) (hS : S ⊆ cols π) :
    (fullTerms S T).filter (fun M => M ⊆ π) =
      if rows (columnSlice π S) ⊆ T then {columnSlice π S} else ∅ := by
  classical
  have hc := columnSlice_cols π S hS
  have hm := matching_subset hπ (columnSlice_subset π S)
  ext M
  simp only [fullTerms, Finset.mem_filter, Finset.mem_powerset, subset_product_iff]
  split_ifs with hr
  · simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_,_,hcM⟩,hMP⟩
      exact subset_eq_columnSlice hπ S hMP hcM
    · rintro rfl
      exact ⟨⟨⟨hr,hc.le⟩,hm,hc⟩,columnSlice_subset π S⟩
  · simp only [Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨hMT,_⟩,_,hcM⟩,hMP⟩
    exact hr ((subset_eq_columnSlice hπ S hMP hcM) ▸ hMT)

theorem fullEval_eq (π : Edges) (hπ : IsMatching π) (S T : Finset ℕ) (hS : S ⊆ cols π) :
    fullEval π S T = if rows (columnSlice π S) ⊆ T then 1 else 0 := by
  classical
  have heq : fullEval π S T = ∑ _M ∈ (fullTerms S T).filter (fun M => M ⊆ π), (1:ℤ) := by
    simp only [fullEval, Finset.sum_filter, permutationEval]
  rw [heq,full_filter_eq π hπ S T hS]
  split_ifs <;> simp

/-- The alternating subset sum is proved by expanding a product of 1-1. -/
theorem alternating_powerset (D : Edges) :
    (∑ M ∈ D.powerset, (-1:ℤ)^M.card) = if D = ∅ then 1 else 0 := by
  have h := Finset.prod_sub (fun _ : ℕ × ℕ => (1:ℤ)) (fun _ => (1:ℤ)) D
  have heq : (∑ M ∈ D.powerset, (-1:ℤ)^M.card) = (0:ℤ)^D.card := by
    simpa using h.symm
  rw [heq]
  by_cases hD : D = ∅
  · simp [hD]
  · simp [hD, Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hD)]

theorem lowerEval_eq (π : Edges) (hπ : IsMatching π) (S B : Finset ℕ) :
    lowerEval π S B = if selected π S B = ∅ then 1 else 0 := by
  rw [lowerEval_eq_powerset π hπ S B, alternating_powerset]

/-- The exact complementary-support condition behind the injection identity. -/
theorem selected_empty_iff (π : Edges) (S B T : Finset ℕ)
    (hBT : Disjoint B T) (hcover : rows (columnSlice π S) ⊆ B ∪ T) :
    selected π S B = ∅ ↔ rows (columnSlice π S) ⊆ T := by
  constructor
  · intro hz i hi
    rcases Finset.mem_union.mp (hcover hi) with hb | ht
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hep,hes⟩ := Finset.mem_filter.mp he
      have hx : e ∈ selected π S B := Finset.mem_inter.mpr ⟨hep,Finset.mem_product.mpr ⟨hb,hes⟩⟩
      rw [hz] at hx
      exact (Finset.notMem_empty _ hx).elim
    · exact ht
  · intro ht
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨hep,heb⟩ := Finset.mem_inter.mp he
    obtain ⟨hb,hs⟩ := Finset.mem_product.mp heb
    have hrow : e.1 ∈ rows (columnSlice π S) :=
      Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨hep,hs⟩,rfl⟩
    exact Finset.disjoint_left.mp hBT hb (ht hrow)

/-- The evaluated finite injection identity, with concrete lower and full families. -/
theorem injection_evaluation (π : Edges) (hπ : IsMatching π) (S B T : Finset ℕ)
    (hS : S ⊆ cols π) (hBT : Disjoint B T) (hcover : rows (columnSlice π S) ⊆ B ∪ T) :
    lowerEval π S B = fullEval π S T := by
  rw [lowerEval_eq π hπ S B, fullEval_eq π hπ S T hS]
  simp only [selected_empty_iff π S B T hBT hcover]

/-- A column not used by P cannot use a row already fixed by P in an extending permutation. -/
theorem slice_avoids_fixed_rows {π P : Edges} (hπ : IsMatching π) (hP : P ⊆ π)
    (S : Finset ℕ) (hPS : Disjoint (cols P) S) :
    Disjoint (rows P) (rows (columnSlice π S)) := by
  apply Finset.disjoint_left.mpr
  intro i hiP hiS
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hiP
  obtain ⟨f,hf,hfi⟩ := Finset.mem_image.mp hiS
  obtain ⟨hfπ,hfS⟩ := Finset.mem_filter.mp hf
  have heq := hπ e (hP he) f hfπ (Or.inl (hei.trans hfi.symm))
  have hec : e.2 ∈ cols P := Finset.mem_image.mpr ⟨e,he,rfl⟩
  rw [heq] at hec
  exact Finset.disjoint_left.mp hPS hec hfS

/-- Actual free-before and target-row sets are disjoint. -/
theorem actual_free_target_disjoint {R C : Edges} (hC : C ⊆ R) (U : Finset ℕ) (a : ℕ) :
    Disjoint (freeBefore U R a) (targetRows U R C a) := by
  apply Finset.disjoint_left.mpr
  intro i hiB hiT
  obtain ⟨_,hia,hiR⟩ := Finset.mem_filter.mp hiB
  rcases Finset.mem_union.mp hiT with hiC | hiF
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hiC
    exact hiR (Finset.mem_image.mpr ⟨e,hC he,rfl⟩)
  · have hia' := (Finset.mem_filter.mp hiF).2.1
    omega

/-- The required support partition is derived from the actual fixed complement. -/
theorem actual_slice_cover {π R C : Edges} {N a : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N) (hR : IsMatching R) (hC : C ⊆ R)
    (hP : R \ C ⊆ π) :
    rows (columnSlice π (cols C)) ⊆
      freeBefore (Finset.Icc 1 N) R a ∪ targetRows (Finset.Icc 1 N) R C a := by
  have hd := slice_avoids_fixed_rows hπ hP (cols C) (complement_columns_disjoint hR hC)
  intro i hi
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
  have heπ := (Finset.mem_filter.mp he).1
  have hiU := (Finset.mem_product.mp (hπg heπ)).1
  by_cases hiR : e.1 ∈ rows R
  · obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp hiR
    by_cases hfC : f ∈ C
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f,hfC,hfe⟩))
    · have hiP : e.1 ∈ rows (R \ C) := Finset.mem_image.mpr ⟨f,Finset.mem_sdiff.mpr ⟨hf,hfC⟩,hfe⟩
      exact (Finset.disjoint_left.mp hd hiP (Finset.mem_image.mpr ⟨e,he,rfl⟩)).elim
  · by_cases hia : e.1 ≤ a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiU,hia,hiR⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiU,by omega,hiR⟩))

/-- No support-partition hypothesis remains for the actual row sets at a square permutation. -/
theorem actual_injection_evaluation {π R C : Edges} {N a : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N) (hπc : cols π = Finset.Icc 1 N)
    (hR : IsMatching R) (hRg : R ⊆ grid N N) (hC : C ⊆ R) (hP : R \ C ⊆ π) :
    lowerEval π (cols C) (freeBefore (Finset.Icc 1 N) R a) =
      fullEval π (cols C) (targetRows (Finset.Icc 1 N) R C a) := by
  apply injection_evaluation π hπ
  · rw [hπc]
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_product.mp (hRg (hC he))).2
  · exact actual_free_target_disjoint hC _ _
  · exact actual_slice_cover hπ hπg hR hC hP

/-- The actual initial C occurs among the full injections with coefficient one. -/
theorem original_mem_full {R C : Edges} (hR : IsMatching R) (hC : C ⊆ R)
    (U : Finset ℕ) (a : ℕ) : C ∈ fullTerms (cols C) (targetRows U R C a) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ((subset_product_iff C _ _).mpr ⟨?_,Finset.Subset.refl _⟩),matching_subset hR hC,rfl⟩
  exact Finset.subset_union_left

/-- Separating the actual original injection from the other full injections. -/
theorem fullEval_split {π C : Edges} {T : Finset ℕ} (hC : C ∈ fullTerms (cols C) T) :
    fullEval π (cols C) T = permutationEval π C +
      ∑ M ∈ (fullTerms (cols C) T).erase C, permutationEval π M := by
  exact (Finset.add_sum_erase _ _ hC).symm

/-- The solved signed injection formula with its actual fixed complement, including non-extending permutations. -/
theorem actual_solved_evaluation {π R C : Edges} {N a : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N) (hπc : cols π = Finset.Icc 1 N)
    (hR : IsMatching R) (hRg : R ⊆ grid N N) (hC : C ⊆ R) :
    permutationEval π R =
      (∑ M ∈ lowerTerms (cols C) (freeBefore (Finset.Icc 1 N) R a),
        (-1:ℤ)^M.card * permutationEval π ((R \ C) ∪ M)) -
      ∑ M ∈ (fullTerms (cols C) (targetRows (Finset.Icc 1 N) R C a)).erase C,
        permutationEval π ((R \ C) ∪ M) := by
  by_cases hP : R \ C ⊆ π
  · have hpv : permutationEval π (R \ C) = 1 := if_pos hP
    have hv : permutationEval π R = permutationEval π C := by
      calc
        permutationEval π R = permutationEval π ((R \ C) ∪ C) := by rw [Finset.sdiff_union_of_subset hC]
        _ = permutationEval π C := by rw [permutationEval_union,hpv,one_mul]
    simp only [permutationEval_union,hpv,one_mul,hv]
    change permutationEval π C = lowerEval π (cols C) (freeBefore (Finset.Icc 1 N) R a) - _
    rw [actual_injection_evaluation hπ hπg hπc hR hRg hC hP,
      fullEval_split (original_mem_full hR hC _ a)]
    ring
  · have hpv : permutationEval π (R \ C) = 0 := if_neg hP
    have hRv : permutationEval π R = 0 := by
      apply if_neg
      exact fun h => hP (Finset.sdiff_subset.trans h)
    simp only [permutationEval_union,hpv,zero_mul,mul_zero,Finset.sum_const_zero,sub_zero,hRv]

/-- Invalid unions automatically evaluate to zero at a matching. -/
theorem eval_zero_of_not_matching {π Q : Edges} (hπ : IsMatching π) (hQ : ¬ IsMatching Q) :
    permutationEval π Q = 0 := by
  apply if_neg
  exact fun h => hQ (matching_subset hπ h)

/-- Keeping only compatible fixed-complement unions does not change the signed sum. -/
theorem sum_filter_compatible {π P : Edges} (hπ : IsMatching π) (A : Finset Edges) (w : Edges → ℤ) :
    (∑ M ∈ A.filter (fun M => IsMatching (P ∪ M)), w M * permutationEval π (P ∪ M)) =
      ∑ M ∈ A, w M * permutationEval π (P ∪ M) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M hM
  split_ifs with h
  · rfl
  · rw [eval_zero_of_not_matching hπ h,mul_zero]

/-- Explicit signed pairs before adjoining the fixed complement. -/
def rowPairs (P C : Edges) (B T : Finset ℕ) : Finset (Edges × ℤ) :=
  (((lowerTerms (cols C) B).filter (fun M => IsMatching (P ∪ M))).image
    (fun M => (M,(-1:ℤ)^M.card))) ∪
  ((((fullTerms (cols C) T).erase C).filter (fun M => IsMatching (P ∪ M))).image
    (fun M => (M,(-1:ℤ))))

/-- The finite explicit pair enumeration is exactly the original replacement predicate. -/
theorem mem_rowPairs (P C M : Edges) (B T : Finset ℕ) (z : ℤ) :
    (M,z) ∈ rowPairs P C B T ↔ Replacement C B T M z ∧ IsMatching (P ∪ M) := by
  simp only [rowPairs, Finset.mem_union, Finset.mem_image, Prod.mk.injEq]
  simp only [lowerTerms, fullTerms, Finset.mem_filter, Finset.mem_powerset,
    subset_product_iff, Finset.mem_erase]
  constructor
  · rintro (⟨M',⟨⟨⟨hrow,hcol⟩,hm⟩,hPM⟩,rfl,rfl⟩ | ⟨M',⟨⟨hne,⟨⟨hrow,hcol⟩,hm,hcols⟩⟩,hPM⟩,rfl,rfl⟩)
    · exact ⟨Or.inl ⟨hm,hrow,hcol,rfl⟩,hPM⟩
    · exact ⟨Or.inr ⟨hm,hrow,hcols,hne,rfl⟩,hPM⟩
  · rintro ⟨h,hPM⟩
    rcases h with ⟨hm,hrow,hcol,rfl⟩ | ⟨hm,hrow,hcols,hne,rfl⟩
    · exact Or.inl ⟨M,⟨⟨⟨hrow,hcol⟩,hm⟩,hPM⟩,rfl,rfl⟩
    · exact Or.inr ⟨M,⟨⟨hne,⟨⟨hrow,hcols.le⟩,hm,hcols⟩⟩,hPM⟩,rfl,rfl⟩

theorem mem_lowerTerms (S B : Finset ℕ) (M : Edges) :
    M ∈ lowerTerms S B ↔ IsMatching M ∧ rows M ⊆ B ∧ cols M ⊆ S := by
  simp only [lowerTerms,Finset.mem_filter,Finset.mem_powerset,subset_product_iff]
  tauto

theorem mem_fullTerms (S T : Finset ℕ) (M : Edges) :
    M ∈ fullTerms S T ↔ IsMatching M ∧ rows M ⊆ T ∧ cols M = S := by
  simp only [fullTerms,Finset.mem_filter,Finset.mem_powerset,subset_product_iff]
  constructor
  · rintro ⟨⟨hr,_⟩,hm,hc⟩; exact ⟨hm,hr,hc⟩
  · rintro ⟨hm,hr,hc⟩; exact ⟨⟨hr,hc.le⟩,hm,hc⟩

/-- The lower and other full signed families cannot be merged with multiplicity loss. -/
theorem rowPair_families_disjoint (P C : Edges) (B T : Finset ℕ)
    (hC : IsMatching C) (hB : B.card < C.card) :
    Disjoint
      (((lowerTerms (cols C) B).filter (fun M => IsMatching (P ∪ M))).image
        (fun M => (M,(-1:ℤ)^M.card)))
      ((((fullTerms (cols C) T).erase C).filter (fun M => IsMatching (P ∪ M))).image
        (fun M => (M,(-1:ℤ)))) := by
  apply Finset.disjoint_left.mpr
  intro v hl hu
  obtain ⟨M,hM,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨K,hK,heq⟩ := Finset.mem_image.mp hu
  have hKM : K = M := congrArg Prod.fst heq
  subst K
  have hm := (mem_lowerTerms _ _ _).mp (Finset.mem_filter.mp hM).1
  have hk := Finset.mem_erase.mp (Finset.mem_filter.mp hK).1
  have hfull := (mem_fullTerms _ _ _).mp hk.2
  exact term_kinds_disjoint hC hB ⟨hm.1,hm.2.1,hm.2.2,rfl⟩
    ⟨hfull.1,hfull.2.1,hfull.2.2,hk.1,rfl⟩

/-- Weighted pair sum equals the solved injection formula, with compatibility proved harmless. -/
theorem rowPairs_sum (π P C : Edges) (B T : Finset ℕ)
    (hπ : IsMatching π) (hC : IsMatching C) (hB : B.card < C.card) :
    (∑ v ∈ rowPairs P C B T, v.2 * permutationEval π (P ∪ v.1)) =
      (∑ M ∈ lowerTerms (cols C) B, (-1:ℤ)^M.card * permutationEval π (P ∪ M)) -
      ∑ M ∈ (fullTerms (cols C) T).erase C, permutationEval π (P ∪ M) := by
  rw [rowPairs,Finset.sum_union (rowPair_families_disjoint P C B T hC hB)]
  rw [Finset.sum_image (fun M _ K _ h => congrArg Prod.fst h),
    Finset.sum_image (fun M _ K _ h => congrArg Prod.fst h)]
  change (∑ M ∈ (lowerTerms (cols C) B).filter (fun M => IsMatching (P ∪ M)),
    (-1:ℤ)^M.card * permutationEval π (P ∪ M)) +
    (∑ M ∈ ((fullTerms (cols C) T).erase C).filter (fun M => IsMatching (P ∪ M)),
    (-1:ℤ) * permutationEval π (P ∪ M)) = _
  rw [sum_filter_compatible hπ, sum_filter_compatible hπ]
  simp [sub_eq_add_neg,Finset.sum_neg_distrib]

/-- Adjoining the fixed complement is injective on the actual signed pair family. -/
theorem adjoin_injOn (P C : Edges) (B T : Finset ℕ) (hPC : Disjoint (cols P) (cols C)) :
    Set.InjOn (fun v : Edges × ℤ => (P ∪ v.1,v.2)) (rowPairs P C B T : Set (Edges × ℤ)) := by
  intro v hv w hw heq
  have hv' := (mem_rowPairs _ _ _ _ _ _).mp hv
  have hw' := (mem_rowPairs _ _ _ _ _ _).mp hw
  apply Prod.ext
  · exact replacement_unique hPC hv'.1 hw'.1 (congrArg Prod.fst heq)
  · have hz := congrArg (fun x : Edges × ℤ => x.2) heq
    exact hz

/-- The original existential branch predicate is exactly the image of our finite signed family. -/
theorem mem_adjoined_pairs (P C Q : Edges) (B T : Finset ℕ) (z : ℤ) :
    (Q,z) ∈ (rowPairs P C B T).image (fun v => (P ∪ v.1,v.2)) ↔ Branch P C B T Q z := by
  constructor
  · intro h
    obtain ⟨⟨M,w⟩,hM,hq⟩ := Finset.mem_image.mp h
    have hzw := congrArg Prod.snd hq
    change w=z at hzw
    subst w
    obtain ⟨hr,hm⟩ := (mem_rowPairs _ _ _ _ _ _).mp hM
    exact ⟨M,hr,hm,(congrArg Prod.fst hq).symm⟩
  · rintro ⟨M,hr,hm,rfl⟩
    exact Finset.mem_image.mpr ⟨(M,z),(mem_rowPairs _ _ _ _ _ _).mpr ⟨hr,hm⟩,rfl⟩

/-- For a genuine row choice, this is exactly the finite children enumeration from Cycle040. -/
theorem children_row_eq {N K a : ℕ} {R C : Edges} (hR : R ⊆ grid N K)
    (hc : chosenRewrite R = .row a C) :
    children N K R =
      (rowPairs (R \ C) C (freeBefore (Finset.Icc 1 N) R a)
        (targetRows (Finset.Icc 1 N) R C a)).image (fun v => ((R \ C) ∪ v.1,v.2)) := by
  ext v
  rcases v with ⟨Q,z⟩
  rw [mem_children_iff hR,mem_adjoined_pairs]
  simp only [ChosenBranch,hc]

/-- Actual row-child evaluation, with every finite enumeration and weight accounted for. -/
theorem row_children_evaluation {π R C : Edges} {N a : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N) (hπc : cols π = Finset.Icc 1 N)
    (hR : IsMatching R) (hRg : R ⊆ grid N N) (hC : C ⊆ R)
    (hB : (freeBefore (Finset.Icc 1 N) R a).card < C.card)
    (hc : chosenRewrite R = .row a C) :
    permutationEval π R = ∑ v ∈ children N N R, v.2 * permutationEval π v.1 := by
  rw [children_row_eq hRg hc,Finset.sum_image
    (adjoin_injOn _ _ _ _ (complement_columns_disjoint hR hC))]
  rw [rowPairs_sum π (R \ C) C _ _ hπ (matching_subset hR hC) hB]
  exact actual_solved_evaluation hπ hπg hπc hR hRg hC

/-- First-failure and longest-chain data imply the actual small-B guard. -/
theorem first_row_data {R C : Edges} {N K a : ℕ} (hRg : R ⊆ grid N K)
    (hf : FirstRowAt R a) (hC : C ∈ longestChains (rowPrefix R a)) :
    C ⊆ R ∧ (freeBefore (Finset.Icc 1 N) R a).card < C.card := by
  obtain ⟨hsub,_⟩ := (mem_chains _ _).mp (Finset.mem_filter.mp hC).1
  have hCR : C ⊆ R := hsub.trans (Finset.filter_subset _ _)
  have positive := grid_positive hRg
  obtain ⟨e,he,hea⟩ := first_failed_longest_has_endpoint positive hf hC
  have heG := Finset.mem_product.mp (hRg (hCR he))
  have ha : a ≤ N := by simpa only [hea] using (Finset.mem_Icc.mp heG.1).2
  exact ⟨hCR,failed_longest_chain_guard ha positive hf.1 hC⟩

/-- No support or guard hypothesis is left for a selected row branch. -/
theorem row_choice_data {R C : Edges} {N K a : ℕ} (hRg : R ⊆ grid N K)
    (hc : chosenRewrite R = .row a C) :
    C ⊆ R ∧ (freeBefore (Finset.Icc 1 N) R a).card < C.card := by
  unfold chosenRewrite at hc
  split_ifs at hc with hr hcol
  obtain ⟨ha,hcc⟩ := ChosenRewrite.row.inj hc
  subst a; subst C
  exact first_row_data hRg (min_row_failure_is_first R hr) (chosenLongest_spec _).1

/-- Transposition preserves the actual permutation monomial evaluation. -/
theorem eval_transpose (π R : Edges) :
    permutationEval (transpose π) (transpose R) = permutationEval π R := by
  simp only [permutationEval,transpose,Finset.map_subset_map]

def signedTranspose (v : Edges × ℤ) : Edges × ℤ := (transpose v.1,v.2)

@[simp] theorem signedTranspose_involution (v : Edges × ℤ) :
    signedTranspose (signedTranspose v) = v := by
  simp [signedTranspose,transpose_transpose]

theorem signedTranspose_injective : Function.Injective signedTranspose := by
  intro v w h
  simpa only [signedTranspose_involution] using congrArg signedTranspose h

/-- A column choice becomes a row choice on the transposed matching. -/
theorem column_choice_transposes {R C : Edges} {a : ℕ}
    (hc : chosenRewrite R = .column a C) :
    chosenRewrite (transpose R) = .row a (transpose C) := by
  unfold chosenRewrite at hc
  split_ifs at hc with hr hcol
  obtain ⟨ha,hcc⟩ := ChosenRewrite.column.inj hc
  subst a; subst C
  have ht : (rowFailures (transpose R)).Nonempty := by simpa only [rowFailures_transpose] using hcol
  rw [chosenRewrite,dif_pos ht]
  simp only [rowFailures_transpose,chosenColumnChain,transpose_transpose]

/-- The actual children transpose exactly for a selected column branch. -/
theorem children_column_transpose {R C : Edges} {N K a : ℕ} (hRg : R ⊆ grid N K)
    (hc : chosenRewrite R = .column a C) :
    (children N K R).image signedTranspose = children K N (transpose R) := by
  have ht := column_choice_transposes hc
  ext v
  rcases v with ⟨Q,z⟩
  rw [mem_children_iff (transpose_subset_grid hRg)]
  constructor
  · intro h
    obtain ⟨⟨M,w⟩,hm,heq⟩ := Finset.mem_image.mp h
    have hw : w=z := congrArg Prod.snd heq
    have hQ : transpose M=Q := congrArg Prod.fst heq
    subst w; subst Q
    have hb := (mem_children_iff hRg).mp hm
    simpa only [ChosenBranch,hc,ht,ColumnBranch,transpose_sdiff] using hb
  · intro h
    have hb : ChosenBranch N K R (transpose Q) z := by
      simpa only [ChosenBranch,hc,ht,ColumnBranch,transpose_sdiff,transpose_transpose] using h
    exact Finset.mem_image.mpr ⟨(transpose Q,z),(mem_children_iff hRg).mpr hb,by simp [signedTranspose,transpose_transpose]⟩

/-- Every actual selected nonterminal rewrite preserves square permutation evaluation. -/
theorem chosen_children_evaluation {π R : Edges} {N : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N)
    (hπr : rows π = Finset.Icc 1 N) (hπc : cols π = Finset.Icc 1 N)
    (hR : IsMatching R) (hRg : R ⊆ grid N N) (hnt : chosenRewrite R ≠ .terminal) :
    permutationEval π R = ∑ v ∈ children N N R, v.2 * permutationEval π v.1 := by
  cases hc : chosenRewrite R with
  | terminal => exact (hnt hc).elim
  | row a C =>
    obtain ⟨hC,hB⟩ := row_choice_data hRg hc
    exact row_children_evaluation hπ hπg hπc hR hRg hC hB hc
  | column a C =>
    have ht := column_choice_transposes hc
    have hRg' := transpose_subset_grid hRg
    obtain ⟨hC,hB⟩ := row_choice_data hRg' ht
    have hcols : cols (transpose π) = Finset.Icc 1 N := by
      have h := rows_transpose (transpose π)
      simpa only [transpose_transpose,hπr] using h.symm
    have h := row_children_evaluation ((matching_transpose π).mpr hπ) (transpose_subset_grid hπg)
      hcols ((matching_transpose R).mpr hR) hRg' hC hB ht
    rw [← children_column_transpose hRg hc,Finset.sum_image signedTranspose_injective.injOn] at h
    simpa only [signedTranspose,eval_transpose] using h

/-- The actual 2-by-2 row branch has one deletion and one negative replacement. -/
theorem row_two_children : children 2 2 {(1,1)} = {(∅,1),({(2,1)},-1)} := by
  rw [children_row_eq (by decide) chosen_singleton_example]
  decide

theorem row_two_identity_evaluation :
    permutationEval {(1,1),(2,2)} {(1,1)} =
      ∑ v ∈ children 2 2 {(1,1)}, v.2 * permutationEval {(1,1),(2,2)} v.1 := by
  apply chosen_children_evaluation <;> decide

/-- A genuine 1-1 cancellation, not an example where every summand vanishes. -/
theorem row_two_swap_cancellation :
    permutationEval {(1,2),(2,1)} {(1,1)} = 0 ∧
    (∑ v ∈ children 2 2 {(1,1)}, v.2 * permutationEval {(1,2),(2,1)} v.1) = 1 + (-1) := by
  rw [row_two_children]
  decide

/-- A real column choice, with no row failure, in the 2-by-2 square. -/
theorem column_two_choice : chosenRewrite {(2,1)} = .column 1 {(2,1)} := by
  have hr : rowFailures {(2,1)} = ∅ := by decide
  have hc : columnFailures {(2,1)} = {1} := by decide
  have hp : rowPrefix (transpose {(2,1)}) 1 = {(1,2)} := by decide
  have hl : chosenLongest {(1,2)} = {(1,2)} := by
    apply chosenLongest_unique
    · decide
    · intro D hD
      have hd : longestChains {(1,2)} = {{(1,2)}} := by decide
      rw [hd] at hD
      have heq := Finset.mem_singleton.mp hD
      subst D
      exact le_refl _
  unfold chosenRewrite
  simp only [hr,Finset.not_nonempty_empty,↓reduceDIte,hc,Finset.singleton_nonempty,Finset.min'_singleton]
  unfold chosenColumnChain
  rw [hp,hl]
  rfl

theorem column_two_evaluation :
    permutationEval {(1,1),(2,2)} {(2,1)} =
      ∑ v ∈ children 2 2 {(2,1)}, v.2 * permutationEval {(1,1),(2,2)} v.1 := by
  apply chosen_children_evaluation <;> decide

/-- At a terminal matching the absent rewrite equation must not be imposed. -/
theorem terminal_guard_necessary :
    chosenRewrite {(2,2)} = .terminal ∧ permutationEval {(1,1),(2,2)} {(2,2)} = 1 ∧
    children 2 2 {(2,2)} = ∅ := by
  have hr : rowFailures {(2,2)} = ∅ := by decide
  have hc : columnFailures {(2,2)} = ∅ := by decide
  have ht : chosenRewrite {(2,2)} = .terminal := by simp [chosenRewrite,hr,hc]
  exact ⟨ht,by decide,children_terminal ht⟩

/-- The selected column branch also has its exact signed children identified. -/
theorem column_two_children : children 2 2 {(2,1)} = {(∅,1),({(2,2)},-1)} := by
  have hc : children 2 2 (transpose {(2,1)}) = {(∅,1),({(2,2)},-1)} := by
    rw [children_row_eq (by decide) (column_choice_transposes column_two_choice)]
    decide
  have h := children_column_transpose (N:=2) (K:=2) (by decide) column_two_choice
  rw [hc] at h
  have h' := congrArg (Finset.image signedTranspose) h
  simp only [Finset.image_image,Function.comp_def,signedTranspose_involution] at h'
  simpa [signedTranspose,transpose,swapEmbedding] using h'

theorem column_two_identity_cancellation :
    permutationEval {(1,1),(2,2)} {(2,1)} = 0 ∧
    (∑ v ∈ children 2 2 {(2,1)}, v.2 * permutationEval {(1,1),(2,2)} v.1) = 1 + (-1) := by
  rw [column_two_children]
  decide

/-- The proved integer identity transports to every coefficient ring. -/
theorem chosen_children_evaluation_cast {F : Type*} [CommRing F] {π R : Edges} {N : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N)
    (hπr : rows π = Finset.Icc 1 N) (hπc : cols π = Finset.Icc 1 N)
    (hR : IsMatching R) (hRg : R ⊆ grid N N) (hnt : chosenRewrite R ≠ .terminal) :
    (permutationEval π R : F) =
      ∑ v ∈ children N N R, (v.2 : F) * (permutationEval π v.1 : F) := by
  have h := congrArg (fun z : ℤ => (z:F)) (chosen_children_evaluation hπ hπg hπr hπc hR hRg hnt)
  simpa only [Int.cast_sum,Int.cast_mul] using h

/-- An actual square permutation exists in every ambient size, including zero. -/
def diagonal (N : ℕ) : Edges := (Finset.Icc 1 N).image (fun i => (i,i))

theorem diagonal_matching (N : ℕ) : IsMatching (diagonal N) := by
  intro e he f hf h
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
  rcases h with h | h <;> exact congrArg (fun x => (x,x)) h

theorem diagonal_grid (N : ℕ) : diagonal N ⊆ grid N N := by
  intro e he
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_product.mpr ⟨hi,hi⟩

theorem diagonal_rows_cols (N : ℕ) : rows (diagonal N) = Finset.Icc 1 N ∧ cols (diagonal N) = Finset.Icc 1 N := by
  simp [diagonal,rows,cols,Finset.image_image,Function.comp_def]

end SelfContainedCycle045
