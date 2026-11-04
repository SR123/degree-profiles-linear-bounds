import DesignShift

namespace SelfContainedCycle056
attribute [local instance] Classical.propDecidable
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037 SelfContainedCycle038
open SelfContainedCycle045 SelfContainedCycle046 SelfContainedCycle053 SelfContainedCycle055

/-- The actual full injection family with a per-edge restriction. -/
noncomputable def maskedTerms (U S : Finset ℕ) (A : ℕ × ℕ → Prop) : Finset Edges :=
  by classical exact (fullTerms S U).filter (fun M => ∀ e ∈ M, A e)

theorem mem_maskedTerms (U S : Finset ℕ) (A : ℕ × ℕ → Prop) (M : Edges) :
    M ∈ maskedTerms U S A ↔ IsMatching M ∧ rows M ⊆ U ∧ cols M=S ∧ ∀ e ∈ M, A e := by
  classical
  simp only [maskedTerms,Finset.mem_filter,mem_fullTerms]
  tauto

theorem fresh_column_not_mem {M : Edges} {S : Finset ℕ} {i j : ℕ}
    (hM : cols M=S) (hj : j∉S) : (i,j)∉M := by
  intro h
  apply hj
  rw [← hM]
  exact Finset.mem_image.mpr ⟨(i,j),h,rfl⟩

/-- Inserting in a new column has an actual inverse by edge erasure. -/
theorem erase_fresh_column {Q : Edges} {S : Finset ℕ} {i j : ℕ}
    (hQ : IsMatching Q) (hc : cols Q=insert j S) (he : (i,j)∈Q) (hj : j∉S) :
    cols (Q.erase (i,j))=S := by
  ext k
  constructor
  · intro hk
    obtain ⟨e,he',rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hne,heQ⟩ := Finset.mem_erase.mp he'
    have hk : e.2∈insert j S := hc ▸ Finset.mem_image.mpr ⟨e,heQ,rfl⟩
    rcases Finset.mem_insert.mp hk with h | h
    · exact (hne (hQ e heQ (i,j) he (Or.inr h))).elim
    · exact h
  · intro hk
    have hk' : k∈cols Q := hc ▸ Finset.mem_insert_of_mem hk
    obtain ⟨e,heQ,hek⟩ := Finset.mem_image.mp hk'
    refine Finset.mem_image.mpr ⟨e,Finset.mem_erase.mpr ⟨?_,heQ⟩,hek⟩
    intro heq
    subst e
    exact hj (by simpa only [← hek] using hk)

/-- Distinct parent-row pairs cannot create the same matching at a fresh column. -/
theorem insert_pair_injective {S : Finset ℕ} {j : ℕ} (hj : j∉S)
    {M N : Edges} {i k : ℕ} (hM : cols M=S) (hN : cols N=S)
    (he : insert (i,j) M=insert (k,j) N) : M=N ∧ i=k := by
  have hi : (i,j)∈insert (k,j) N := he ▸ Finset.mem_insert_self _ _
  have hik : i=k := by
    rcases Finset.mem_insert.mp hi with h | h
    · exact congrArg Prod.fst h
    · exact (fresh_column_not_mem hN hj h).elim
  subst k
  have hh := congrArg (fun P : Edges => P.erase (i,j)) he
  refine ⟨?_,rfl⟩
  simpa only [Finset.erase_insert (fresh_column_not_mem hM hj),
    Finset.erase_insert (fresh_column_not_mem hN hj)] using hh

/-- Every actual new-column injection has a unique parent and selected row. -/
theorem maskedTerms_insert_image (U S : Finset ℕ) (A : ℕ × ℕ → Prop) (j : ℕ) (hj : j∉S) :
    maskedTerms U (insert j S) A =
      (((maskedTerms U S A).product (U.filter (fun i => A (i,j)))).filter
        (fun x => IsMatching (insert (x.2,j) x.1))).image
        (fun x => insert (x.2,j) x.1) := by
  classical
  ext Q
  constructor
  · intro hQ
    obtain ⟨hm,hr,hc,hA⟩ := (mem_maskedTerms _ _ _ _).mp hQ
    have hjQ : j∈cols Q := hc ▸ Finset.mem_insert_self _ _
    obtain ⟨⟨i,k⟩,he,hk⟩ := Finset.mem_image.mp hjQ
    change k=j at hk
    subst k
    have heq : insert (i,j) (Q.erase (i,j))=Q := Finset.insert_erase he
    refine Finset.mem_image.mpr ⟨(Q.erase (i,j),i),?_,heq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,heq.symm ▸ hm⟩
    · apply (mem_maskedTerms _ _ _ _).mpr
      exact ⟨matching_subset hm (Finset.erase_subset _ _),
        (Finset.image_subset_image (Finset.erase_subset _ _)).trans hr,
        erase_fresh_column hm hc he hj,fun e he' => hA e (Finset.mem_of_mem_erase he')⟩
    · exact Finset.mem_filter.mpr ⟨hr (Finset.mem_image.mpr ⟨(i,j),he,rfl⟩),hA _ he⟩
  · intro h
    obtain ⟨⟨M,i⟩,hMI,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hMI,hm⟩ := Finset.mem_filter.mp hMI
    obtain ⟨hM,hi⟩ := Finset.mem_product.mp hMI
    obtain ⟨hi,hAi⟩ := Finset.mem_filter.mp hi
    obtain ⟨_,hr,hc,hA⟩ := (mem_maskedTerms _ _ _ _).mp hM
    apply (mem_maskedTerms _ _ _ _).mpr
    refine ⟨hm,?_,?_,?_⟩
    · simpa only [rows,Finset.image_insert] using Finset.insert_subset hi hr
    · simp only [cols,Finset.image_insert,← hc]
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hAi
      · exact hA e he

/-- Reindexing the new-column sum; collisions vanish before using any design equation. -/
theorem masked_sum_insert {F : Type*} [CommRing F] (ψ : Edges → F)
    (hz : ∀ P, ¬IsMatching P → ψ P=0) (P : Edges)
    (U S : Finset ℕ) (A : ℕ × ℕ → Prop) (j : ℕ) (hj : j∉S) :
    (∑ Q ∈ maskedTerms U (insert j S) A, ψ (P∪Q)) =
      ∑ M ∈ maskedTerms U S A, ∑ i ∈ U.filter (fun i => A (i,j)), ψ (P∪insert (i,j) M) := by
  classical
  rw [maskedTerms_insert_image U S A j hj,Finset.sum_image]
  · rw [Finset.sum_filter]
    have he : ∀ x ∈ (maskedTerms U S A).product (U.filter (fun i => A (i,j))),
        (if IsMatching (insert (x.2,j) x.1) then ψ (P∪insert (x.2,j) x.1) else 0)=
          ψ (P∪insert (x.2,j) x.1) := by
      intro x _
      split_ifs with hm
      · rfl
      · symm
        apply hz
        intro hu
        exact hm (matching_subset hu Finset.subset_union_right)
    rw [Finset.sum_congr rfl he]
    exact Finset.sum_product _ _ (fun x => ψ (P∪insert (x.2,j) x.1))
  · intro x hx y hy he
    have hx' := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    have hy' := (Finset.mem_product.mp (Finset.mem_filter.mp hy).1).1
    obtain ⟨hh,hi⟩ := insert_pair_injective hj ((mem_maskedTerms _ _ _ _).mp hx').2.2.1
      ((mem_maskedTerms _ _ _ _).mp hy').2.2.1 he
    exact Prod.ext hh hi

/-- A new edge in an occupied row and a fresh column forces a collision. -/
theorem occupied_row_collision {P M : Edges} {i j : ℕ}
    (hi : i∈rows P) (hj : j∉cols P) : ¬ IsMatching (P∪insert (i,j) M) := by
  intro h
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hi
  have heq := h e (Finset.mem_union_left _ he) (i,j)
    (Finset.mem_union_right _ (Finset.mem_insert_self _ _)) (Or.inl hei)
  apply hj
  exact Finset.mem_image.mpr ⟨e,he,congrArg Prod.snd heq⟩

/-- Edge restrictions need only agree on the selected columns. -/
theorem maskedTerms_congr (U S : Finset ℕ) (A B : ℕ × ℕ → Prop)
    (h : ∀ i j, j∈S → (A (i,j) ↔ B (i,j))) : maskedTerms U S A=maskedTerms U S B := by
  classical
  ext M
  rw [mem_maskedTerms,mem_maskedTerms]
  constructor <;> rintro ⟨hm,hr,hc,ha⟩ <;> refine ⟨hm,hr,hc,?_⟩ <;> intro e he
  · exact (h e.1 e.2 (hc ▸ Finset.mem_image.mpr ⟨e,he,rfl⟩)).mp (ha e he)
  · exact (h e.1 e.2 (hc ▸ Finset.mem_image.mpr ⟨e,he,rfl⟩)).mpr (ha e he)

/-- Summing over a fresh column uses exactly one design equation per parent matching.
The allowed rows may omit occupied rows of P, since those terms are genuine collisions. -/
theorem masked_sum_totality {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (P : Edges) (S : Finset ℕ) (A : ℕ × ℕ → Prop)
    (hP : P ⊆ grid n m) (hS : S ⊆ Finset.Icc 1 m) (j : ℕ)
    (hj : j∈Finset.Icc 1 m) (hjS : j∉S) (hjP : j∉cols P)
    (hA : ∀ i∈Finset.Icc 1 n, i∉rows P → A (i,j))
    (hd : P.card+S.card+1≤d) :
    (∑ Q ∈ maskedTerms (Finset.Icc 1 n) (insert j S) A, ψ (P∪Q)) =
      ∑ M ∈ maskedTerms (Finset.Icc 1 n) S A, ψ (P∪M) := by
  classical
  rw [masked_sum_insert ψ hψ.1 P _ S A j hjS]
  apply Finset.sum_congr rfl
  intro M hM
  obtain ⟨hm,hr,hc,_⟩ := (mem_maskedTerms _ _ _ _).mp hM
  have hMg : M ⊆ grid n m := by
    apply (subset_product_iff M _ _).mpr
    exact ⟨hr,hc ▸ hS⟩
  have he : (∑ i ∈ (Finset.Icc 1 n).filter (fun i => A (i,j)), ψ (P∪insert (i,j) M)) =
      ∑ i ∈ Finset.Icc 1 n, ψ (P∪insert (i,j) M) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hai
    · rfl
    · symm
      apply hψ.1
      apply occupied_row_collision (hj:=hjP)
      by_contra hiP
      exact hai (hA i hi hiP)
  rw [he]
  have hcard : (P∪M).card+1≤d := by
    have hcm := matching_cols_card hm
    have hu := Finset.card_union_le P M
    rw [hc] at hcm
    omega
  simpa only [Finset.union_insert] using hψ.2.2 (P∪M) (Finset.union_subset hP hMg) hcard j hj

/-- Mixed injection sum: columns in X use T, and the remaining selected columns use B. -/
noncomputable def mixedSum {F : Type*} [CommRing F] (ψ : Edges → F)
    (P : Edges) (U T B X Y : Finset ℕ) : F :=
  ∑ M ∈ maskedTerms U (X∪Y) (fun e => if e.2∈X then e.1∈T else e.1∈B), ψ (P∪M)

theorem mixed_insert_left {F : Type*} [CommRing F] (ψ : Edges → F)
    (hz : ∀ P, ¬IsMatching P → ψ P=0) (P : Edges) (U T B X Y : Finset ℕ)
    (hT : T⊆U) (j : ℕ) (hj : j∉X∪Y) :
    mixedSum ψ P U T B (insert j X) Y =
      ∑ M ∈ maskedTerms U (X∪Y) (fun e => if e.2∈X then e.1∈T else e.1∈B),
        ∑ i ∈ T, ψ (P∪insert (i,j) M) := by
  classical
  unfold mixedSum
  rw [Finset.insert_union,masked_sum_insert ψ hz P _ _ _ j hj]
  have hmask := maskedTerms_congr U (X∪Y)
    (fun e => if e.2∈insert j X then e.1∈T else e.1∈B)
    (fun e => if e.2∈X then e.1∈T else e.1∈B) (by
      intro i k hk
      have hkj : k≠j := by rintro rfl; exact hj hk
      simp only [Finset.mem_insert,hkj, false_or])
  rw [hmask]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr ?_ (by intros; rfl)
  ext i
  simp only [Finset.mem_filter,Finset.mem_insert_self,if_true]
  exact ⟨And.right,fun hi => ⟨hT hi,hi⟩⟩

theorem mixed_insert_right {F : Type*} [CommRing F] (ψ : Edges → F)
    (hz : ∀ P, ¬IsMatching P → ψ P=0) (P : Edges) (U T B X Y : Finset ℕ)
    (hB : B⊆U) (j : ℕ) (hj : j∉X∪Y) :
    mixedSum ψ P U T B X (insert j Y) =
      ∑ M ∈ maskedTerms U (X∪Y) (fun e => if e.2∈X then e.1∈T else e.1∈B),
        ∑ i ∈ B, ψ (P∪insert (i,j) M) := by
  classical
  unfold mixedSum
  rw [Finset.union_insert,masked_sum_insert ψ hz P _ _ _ j hj]
  have hjX : j∉X := fun h => hj (Finset.mem_union_left _ h)
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr ?_ (by intros; rfl)
  ext i
  simp only [Finset.mem_filter,if_neg hjX]
  exact ⟨And.right,fun hi => ⟨hB hi,hi⟩⟩

/-- A partition of the free rows suffices; omitted occupied rows vanish as collisions. -/
theorem partition_column_totality {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (P M : Edges) (T B : Finset ℕ)
    (hT : T⊆Finset.Icc 1 n) (hB : B⊆Finset.Icc 1 n) (hTB : Disjoint T B)
    (hcover : ∀ i∈Finset.Icc 1 n, i∉rows P → i∈T∪B)
    (hg : P∪M ⊆ grid n m) (hd : (P∪M).card+1≤d)
    (j : ℕ) (hj : j∈Finset.Icc 1 m) (hjP : j∉cols P) :
    (∑ i ∈ T, ψ (P∪insert (i,j) M)) + (∑ i ∈ B, ψ (P∪insert (i,j) M)) = ψ (P∪M) := by
  rw [← Finset.sum_union hTB]
  have he : (∑ i ∈ T∪B, ψ (P∪insert (i,j) M)) =
      ∑ i ∈ Finset.Icc 1 n, ψ (P∪insert (i,j) M) := by
    apply Finset.sum_subset (Finset.union_subset hT hB)
    intro i hi hnot
    apply hψ.1
    apply occupied_row_collision (hj:=hjP)
    by_contra hiP
    exact hnot (hcover i hi hiP)
  rw [he]
  simpa only [Finset.union_insert] using hψ.2.2 (P∪M) hg hd j hj

/-- The actual two-family step behind the signed rewrite, with its original degree budget. -/
theorem mixed_design_step {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (hψ : IsDesign n m d ψ) (P : Edges) (T B X Y : Finset ℕ)
    (hT : T⊆Finset.Icc 1 n) (hB : B⊆Finset.Icc 1 n) (hTB : Disjoint T B)
    (hcover : ∀ i∈Finset.Icc 1 n, i∉rows P → i∈T∪B)
    (hP : P⊆grid n m) (hS : X∪Y ⊆ Finset.Icc 1 m)
    (j : ℕ) (hj : j∈Finset.Icc 1 m) (hjS : j∉X∪Y) (hjP : j∉cols P)
    (hd : P.card+(X∪Y).card+1≤d) :
    mixedSum ψ P (Finset.Icc 1 n) T B (insert j X) Y +
      mixedSum ψ P (Finset.Icc 1 n) T B X (insert j Y) =
        mixedSum ψ P (Finset.Icc 1 n) T B X Y := by
  rw [mixed_insert_left ψ hψ.1 P _ _ _ _ _ hT j hjS,
    mixed_insert_right ψ hψ.1 P _ _ _ _ _ hB j hjS,← Finset.sum_add_distrib]
  unfold mixedSum
  apply Finset.sum_congr rfl
  intro M hM
  obtain ⟨hm,hr,hc,_⟩ := (mem_maskedTerms _ _ _ _).mp hM
  apply partition_column_totality hψ P M T B hT hB hTB hcover
  · apply Finset.union_subset hP
    exact (subset_product_iff M _ _).mpr ⟨hr,hc ▸ hS⟩
  · have hcm := matching_cols_card hm
    have hu := Finset.card_union_le P M
    rw [hc] at hcm
    omega
  · exact hj
  · exact hjP

/-- A non-vacuous two-column step for the actual rectangular characteristic-two design. -/
theorem four_by_eight_mixed_step :
    mixedSum rectangle ∅ (Finset.Icc 1 4) {1,2} {3,4} (insert 3 {2}) ∅ +
      mixedSum rectangle ∅ (Finset.Icc 1 4) {1,2} {3,4} {2} {3} =
        mixedSum rectangle ∅ (Finset.Icc 1 4) {1,2} {3,4} {2} ∅ := by
  apply mixed_design_step (show IsDesign 4 8 2 rectangle from four_by_eight_design.2)
  · decide
  · decide
  · decide
  · intro i hi _
    obtain ⟨hi,hj⟩ := Finset.mem_Icc.mp hi
    interval_cases i <;> decide
  · simp
  · decide
  · decide
  · decide
  · simp [cols]
  · decide

end SelfContainedCycle056



