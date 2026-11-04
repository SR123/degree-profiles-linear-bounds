import LeafPaths

namespace SelfContainedCycle058
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037 SelfContainedCycle038
open SelfContainedCycle039 SelfContainedCycle040 SelfContainedCycle041 SelfContainedCycle042
open SelfContainedCycle043 SelfContainedCycle044 SelfContainedCycle046 SelfContainedCycle052
open SelfContainedCycle053 SelfContainedCycle055 SelfContainedCycle057

/-- A finite pair retains the initial mark separately from its signed path. -/
noncomputable def markedLeafPaths (n L m : ℕ) (T R : Edges) (j : ℕ) : Finset MarkedPath := by
  classical
  exact (tailRows n L).biUnion (fun i => (allLeafPaths (n+L) m T (addEdge R i j)).image (fun xs => (i,xs)))

theorem mem_markedLeafPaths (n L m : ℕ) (T R : Edges) (j : ℕ) (v : MarkedPath) :
    v ∈ markedLeafPaths n L m T R j ↔ v.1 ∈ tailRows n L ∧ v.2 ∈ allLeafPaths (n+L) m T (addEdge R v.1 j) := by
  classical
  simp [markedLeafPaths, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff]

noncomputable def markedLeafFiber (N m n : ℕ) (T R : Edges) (j : ℕ) (S : Finset ℕ) : Finset MarkedPath := by
  classical
  exact S.biUnion (fun i => (leafHistoryPaths N m n T (addEdge R i j) S).image (fun xs => (i,xs)))

theorem mem_markedLeafFiber (N m n : ℕ) (T R : Edges) (j : ℕ) (S : Finset ℕ) (v : MarkedPath) :
    v ∈ markedLeafFiber N m n T R j S ↔ v.1 ∈ S ∧ v.2 ∈ leafHistoryPaths N m n T (addEdge R v.1 j) S := by
  classical
  simp [markedLeafFiber, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff]

/-- The mark is in the actual whole history even when its edge has been deleted. -/
theorem markedLeaf_history_properties {n L m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (v : MarkedPath) (hv : v ∈ markedLeafPaths n L m T R j) :
    v.1 ∈ markedHistory n R j v ∧ (markedHistory n R j v).Nonempty ∧
    markedHistory n R j v ⊆ tailRows n L ∧ (markedHistory n R j v).card ≤ R.card+1 := by
  obtain ⟨hi,hp⟩ := (mem_markedLeafPaths n L m T R j v).mp hv
  have hni := (Finset.mem_Icc.mp hi).1
  have hiu := new_row_unused R hR hni
  have hmi := addEdge_matching R hm hiu hju
  have hgi := addEdge_grid R hR hi hj
  have hci := addEdge_card (j:=j) R hiu
  have hvalid := (mem_allLeafPaths_iff T _ _ hmi hgi).mp hp
  have hmark := validLeafPath_marked_history T (addEdge R v.1 j) v.2 hmi (by omega) hn hvalid
    hni (Finset.mem_insert_self (v.1,j) R)
  exact ⟨hmark.1, ⟨v.1,hmark.1⟩, leafPathHistory_subset T v.2 _ hgi hvalid, by simpa only [hci] using hmark.2.2⟩

/-- For a prescribed support, the whole pair (mark,path) has an exact two-way correspondence. -/
theorem markedLeafFiber_image {n L m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hT : T ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (markedLeafFiber (n+S.card) m n T R j (tailRows n S.card)).image (markedRename (supportEmbedding S hS)) =
      markedLeafFiber (n+L) m n T R j S := by
  classical
  let f := supportEmbedding S hS
  have hfiber : ∀ i ∈ tailRows n S.card,
      (leafHistoryPaths (n+S.card) m n T (addEdge R i j) (tailRows n S.card)).image (pathRename f) =
        leafHistoryPaths (n+L) m n T (addEdge R (f i) j) S := by
    intro i hi
    have hiu := new_row_unused R hR (Finset.mem_Icc.mp hi).1
    have hmi := addEdge_matching R hm hiu hju
    have hgi := addEdge_grid R hR hi hj
    have hci := addEdge_card (j:=j) R hiu
    have h := leafHistoryPaths_image_eq f (supportMap_strictMono hS) (supportEmbedding_old S hS)
      (supportEmbedding_preimage S hS) T (addEdge R i j) hmi hgi (by omega) hn (tailRows n S.card)
    rw [addEdge_rename, old_matching_fixed S hS R hR, old_matching_fixed S hS T hT, supportEmbedding_image S hS] at h
    exact h
  ext w
  constructor
  · intro hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hi,hp⟩ := (mem_markedLeafFiber _ _ _ _ _ _ _ v).mp hv
    apply (mem_markedLeafFiber _ _ _ _ _ _ _ _).mpr
    refine ⟨?_, ?_⟩
    · have ht : f v.1 ∈ (tailRows n S.card).map f := Finset.mem_map.mpr ⟨v.1,hi,rfl⟩
      simpa only [f, supportEmbedding_image] using ht
    · change pathRename f v.2 ∈ leafHistoryPaths (n+L) m n T (addEdge R (f v.1) j) S
      rw [← hfiber v.1 hi]
      exact Finset.mem_image.mpr ⟨v.2,hp,rfl⟩
  · intro hw
    obtain ⟨hi,hp⟩ := (mem_markedLeafFiber _ _ _ _ _ _ _ w).mp hw
    rw [← supportEmbedding_image S hS] at hi
    obtain ⟨i,hi,hfi⟩ := Finset.mem_map.mp hi
    change f i = w.1 at hfi
    have hp' : w.2 ∈ leafHistoryPaths (n+L) m n T (addEdge R (f i) j) S := by simpa only [hfi] using hp
    rw [← hfiber i hi] at hp'
    obtain ⟨xs,hxs,hmap⟩ := Finset.mem_image.mp hp'
    refine Finset.mem_image.mpr ⟨(i,xs), (mem_markedLeafFiber _ _ _ _ _ _ _ _).mpr ⟨hi,hxs⟩, ?_⟩
    exact Prod.ext hfi hmap

noncomputable def markedLeafCoefficient (n m : ℕ) (T R : Edges) (j k : ℕ) : ℤ :=
  ∑ v ∈ markedLeafFiber (n+k) m n T R j (tailRows n k), markedWeight v

theorem markedLeaf_fiber_sum_by_card {n L m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hT : T ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (∑ v ∈ markedLeafFiber (n+L) m n T R j S, markedWeight v) = markedLeafCoefficient n m T R j S.card := by
  classical
  rw [← markedLeafFiber_image T R hm hR hT hj hju hd hn S hS,
    Finset.sum_image (markedRename_injective _).injOn]
  simp only [markedRename_weight]
  rfl


noncomputable def markedLeafSum (n L m : ℕ) (T R : Edges) (j : ℕ) : ℤ :=
  ∑ i ∈ tailRows n L, leafCoeff (n+L) m (addEdge R i j) T

theorem markedLeafSum_eq_pair_sum (n L m : ℕ) (T R : Edges) (j : ℕ) :
    markedLeafSum n L m T R j = ∑ v ∈ markedLeafPaths n L m T R j, markedWeight v := by
  classical
  rw [markedLeafPaths, Finset.sum_biUnion (tagged_families_disjoint _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image (fun xs _ ys _ h => (Prod.mk.inj h).2)]
  exact leafCoeff_eq_allLeafPaths_sum (n+L) m T (addEdge R i j)

theorem markedLeafHistory_mem_histories {n L m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (v : MarkedPath) (hv : v ∈ markedLeafPaths n L m T R j) :
    markedHistory n R j v ∈ histories n L D := by
  have hp := markedLeaf_history_properties T R hm hR hj hju hd hn v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hp.2.2.1,hp.2.2.2.trans hd⟩

/-- Exact history partition of marked pairs, deriving membership of the initial mark in S. -/
theorem markedLeafFiber_eq_filter {n L m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (markedLeafPaths n L m T R j).filter (fun v => markedHistory n R j v = S) =
      markedLeafFiber (n+L) m n T R j S := by
  classical
  ext v
  simp only [Finset.mem_filter, mem_markedLeafFiber, leafHistoryPaths, Finset.mem_filter]
  constructor
  · rintro ⟨hv,hh⟩
    have hmark := (markedLeaf_history_properties T R hm hR hj hju hd hn v hv).1
    rw [hh] at hmark
    exact ⟨hmark, (mem_markedLeafPaths n L m T R j v).mp hv |>.2, hh⟩
  · rintro ⟨hi,hp,hh⟩
    exact ⟨(mem_markedLeafPaths n L m T R j v).mpr ⟨hS hi,hp⟩,hh⟩

/-- The actual marked sum is grouped by the complete history, never the final state. -/
theorem markedLeafSum_eq_history_sum {n L m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hT : T ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) :
    markedLeafSum n L m T R j = ∑ S ∈ histories n L D, markedLeafCoefficient n m T R j S.card := by
  classical
  rw [markedLeafSum_eq_pair_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (markedLeafHistory_mem_histories (L:=L) T R hm hR hj hju hd hn) markedWeight]
  apply Finset.sum_congr rfl
  intro S hS
  have hs := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  rw [markedLeafFiber_eq_filter T R hm hR hj hju hd hn S hs]
  exact markedLeaf_fiber_sum_by_card T R hm hR hT hj hju hd hn S hs

@[simp] theorem markedLeafCoefficient_zero (n m : ℕ) (T R : Edges) (j : ℕ) :
    markedLeafCoefficient n m T R j 0 = 0 := by
  simp [markedLeafCoefficient, markedLeafFiber]

/-- Integral marked binomial identity with explicitly constructed coefficients. -/
theorem markedLeaf_binomial_range {n m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hT : T ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (L : ℕ) :
    markedLeafSum n L m T R j = ∑ k ∈ Finset.range (D+1), (L.choose k : ℤ) * markedLeafCoefficient n m T R j k := by
  rw [markedLeafSum_eq_history_sum T R hm hR hT hj hju hd hn, sum_histories_by_card]


/-- Explicit double-sum presentation of the coefficients, with the distinguished label retained. -/
theorem markedLeafCoefficient_eq_double_sum (n m : ℕ) (T R : Edges) (j k : ℕ) :
    markedLeafCoefficient n m T R j k = ∑ i ∈ tailRows n k,
      ∑ xs ∈ leafHistoryPaths (n+k) m n T (addEdge R i j) (tailRows n k), pathWeight xs := by
  classical
  rw [markedLeafCoefficient, markedLeafFiber, Finset.sum_biUnion (tagged_families_disjoint _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image (fun xs _ ys _ h => (Prod.mk.inj h).2)]
  rfl

/-- The constant term is removed explicitly, not left as an unproved marked premise. -/
theorem markedLeaf_binomial_positive {n m D j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hT : T ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (L : ℕ) :
    markedLeafSum n L m T R j = ∑ k ∈ Finset.Icc 1 D, (L.choose k : ℤ) * markedLeafCoefficient n m T R j k := by
  classical
  rw [markedLeaf_binomial_range T R hm hR hT hj hju hd hn L]
  symm
  apply Finset.sum_subset
  · intro k hk
    have hb := Finset.mem_Icc.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro k hk hnot
    have hb := Finset.mem_range.mp hk
    have hk0 : k = 0 := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    simp [hk0]

/-- The exact input-cardinality version of the marked integral identity. -/
theorem markedLeaf_binomial {n m j : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hT : T ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hn : 2*(R.card+1) ≤ n) (L : ℕ) :
    markedLeafSum n L m T R j = ∑ k ∈ Finset.Icc 1 (R.card+1),
      (L.choose k : ℤ) * markedLeafCoefficient n m T R j k :=
  markedLeaf_binomial_positive T R hm hR hT hj hju le_rfl hn L

/-- The marked polynomial degree is at most the number of initial tokens, |R|+1. -/
theorem markedLeafCoefficient_gt_degree {n m D j k : ℕ} (T R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (hk : R.card+1 < k) :
    markedLeafCoefficient n m T R j k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro v hv
  obtain ⟨hi,hp⟩ := (mem_markedLeafFiber _ _ _ _ _ _ _ v).mp hv
  obtain ⟨hall,hh⟩ := Finset.mem_filter.mp hp
  have hv' := (mem_markedLeafPaths n k m T R j v).mpr ⟨hi,hall⟩
  have hc := (markedLeaf_history_properties T R hm hR hj hju hd hn v hv').2.2.2
  change (pathHistory n (addEdge R v.1 j) v.2).card ≤ R.card+1 at hc
  rw [hh,tailRows_card] at hc
  omega

@[simp] theorem markedLeafSum_zero (n m : ℕ) (T R : Edges) (j : ℕ) : markedLeafSum n 0 m T R j = 0 := by
  simp [markedLeafSum]



/-- Positive-support binomial coefficients vanish in the exact characteristic range. -/
theorem markedLeafSum_char_zero {F : Type*} [CommRing F] {p a n L m D j : ℕ}
    (hp : p.Prime) [CharP F p] (T R : Edges) (hm : IsMatching R)
    (hR : R⊆grid n m) (hT : T⊆grid n m) (hj : j∈Finset.Icc 1 m) (hju : j∉cols R)
    (hd : R.card+1≤D) (hn : 2*D≤n) (hdq : D < p^a) (hdiv : p^a∣L) :
    (∑ i∈tailRows n L,(leafCoeff (n+L) m (addEdge R i j) T:F))=0 := by
  have h : (markedLeafSum n L m T R j:F)=0 := by
    rw [markedLeaf_binomial_positive T R hm hR hT hj hju hd hn L]
    push_cast
    apply Finset.sum_eq_zero
    intro k hk
    obtain ⟨hk0,hkD⟩ := Finset.mem_Icc.mp hk
    rw [choose_cast_eq_zero hp hdiv hk0 (hkD.trans_lt hdq),zero_mul]
  simpa only [markedLeafSum,Int.cast_sum] using h

/-- All omitted-row terms cancel for each old square coordinate, including collision cases. -/
theorem squareLeaf_appended_sum_zero {F : Type*} [CommRing F] {p a n m D j : ℕ}
    (hp : p.Prime) [CharP F p] (T P : Edges) (hP : P⊆grid n m) (hT : T⊆grid n m)
    (hj : j∈Finset.Icc 1 m) (hd : P.card+1≤D) (hn : 2*D≤n)
    (hdq : D < p^a) (hnm : n≤m) (hdiv : p^a∣m-n) :
    (∑ i∈Finset.Icc (n+1) m,(squareLeafCoeff m (insert (i,j) P) T:F))=0 := by
  by_cases hm : IsMatching P
  · by_cases hjused : j∈cols P
    · apply Finset.sum_eq_zero
      intro i hi
      rw [squareLeafCoeff_collision (appended_occupied_collision P hP
        (by have := (Finset.mem_Icc.mp hi).1; omega) hjused) T,Int.cast_zero]
    · have hs := markedLeafSum_char_zero (F:=F) hp T P hm hP hT hj hjused hd hn hdq hdiv
      simp only [tailRows,Nat.add_sub_of_le hnm,addEdge] at hs
      change (∑ i∈Finset.Icc (n+1) m,(leafCoeff m m (insert (i,j) P) T:F))=0 at hs
      convert hs using 1
      apply Finset.sum_congr rfl
      intro i hi
      have hmi : IsMatching (insert (i,j) P) := addEdge_matching (i:=i) P hm
        (new_row_unused (i:=i) P hP (by have := (Finset.mem_Icc.mp hi).1; omega)) hjused
      exact congrArg (fun z:ℤ => (z:F)) (squareLeafCoeff_matching hmi T)
  · apply Finset.sum_eq_zero
    intro i _
    rw [squareLeafCoeff_collision (nonmatching_insert hm (i,j)) T,Int.cast_zero]

/-- Every old terminal square coordinate restricts to an actual rectangular design. -/
theorem squareLeaf_rectangular_design {F : Type*} [CommRing F] {p a n m D : ℕ}
    (hp : p.Prime) [CharP F p] (hn : 2*D≤n) (hdq : D < p^a) (hnm : n≤m)
    (hdiv : p^a∣m-n) (T : Edges) (hT : T∈terminalFamily n m) :
    IsDesign n m D (fun P => (squareLeafCoeff m P T:F)) := by
  obtain ⟨hTg,hTm,hTt⟩ := (mem_terminalFamily _ _ _).mp hT
  have hTs : T∈terminalFamily m m :=
    (mem_terminalFamily _ _ _).mpr ⟨hTg.trans (grid_into_square hnm),hTm,hTt⟩
  refine ⟨?_,?_,?_⟩
  · intro P hm; dsimp only; rw [squareLeafCoeff_collision hm T,Int.cast_zero]
  · intro P hP _ i hi
    have him : i∈Finset.Icc 1 m := by
      obtain ⟨hil,hih⟩ := Finset.mem_Icc.mp hi
      exact Finset.mem_Icc.mpr ⟨hil,hih.trans hnm⟩
    have hs := squareLeafCoeff_row_sum P (hP.trans (grid_into_square hnm)) him T hTs
    have hcast := congrArg (fun z:ℤ => (z:F)) hs
    simpa only [Int.cast_sum] using hcast
  · intro P hP hd j hj
    have hs := squareLeafCoeff_col_sum P (hP.trans (grid_into_square hnm)) hj T hTs
    have hcast := congrArg (fun z:ℤ => (z:F)) hs
    push_cast at hcast
    rw [← row_interval_partition hnm,Finset.sum_union (row_intervals_disjoint n m),
      squareLeaf_appended_sum_zero hp T P hP hTg hj hd hn hdq hnm hdiv,add_zero] at hcast
    exact hcast

end SelfContainedCycle058
