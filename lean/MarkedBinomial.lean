import SupportEmbedding

namespace SelfContainedCycle043
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle039 SelfContainedCycle040
open SelfContainedCycle041 SelfContainedCycle042

abbrev SignedPath := List (Edges × ℤ)
abbrev MarkedPath := ℕ × SignedPath

def addEdge (R : Edges) (i j : ℕ) : Edges := insert (i,j) R

theorem new_row_unused {n m i : ℕ} (R : Edges) (hR : R ⊆ grid n m) (hi : n < i) :
    i ∉ rows R := by
  intro h
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp h
  have hu := (Finset.mem_Icc.mp (Finset.mem_product.mp (hR he)).1).2
  omega

theorem addEdge_matching {i j : ℕ} (R : Edges) (hm : IsMatching R)
    (hi : i ∉ rows R) (hj : j ∉ cols R) : IsMatching (addEdge R i j) := by
  intro e he e' he' hc
  rcases Finset.mem_insert.mp he with he | he <;> rcases Finset.mem_insert.mp he' with he' | he'
  · exact he.trans he'.symm
  · subst e
    rcases hc with hc | hc
    · exact (hi (Finset.mem_image.mpr ⟨e',he',hc.symm⟩)).elim
    · exact (hj (Finset.mem_image.mpr ⟨e',he',hc.symm⟩)).elim
  · subst e'
    rcases hc with hc | hc
    · exact (hi (Finset.mem_image.mpr ⟨e,he,hc⟩)).elim
    · exact (hj (Finset.mem_image.mpr ⟨e,he,hc⟩)).elim
  · exact hm e he e' he' hc

theorem addEdge_card {i j : ℕ} (R : Edges) (hi : i ∉ rows R) :
    (addEdge R i j).card = R.card+1 := by
  apply Finset.card_insert_of_notMem
  intro h
  exact hi (Finset.mem_image.mpr ⟨(i,j),h,rfl⟩)

theorem addEdge_grid {n L m i j : ℕ} (R : Edges) (hR : R ⊆ grid n m)
    (hi : i ∈ tailRows n L) (hj : j ∈ Finset.Icc 1 m) :
    addEdge R i j ⊆ grid (n+L) m := by
  intro e he
  rcases Finset.mem_insert.mp he with he | he
  · subst e
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hhi⟩,hj⟩
  · exact hR.trans (grid_row_mono (Nat.le_add_right n L)) he

theorem addEdge_rename (f : ℕ ↪ ℕ) (R : Edges) (i j : ℕ) :
    rowRename f (addEdge R i j) = addEdge (rowRename f R) (f i) j := by
  simp [addEdge, rowRename, rename, edgeEmbedding]

/-- A finite pair retains the initial mark separately from its signed path. -/
noncomputable def markedPaths (n L m : ℕ) (R : Edges) (j : ℕ) : Finset MarkedPath := by
  classical
  exact (tailRows n L).biUnion (fun i => (allPaths (n+L) m (addEdge R i j)).image (fun xs => (i,xs)))

theorem mem_markedPaths (n L m : ℕ) (R : Edges) (j : ℕ) (v : MarkedPath) :
    v ∈ markedPaths n L m R j ↔ v.1 ∈ tailRows n L ∧ v.2 ∈ allPaths (n+L) m (addEdge R v.1 j) := by
  classical
  simp [markedPaths, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff]

noncomputable def markedFiber (N m n : ℕ) (R : Edges) (j : ℕ) (S : Finset ℕ) : Finset MarkedPath := by
  classical
  exact S.biUnion (fun i => (historyPaths N m n (addEdge R i j) S).image (fun xs => (i,xs)))

theorem mem_markedFiber (N m n : ℕ) (R : Edges) (j : ℕ) (S : Finset ℕ) (v : MarkedPath) :
    v ∈ markedFiber N m n R j S ↔ v.1 ∈ S ∧ v.2 ∈ historyPaths N m n (addEdge R v.1 j) S := by
  classical
  simp [markedFiber, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff]

def markedHistory (n : ℕ) (R : Edges) (j : ℕ) (v : MarkedPath) : Finset ℕ :=
  pathHistory n (addEdge R v.1 j) v.2

def markedWeight (v : MarkedPath) : ℤ := pathWeight v.2

/-- The mark is in the actual whole history even when its edge has been deleted. -/
theorem marked_history_properties {n L m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (v : MarkedPath) (hv : v ∈ markedPaths n L m R j) :
    v.1 ∈ markedHistory n R j v ∧ (markedHistory n R j v).Nonempty ∧
    markedHistory n R j v ⊆ tailRows n L ∧ (markedHistory n R j v).card ≤ R.card+1 := by
  obtain ⟨hi,hp⟩ := (mem_markedPaths n L m R j v).mp hv
  have hni := (Finset.mem_Icc.mp hi).1
  have hiu := new_row_unused R hR hni
  have hmi := addEdge_matching R hm hiu hju
  have hgi := addEdge_grid R hR hi hj
  have hci := addEdge_card (j:=j) R hiu
  have hvalid := (mem_allPaths_iff _ _ hmi hgi).mp hp
  have hmark := validPath_marked_history (addEdge R v.1 j) v.2 hmi (by omega) hn hvalid
    hni (Finset.mem_insert_self (v.1,j) R)
  exact ⟨hmark.1, ⟨v.1,hmark.1⟩, pathHistory_subset v.2 _ hgi hvalid, by simpa only [hci] using hmark.2.2⟩

def markedRename (f : ℕ ↪ ℕ) (v : MarkedPath) : MarkedPath := (f v.1, pathRename f v.2)

theorem markedRename_injective (f : ℕ ↪ ℕ) : Function.Injective (markedRename f) := by
  intro v w h
  apply Prod.ext
  · exact f.injective (congrArg Prod.fst h)
  · have hs := congrArg Prod.snd h
    exact pathRename_injective f hs

@[simp] theorem markedRename_weight (f : ℕ ↪ ℕ) (v : MarkedPath) :
    markedWeight (markedRename f v) = markedWeight v := pathRename_weight f v.2

/-- For a prescribed support, the whole pair (mark,path) has an exact two-way correspondence. -/
theorem markedFiber_image {n L m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (markedFiber (n+S.card) m n R j (tailRows n S.card)).image (markedRename (supportEmbedding S hS)) =
      markedFiber (n+L) m n R j S := by
  classical
  let f := supportEmbedding S hS
  have hfiber : ∀ i ∈ tailRows n S.card,
      (historyPaths (n+S.card) m n (addEdge R i j) (tailRows n S.card)).image (pathRename f) =
        historyPaths (n+L) m n (addEdge R (f i) j) S := by
    intro i hi
    have hiu := new_row_unused R hR (Finset.mem_Icc.mp hi).1
    have hmi := addEdge_matching R hm hiu hju
    have hgi := addEdge_grid R hR hi hj
    have hci := addEdge_card (j:=j) R hiu
    have h := historyPaths_image_eq f (supportMap_strictMono hS) (supportEmbedding_old S hS)
      (supportEmbedding_preimage S hS) (addEdge R i j) hmi hgi (by omega) hn (tailRows n S.card)
    rw [addEdge_rename, old_matching_fixed S hS R hR, supportEmbedding_image S hS] at h
    exact h
  ext w
  constructor
  · intro hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hi,hp⟩ := (mem_markedFiber _ _ _ _ _ _ v).mp hv
    apply (mem_markedFiber _ _ _ _ _ _ _).mpr
    refine ⟨?_, ?_⟩
    · have ht : f v.1 ∈ (tailRows n S.card).map f := Finset.mem_map.mpr ⟨v.1,hi,rfl⟩
      simpa only [f, supportEmbedding_image] using ht
    · change pathRename f v.2 ∈ historyPaths (n+L) m n (addEdge R (f v.1) j) S
      rw [← hfiber v.1 hi]
      exact Finset.mem_image.mpr ⟨v.2,hp,rfl⟩
  · intro hw
    obtain ⟨hi,hp⟩ := (mem_markedFiber _ _ _ _ _ _ w).mp hw
    rw [← supportEmbedding_image S hS] at hi
    obtain ⟨i,hi,hfi⟩ := Finset.mem_map.mp hi
    change f i = w.1 at hfi
    have hp' : w.2 ∈ historyPaths (n+L) m n (addEdge R (f i) j) S := by simpa only [hfi] using hp
    rw [← hfiber i hi] at hp'
    obtain ⟨xs,hxs,hmap⟩ := Finset.mem_image.mp hp'
    refine Finset.mem_image.mpr ⟨(i,xs), (mem_markedFiber _ _ _ _ _ _ _).mpr ⟨hi,hxs⟩, ?_⟩
    exact Prod.ext hfi hmap

noncomputable def markedCoefficient (n m : ℕ) (R : Edges) (j k : ℕ) : ℤ :=
  ∑ v ∈ markedFiber (n+k) m n R j (tailRows n k), markedWeight v

theorem marked_fiber_sum_by_card {n L m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (∑ v ∈ markedFiber (n+L) m n R j S, markedWeight v) = markedCoefficient n m R j S.card := by
  classical
  rw [← markedFiber_image R hm hR hj hju hd hn S hS,
    Finset.sum_image (markedRename_injective _).injOn]
  simp only [markedRename_weight]
  rfl


/-- Keeping the mark in the pair prevents duplicate loss in the finite union. -/
theorem tagged_families_disjoint (A : Finset ℕ) (P : ℕ → Finset SignedPath) :
    (A : Set ℕ).PairwiseDisjoint (fun i => (P i).image (fun xs => (i,xs))) := by
  classical
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨xs,_,hxs⟩ := Finset.mem_image.mp hvi
  obtain ⟨ys,_,hys⟩ := Finset.mem_image.mp hvj
  exact hij (congrArg Prod.fst (hxs.trans hys.symm))

noncomputable def markedSum (n L m : ℕ) (R : Edges) (j : ℕ) : ℤ :=
  ∑ i ∈ tailRows n L, normalizer (n+L) m (addEdge R i j)

theorem markedSum_eq_pair_sum (n L m : ℕ) (R : Edges) (j : ℕ) :
    markedSum n L m R j = ∑ v ∈ markedPaths n L m R j, markedWeight v := by
  classical
  rw [markedPaths, Finset.sum_biUnion (tagged_families_disjoint _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image (fun xs _ ys _ h => (Prod.mk.inj h).2)]
  exact normalizer_eq_allPaths_sum (n+L) m (addEdge R i j)

theorem markedHistory_mem_histories {n L m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (v : MarkedPath) (hv : v ∈ markedPaths n L m R j) :
    markedHistory n R j v ∈ histories n L D := by
  have hp := marked_history_properties R hm hR hj hju hd hn v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hp.2.2.1,hp.2.2.2.trans hd⟩

/-- Exact history partition of marked pairs, deriving membership of the initial mark in S. -/
theorem markedFiber_eq_filter {n L m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (S : Finset ℕ) (hS : S ⊆ tailRows n L) :
    (markedPaths n L m R j).filter (fun v => markedHistory n R j v = S) =
      markedFiber (n+L) m n R j S := by
  classical
  ext v
  simp only [Finset.mem_filter, mem_markedFiber, historyPaths, Finset.mem_filter]
  constructor
  · rintro ⟨hv,hh⟩
    have hmark := (marked_history_properties R hm hR hj hju hd hn v hv).1
    rw [hh] at hmark
    exact ⟨hmark, (mem_markedPaths n L m R j v).mp hv |>.2, hh⟩
  · rintro ⟨hi,hp,hh⟩
    exact ⟨(mem_markedPaths n L m R j v).mpr ⟨hS hi,hp⟩,hh⟩

/-- The actual marked sum is grouped by the complete history, never the final state. -/
theorem markedSum_eq_history_sum {n L m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) :
    markedSum n L m R j = ∑ S ∈ histories n L D, markedCoefficient n m R j S.card := by
  classical
  rw [markedSum_eq_pair_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (markedHistory_mem_histories (L:=L) R hm hR hj hju hd hn) markedWeight]
  apply Finset.sum_congr rfl
  intro S hS
  have hs := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  rw [markedFiber_eq_filter R hm hR hj hju hd hn S hs]
  exact marked_fiber_sum_by_card R hm hR hj hju hd hn S hs

@[simp] theorem markedCoefficient_zero (n m : ℕ) (R : Edges) (j : ℕ) :
    markedCoefficient n m R j 0 = 0 := by
  simp [markedCoefficient, markedFiber]

/-- Integral marked binomial identity with explicitly constructed coefficients. -/
theorem marked_binomial_range {n m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (L : ℕ) :
    markedSum n L m R j = ∑ k ∈ Finset.range (D+1), (L.choose k : ℤ) * markedCoefficient n m R j k := by
  rw [markedSum_eq_history_sum R hm hR hj hju hd hn, sum_histories_by_card]


/-- Explicit double-sum presentation of the coefficients, with the distinguished label retained. -/
theorem markedCoefficient_eq_double_sum (n m : ℕ) (R : Edges) (j k : ℕ) :
    markedCoefficient n m R j k = ∑ i ∈ tailRows n k,
      ∑ xs ∈ historyPaths (n+k) m n (addEdge R i j) (tailRows n k), pathWeight xs := by
  classical
  rw [markedCoefficient, markedFiber, Finset.sum_biUnion (tagged_families_disjoint _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image (fun xs _ ys _ h => (Prod.mk.inj h).2)]
  rfl

/-- The constant term is removed explicitly, not left as an unproved marked premise. -/
theorem marked_binomial_positive {n m D j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (L : ℕ) :
    markedSum n L m R j = ∑ k ∈ Finset.Icc 1 D, (L.choose k : ℤ) * markedCoefficient n m R j k := by
  classical
  rw [marked_binomial_range R hm hR hj hju hd hn L]
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
theorem marked_binomial {n m j : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hn : 2*(R.card+1) ≤ n) (L : ℕ) :
    markedSum n L m R j = ∑ k ∈ Finset.Icc 1 (R.card+1),
      (L.choose k : ℤ) * markedCoefficient n m R j k :=
  marked_binomial_positive R hm hR hj hju le_rfl hn L

/-- The marked polynomial degree is at most the number of initial tokens, |R|+1. -/
theorem markedCoefficient_gt_degree {n m D j k : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid n m) (hj : j ∈ Finset.Icc 1 m) (hju : j ∉ cols R)
    (hd : R.card+1 ≤ D) (hn : 2*D ≤ n) (hk : R.card+1 < k) :
    markedCoefficient n m R j k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro v hv
  obtain ⟨hi,hp⟩ := (mem_markedFiber _ _ _ _ _ _ v).mp hv
  obtain ⟨hall,hh⟩ := Finset.mem_filter.mp hp
  have hv' := (mem_markedPaths n k m R j v).mpr ⟨hi,hall⟩
  have hc := (marked_history_properties R hm hR hj hju hd hn v hv').2.2.2
  change (pathHistory n (addEdge R v.1 j) v.2).card ≤ R.card+1 at hc
  rw [hh,tailRows_card] at hc
  omega

@[simp] theorem markedSum_zero (n m : ℕ) (R : Edges) (j : ℕ) : markedSum n 0 m R j = 0 := by
  simp [markedSum]

/-- A real marked path deletes its distinguished edge on its first step. -/
theorem marked_deletion_valid : ValidPath 5 2 (addEdge ∅ 5 1) [(∅,1)] := by
  change ValidPath 5 2 {(5,1)} [(∅,1)]
  constructor
  · rw [ChosenBranch, chosen_five_singleton]
    unfold ColumnBranch
    refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide
  · rfl

attribute [local irreducible] allPaths markedPaths markedFiber

theorem marked_deletion_member : ((5,[(∅,1)]) : MarkedPath) ∈ markedPaths 4 1 2 ∅ 1 := by
  apply (mem_markedPaths 4 1 2 ∅ 1 _).mpr
  refine ⟨by decide, ?_⟩
  exact (mem_allPaths_iff (N:=5) (K:=2) (addEdge ∅ 5 1) [(∅,1)] (by decide) (by decide)).mpr marked_deletion_valid

theorem marked_deletion_history :
    markedHistory 4 ∅ 1 (5,[(∅,1)]) = {5} ∧ markedWeight (5,[(∅,1)]) = 1 := by decide

theorem marked_deletion_fiber : ((5,[(∅,1)]) : MarkedPath) ∈ markedFiber 5 2 4 ∅ 1 {5} := by
  apply (mem_markedFiber 5 2 4 ∅ 1 {5} _).mpr
  refine ⟨by simp, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨(mem_markedPaths 4 1 2 ∅ 1 _).mp marked_deletion_member |>.2, marked_deletion_history.1⟩

/-- Nonempty old matching, unused column, and a universal appended-size instance. -/
theorem nonempty_marked_identity_all_L (L : ℕ) :
    markedSum 4 L 2 {(1,1)} 2 = (L:ℤ) * markedCoefficient 4 2 {(1,1)} 2 1 +
      (L.choose 2 : ℤ) * markedCoefficient 4 2 {(1,1)} 2 2 := by
  have h := marked_binomial_range (n:=4) (m:=2) (D:=2) (j:=2) {(1,1)}
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) L
  simpa [Finset.sum_range_succ] using h


/-- Compression changes the retained initial mark even when the path itself immediately becomes empty. -/
theorem marked_deletion_compressed : ((6,[(∅,1)]) : MarkedPath) ∈ markedFiber 7 2 4 ∅ 1 {6} := by
  let hs : ({6}:Finset ℕ) ⊆ tailRows 4 3 := by decide
  let f := supportEmbedding {6} hs
  have h5 : f 5 = 6 := by
    have hi : 5 ∈ tailRows 4 ({6}:Finset ℕ).card := by decide
    have him : f 5 ∈ (tailRows 4 ({6}:Finset ℕ).card).map f := Finset.mem_map.mpr ⟨5,hi,rfl⟩
    have hm : f 5 ∈ ({6}:Finset ℕ) := by simpa only [f, supportEmbedding_image] using him
    exact Finset.mem_singleton.mp hm
  have hv : markedRename f (5,[(∅,1)]) = (6,[(∅,1)]) := by
    simp [markedRename, pathRename, signedRename, rowRename, rename, h5]
  have heq := markedFiber_image (n:=4) (L:=3) (m:=2) (D:=1) (j:=1) ∅
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) {6} hs
  have hmem : markedRename f (5,[(∅,1)]) ∈
      (markedFiber 5 2 4 ∅ 1 {5}).image (markedRename f) :=
    Finset.mem_image.mpr ⟨(5,[(∅,1)]),marked_deletion_fiber,rfl⟩
  have hdom : tailRows 4 ({6}:Finset ℕ).card = {5} := by decide
  rw [hdom] at heq
  change (markedFiber 5 2 4 ∅ 1 {5}).image (markedRename f) =
    markedFiber 7 2 4 ∅ 1 {6} at heq
  rw [heq] at hmem
  simpa only [hv] using hmem

end SelfContainedCycle043
