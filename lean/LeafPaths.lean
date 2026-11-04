import SignedExpansion

namespace SelfContainedCycle058
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037 SelfContainedCycle038
open SelfContainedCycle039 SelfContainedCycle040 SelfContainedCycle041 SelfContainedCycle042
open SelfContainedCycle043 SelfContainedCycle044 SelfContainedCycle046 SelfContainedCycle052

/-- A path with its actual terminal matching recorded. -/
def ValidLeafPath (N K : ℕ) (T : Edges) : Edges → List (Edges × ℤ) → Prop
  | R, [] => R=T ∧ chosenRewrite R=.terminal
  | R, x::xs => ChosenBranch N K R x.1 x.2 ∧ ValidLeafPath N K T x.1 xs

noncomputable def leafPaths (N K : ℕ) (T : Edges) : ℕ → Edges → Finset (List (Edges × ℤ))
  | 0,R => if chosenRewrite R=.terminal then if R=T then {[]} else ∅ else ∅
  | t+1,R => if chosenRewrite R=.terminal then if R=T then {[]} else ∅ else
      (children N K R).biUnion (fun x => (leafPaths N K T t x.1).image (List.cons x))

theorem leafPaths_terminal (N K t : ℕ) (R T : Edges) (ht : chosenRewrite R=.terminal) :
    leafPaths N K T t R = if R=T then {[]} else ∅ := by
  cases t <;> simp only [leafPaths,if_pos ht]

theorem validLeafPath_terminal (N K : ℕ) (R T : Edges) (ht : chosenRewrite R=.terminal)
    (xs : List (Edges × ℤ)) : ValidLeafPath N K T R xs ↔ R=T ∧ xs=[] := by
  cases xs with
  | nil => simp [ValidLeafPath,ht]
  | cons x xs => simp [ValidLeafPath,ChosenBranch,ht]

/-- Exact path membership with no padded terminal steps. -/
theorem mem_leafPaths_iff (N K t : ℕ) (T R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hR : R⊆grid N K) :
    xs∈leafPaths N K T t R ↔ ValidLeafPath N K T R xs ∧ xs.length≤t := by
  classical
  induction t generalizing R xs with
  | zero =>
    cases xs with
    | nil => by_cases ht : chosenRewrite R=.terminal <;> by_cases he : R=T <;>
        simp_all [leafPaths,ValidLeafPath]
    | cons x xs => by_cases ht : chosenRewrite R=.terminal <;> by_cases he : R=T <;>
        simp_all [leafPaths]
  | succ t ih =>
    by_cases ht : chosenRewrite R=.terminal
    · rw [leafPaths_terminal N K (t+1) R T ht,validLeafPath_terminal N K R T ht]
      by_cases he : R=T <;> simp [he]
      exact fun h => by subst xs; simp
    · cases xs with
      | nil => simp [leafPaths,ht,ValidLeafPath]
      | cons x xs =>
        simp only [leafPaths,if_neg ht,Finset.mem_biUnion,Finset.mem_image,
          List.cons.injEq,ValidLeafPath,List.length_cons]
        constructor
        · rintro ⟨y,hy,ys,hys,hyx,hysxs⟩
          subst y; subst ys
          have hcl := child_closed hR hy
          have hp := (ih x.1 xs hcl.1 hcl.2).mp hys
          exact ⟨⟨(mem_children_iff hR).mp hy,hp.1⟩,by omega⟩
        · rintro ⟨⟨hx,hxs⟩,hlen⟩
          have hcl := chosenBranch_closed hR hx
          exact ⟨x,(mem_children_iff hR).mpr hx,xs,
            (ih x.1 xs hcl.1 hcl.2).mpr ⟨hxs,by omega⟩,rfl,rfl⟩

theorem validLeafPath_length_le_rank {N K : ℕ} (T : Edges) (xs : List (Edges × ℤ)) (R : Edges)
    (hm : IsMatching R) (hR : R⊆grid N K) (hp : ValidLeafPath N K T R xs) :
    xs.length≤rank (grid N K) (N+K) R := by
  induction xs generalizing R with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := hp
    have hcl := chosenBranch_closed hR hx
    have hlen := ih x.1 hcl.1 hcl.2 hxs
    have hlt := chosenBranch_rank_lt hm hR hx
    simp only [List.length_cons]; omega

noncomputable def allLeafPaths (N K : ℕ) (T R : Edges) : Finset (List (Edges × ℤ)) :=
  leafPaths N K T (rank (grid N K) (N+K) R) R

theorem mem_allLeafPaths_iff {N K : ℕ} (T R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hR : R⊆grid N K) :
    xs∈allLeafPaths N K T R ↔ ValidLeafPath N K T R xs := by
  rw [allLeafPaths,mem_leafPaths_iff N K _ T R xs hm hR]
  exact ⟨And.left,fun h => ⟨h,validLeafPath_length_le_rank T xs R hm hR h⟩⟩

theorem prefixed_leafPaths_disjoint (N K t : ℕ) (T R : Edges) :
    (children N K R : Set (Edges × ℤ)).PairwiseDisjoint
      (fun x => (leafPaths N K T t x.1).image (List.cons x)) := by
  classical
  intro x hx y hy hxy
  apply Finset.disjoint_left.mpr
  intro xs hxs hys
  obtain ⟨as,_,ha⟩ := Finset.mem_image.mp hxs
  obtain ⟨bs,_,hb⟩ := Finset.mem_image.mp hys
  exact hxy (List.cons.inj (ha.trans hb.symm)).1

/-- The existing full-leaf coefficient is the actual signed path sum. -/
theorem leafTruncated_eq_path_sum (N K t : ℕ) (T R : Edges) :
    leafTruncated N K t R T = ∑ xs∈leafPaths N K T t R,pathWeight xs := by
  classical
  induction t generalizing R with
  | zero =>
    by_cases ht : chosenRewrite R=.terminal <;> by_cases he : R=T <;>
      simp_all [leafTruncated,leafPaths,pathWeight]
  | succ t ih =>
    by_cases ht : chosenRewrite R=.terminal
    · by_cases he : R=T <;> simp_all [leafTruncated,leafPaths,pathWeight]
    · rw [leafTruncated,leafPaths,if_neg ht,if_neg ht,
        Finset.sum_biUnion (prefixed_leafPaths_disjoint N K t T R)]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_image (fun a _ b _ h => (List.cons.inj h).2)]
      simp only [pathWeight]
      rw [← Finset.mul_sum,ih x.1]

theorem leafCoeff_eq_allLeafPaths_sum (N K : ℕ) (T R : Edges) :
    leafCoeff N K R T = ∑ xs∈allLeafPaths N K T R,pathWeight xs :=
  leafTruncated_eq_path_sum N K _ T R

/-- The prescribed endpoint is transported by the same embedding as every intermediate state. -/
theorem validLeafPath_compression_iff (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i≤n,f i=i)
    (hU : ∀ i,f i∈Finset.Icc 1 N' ↔ i∈Finset.Icc 1 N)
    (T : Edges) (xs : List (Edges × ℤ)) (R : Edges) (hm : IsMatching R)
    (hd : R.card≤d) (hn : 2*d≤n) :
    ValidLeafPath N' K (rowRename f T) (rowRename f R) (pathRename f xs) ↔
      ValidLeafPath N K T R xs := by
  induction xs generalizing R with
  | nil =>
    simp only [pathRename_nil,ValidLeafPath]
    rw [chosenRewrite_tail_compression f hf R n d fixOld hd hn]
    have he : rowRename f R=rowRename f T ↔ R=T :=
      (rename_injective f (Function.Embedding.refl ℕ)).eq_iff
    rw [he]
    cases chosenRewrite R <;> simp [renameChoice]
  | cons x xs ih =>
    simp only [pathRename_cons,ValidLeafPath,signedRename]
    have hb := chosenBranch_compression_iff f hf (K:=K) fixOld hU R x.1 x.2 hd hn
    constructor
    · rintro ⟨hx,hxs⟩
      have hs := hb.mp hx
      exact ⟨hs,(ih x.1 (chosenBranch_matching hs)
        ((chosenBranch_card_le hm hd hn hs).trans hd)).mp hxs⟩
    · rintro ⟨hx,hxs⟩
      exact ⟨hb.mpr hx,(ih x.1 (chosenBranch_matching hx)
        ((chosenBranch_card_le hm hd hn hx).trans hd)).mpr hxs⟩


/-- Validity is reflected by the actual inverse on all supported child states. -/
theorem validLeaf_retained_preimage (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i≤n,f i=i)
    (hU : ∀ i,f i∈Finset.Icc 1 N' ↔ i∈Finset.Icc 1 N)
    (T R : Edges) (hm : IsMatching R) (hd : R.card≤d) (hn : 2*d≤n)
    (ys : List (Edges × ℤ)) (hs : PathSupported f ys)
    (hp : ValidLeafPath N' K (rowRename f T) (rowRename f R) ys) :
    ∃ xs,pathRename f xs=ys ∧ ValidLeafPath N K T R xs := by
  obtain ⟨xs,hxs⟩ := path_supported_preimage f ys hs
  refine ⟨xs,hxs,(validLeafPath_compression_iff f hf fixOld hU T xs R hm hd hn).mp ?_⟩
  simpa only [hxs] using hp

noncomputable def leafHistoryPaths (N K n : ℕ) (T R : Edges) (S : Finset ℕ) :
    Finset (List (Edges × ℤ)) := by
  classical
  exact (allLeafPaths N K T R).filter (fun xs => pathHistory n R xs=S)

/-- Every prescribed history fiber corresponds, with the endpoint transported naturally. -/
theorem leafHistoryPaths_image_eq (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i≤n,f i=i)
    (hU : ∀ i,f i∈Finset.Icc 1 N' ↔ i∈Finset.Icc 1 N)
    (T R : Edges) (hm : IsMatching R) (hR : R⊆grid N K)
    (hd : R.card≤d) (hn : 2*d≤n) (S : Finset ℕ) :
    (leafHistoryPaths N K n T R S).image (pathRename f) =
      leafHistoryPaths N' K n (rowRename f T) (rowRename f R) (S.map f) := by
  classical
  have hm' := (matching_rename f (Function.Embedding.refl ℕ) R).mpr hm
  have hR' := rowRename_grid f hU R hR
  ext ys
  simp only [leafHistoryPaths,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨xs,⟨hx,hh⟩,rfl⟩
    refine ⟨?_,(pathHistory_exact_iff f hf n fixOld R xs S).mpr hh⟩
    apply (mem_allLeafPaths_iff _ _ _ hm' hR').mpr
    exact (validLeafPath_compression_iff f hf fixOld hU T xs R hm hd hn).mpr
      ((mem_allLeafPaths_iff T R xs hm hR).mp hx)
  · rintro ⟨hy,hh⟩
    have hs : PathSupported f ys := by
      apply history_supported_implies_pathSupported f n fixOld (rowRename f R) ys
      intro i hi
      rw [hh] at hi
      obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hi
      exact ⟨j,hj⟩
    obtain ⟨xs,hxs,hp⟩ := validLeaf_retained_preimage f hf fixOld hU T R hm hd hn ys hs
      ((mem_allLeafPaths_iff _ _ _ hm' hR').mp hy)
    refine ⟨xs,⟨(mem_allLeafPaths_iff T R xs hm hR).mpr hp,?_⟩,hxs⟩
    apply (pathHistory_exact_iff f hf n fixOld R xs S).mp
    simpa only [hxs] using hh

/-- Actual steps up to the terminal endpoint, with no assumption about empty leaves. -/
theorem validLeafPath_trajectory_steps {N K : ℕ} (T : Edges) (xs : List (Edges × ℤ)) (R : Edges)
    (hp : ValidLeafPath N K T R xs) :
    ∀ t<xs.length,∃ z,ChosenBranch N K (trajectory R xs t) (trajectory R xs (t+1)) z := by
  induction xs generalizing R with
  | nil => simp
  | cons x xs ih =>
    intro t ht
    cases t with
    | zero => exact ⟨x.2,by simpa only [trajectory_zero,trajectory_succ] using hp.1⟩
    | succ t => exact ih x.1 hp.2 t (by simpa using ht)

/-- The same persistent-token bound applies to nonempty terminal leaves. -/
theorem validLeafPath_history_bound {N K n d : ℕ} (T R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hd : R.card≤d) (hn : 2*d≤n)
    (hp : ValidLeafPath N K T R xs) : (pathHistory n R xs).card≤R.card := by
  rw [pathHistory_eq_historyRows]
  simpa only [trajectory_zero] using actual_path_history_bound (trajectory R xs)
    (by simpa only [trajectory_zero] using hm) (by simpa only [trajectory_zero] using hd) hn
    (validLeafPath_trajectory_steps T xs R hp)

theorem validLeafPath_marked_history {N K n d i j : ℕ} (T R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hd : R.card≤d) (hn : 2*d≤n)
    (hp : ValidLeafPath N K T R xs) (hi : n < i) (he : (i,j)∈R) :
    i∈pathHistory n R xs ∧ 1≤(pathHistory n R xs).card ∧ (pathHistory n R xs).card≤R.card := by
  rw [pathHistory_eq_historyRows]
  simpa only [trajectory_zero] using marked_actual_path_history_bound (trajectory R xs)
    (by simpa only [trajectory_zero] using hm) (by simpa only [trajectory_zero] using hd) hn
    (validLeafPath_trajectory_steps T xs R hp) hi (by simpa only [trajectory_zero] using he)

theorem leafPathHistory_subset {n L m : ℕ} (T : Edges) (xs : List (Edges × ℤ)) (R : Edges)
    (hR : R⊆grid (n+L) m) (hp : ValidLeafPath (n+L) m T R xs) :
    pathHistory n R xs ⊆ tailRows n L := by
  induction xs generalizing R with
  | nil => exact appended_rows_subset R hR
  | cons x xs ih =>
    exact Finset.union_subset (appended_rows_subset R hR)
      (ih x.1 (chosenBranch_closed hR hp.1).2 hp.2)

end SelfContainedCycle058
