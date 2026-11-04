import SignedNormalizer

namespace SelfContainedCycle041
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle039 SelfContainedCycle040

abbrev rowRename (f : ℕ ↪ ℕ) (R : Edges) : Edges :=
  rename f (Function.Embedding.refl ℕ) R

theorem rename_sdiff (f g : ℕ ↪ ℕ) (R C : Edges) :
    rename f g (R \ C) = rename f g R \ rename f g C := Finset.map_sdiff _ _

theorem chosen_row_fails {R C : Edges} {a : ℕ}
    (h : chosenRewrite R = .row a C) : RowFails R a := by
  unfold chosenRewrite at h
  split_ifs at h with hr hc
  · cases h; exact (min_row_failure_is_first R hr).1

/-- The actual selector and both actual signed branch formulas commute. -/
theorem chosenBranch_compression_iff (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i ≤ n, f i = i)
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (R Q : Edges) (z : ℤ) (hd : R.card ≤ d) (hn : 2*d ≤ n) :
    ChosenBranch N' K (rowRename f R) (rowRename f Q) z ↔ ChosenBranch N K R Q z := by
  unfold ChosenBranch
  rw [chosenRewrite_tail_compression f hf R n d fixOld hd hn]
  cases hc : chosenRewrite R with
  | row a C =>
    have ha : f a = a := fixOld a (Nat.le_of_lt (rowFails_old (chosen_row_fails hc) hd hn))
    simp only [renameChoice]
    rw [← rename_sdiff]
    simpa only [ha] using supplied_chain_branch_iff f (Function.Embedding.refl ℕ)
      (Finset.Icc 1 N) (Finset.Icc 1 N') R (R \ C) C Q a z hf hU
  | column a C =>
    simp only [renameChoice]
    rw [← rename_sdiff]
    simpa [freeBefore, targetRows, transpose_rename, rows_rename] using
      columnBranch_row_compression f (R \ C) C Q
        (freeBefore (Finset.Icc 1 K) (transpose R) a)
        (targetRows (Finset.Icc 1 K) (transpose R) (transpose C) a) z
  | terminal => rfl

theorem chosenBranch_card_le {N K n d : ℕ} {R Q : Edges} {z : ℤ}
    (hm : IsMatching R) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (hb : ChosenBranch N K R Q z) : Q.card ≤ R.card :=
  represented_card_le (chosenBranch_tokens (initialTokens R)
    (initialTokens_represents R) hm hd hn hb).1

def signedRename (f : ℕ ↪ ℕ) (x : Edges × ℤ) : Edges × ℤ := (rowRename f x.1, x.2)
def pathRename (f : ℕ ↪ ℕ) (xs : List (Edges × ℤ)) : List (Edges × ℤ) := xs.map (signedRename f)

@[simp] theorem pathRename_nil (f : ℕ ↪ ℕ) : pathRename f [] = [] := rfl
@[simp] theorem pathRename_cons (f : ℕ ↪ ℕ) (x : Edges × ℤ) (xs : List (Edges × ℤ)) :
    pathRename f (x::xs) = signedRename f x :: pathRename f xs := rfl

@[simp] theorem pathRename_length (f : ℕ ↪ ℕ) (xs : List (Edges × ℤ)) :
    (pathRename f xs).length = xs.length := List.length_map _

@[simp] theorem pathRename_weight (f : ℕ ↪ ℕ) (xs : List (Edges × ℤ)) :
    pathWeight (pathRename f xs) = pathWeight xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [pathRename_cons, pathWeight, signedRename, ih]

theorem signedRename_injective (f : ℕ ↪ ℕ) : Function.Injective (signedRename f) := by
  intro x y h
  apply Prod.ext
  · exact rename_injective f (Function.Embedding.refl ℕ) (congrArg Prod.fst h)
  · have hs := congrArg Prod.snd h
    exact hs

theorem pathRename_injective (f : ℕ ↪ ℕ) : Function.Injective (pathRename f) :=
  List.map_injective_iff.mpr (signedRename_injective f)

/-- Degree control is derived at every intermediate child; no path invariant is assumed. -/
theorem validPath_compression_iff (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i ≤ n, f i = i)
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (xs : List (Edges × ℤ)) (R : Edges) (hm : IsMatching R)
    (hd : R.card ≤ d) (hn : 2*d ≤ n) :
    ValidPath N' K (rowRename f R) (pathRename f xs) ↔ ValidPath N K R xs := by
  induction xs generalizing R with
  | nil => simp [ValidPath, rename]
  | cons x xs ih =>
    simp only [pathRename_cons, ValidPath, signedRename]
    have hb := chosenBranch_compression_iff f hf (K:=K) fixOld hU R x.1 x.2 hd hn
    constructor
    · rintro ⟨hx, hxs⟩
      have hs := hb.mp hx
      have hmQ := chosenBranch_matching hs
      have hdQ := (chosenBranch_card_le hm hd hn hs).trans hd
      exact ⟨hs, (ih x.1 hmQ hdQ).mp hxs⟩
    · rintro ⟨hx, hxs⟩
      have hmQ := chosenBranch_matching hx
      have hdQ := (chosenBranch_card_le hm hd hn hx).trans hd
      exact ⟨hb.mpr hx, (ih x.1 hmQ hdQ).mpr hxs⟩

def RowSupported (f : ℕ ↪ ℕ) (Q : Edges) : Prop := ∀ e ∈ Q, e.1 ∈ Set.range f

def PathSupported (f : ℕ ↪ ℕ) (xs : List (Edges × ℤ)) : Prop :=
  ∀ x ∈ xs, RowSupported f x.1

theorem rowRename_supported (f : ℕ ↪ ℕ) (R : Edges) : RowSupported f (rowRename f R) := by
  intro e he
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp he
  exact ⟨x.1, rfl⟩

theorem row_supported_preimage (f : ℕ ↪ ℕ) (Q : Edges) (hQ : RowSupported f Q) :
    ∃ R, rowRename f R = Q := by
  apply exists_rename_of_supported
  intro e he
  exact ⟨hQ e he, ⟨e.2, rfl⟩⟩

theorem pathRename_supported (f : ℕ ↪ ℕ) (xs : List (Edges × ℤ)) :
    PathSupported f (pathRename f xs) := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact rowRename_supported f y.1

/-- Preimages are obtained for every supported intermediate state, including ones later deleted. -/
theorem path_supported_preimage (f : ℕ ↪ ℕ) (ys : List (Edges × ℤ))
    (hs : PathSupported f ys) : ∃ xs, pathRename f xs = ys := by
  induction ys with
  | nil => exact ⟨[], rfl⟩
  | cons y ys ih =>
    obtain ⟨R, hR⟩ := row_supported_preimage f y.1 (hs y (by simp))
    obtain ⟨xs, hxs⟩ := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    refine ⟨(R,y.2)::xs, ?_⟩
    simp only [pathRename_cons, signedRename, hR, hxs, Prod.mk.eta]

theorem rowRename_grid (f : ℕ ↪ ℕ) {N N' K : ℕ}
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (R : Edges) (hR : R ⊆ grid N K) : rowRename f R ⊆ grid N' K := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
  have hG := Finset.mem_product.mp (hR hx)
  exact Finset.mem_product.mpr ⟨(hU x.1).mpr hG.1, hG.2⟩

/-- Surjectivity reflects actual validity, rather than merely producing a supported list. -/
theorem valid_retained_preimage (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i ≤ n, f i = i)
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (ys : List (Edges × ℤ)) (hs : PathSupported f ys)
    (hp : ValidPath N' K (rowRename f R) ys) :
    ∃ xs, pathRename f xs = ys ∧ ValidPath N K R xs := by
  obtain ⟨xs, hxs⟩ := path_supported_preimage f ys hs
  refine ⟨xs, hxs, (validPath_compression_iff f hf fixOld hU xs R hm hd hn).mp ?_⟩
  simpa only [hxs] using hp

noncomputable def retainedPaths (f : ℕ ↪ ℕ) (N' K : ℕ) (R' : Edges) : Finset (List (Edges × ℤ)) := by
  classical
  exact (allPaths N' K R').filter (PathSupported f)

/-- Exact finite-set image, independent of changes in the auxiliary rank. -/
theorem allPaths_image_eq_retained (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i ≤ n, f i = i)
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N K)
    (hd : R.card ≤ d) (hn : 2*d ≤ n) :
    (allPaths N K R).image (pathRename f) = retainedPaths f N' K (rowRename f R) := by
  classical
  have hm' := (matching_rename f (Function.Embedding.refl ℕ) R).mpr hm
  have hR' := rowRename_grid f hU R hR
  ext ys
  simp only [Finset.mem_image, retainedPaths, Finset.mem_filter]
  constructor
  · rintro ⟨xs, hx, rfl⟩
    refine ⟨?_, pathRename_supported f xs⟩
    apply (mem_allPaths_iff _ _ hm' hR').mpr
    exact (validPath_compression_iff f hf fixOld hU xs R hm hd hn).mpr
      ((mem_allPaths_iff R xs hm hR).mp hx)
  · rintro ⟨hy, hs⟩
    obtain ⟨xs, hxs, hp⟩ := valid_retained_preimage f hf fixOld hU R hm hd hn ys hs
      ((mem_allPaths_iff _ _ hm' hR').mp hy)
    exact ⟨xs, (mem_allPaths_iff R xs hm hR).mpr hp, hxs⟩

/-- The small integer coefficient is the signed sum over exactly the retained large paths. -/
theorem normalizer_eq_retained_sum (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i ≤ n, f i = i)
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N K)
    (hd : R.card ≤ d) (hn : 2*d ≤ n) :
    normalizer N K R = ∑ ys ∈ retainedPaths f N' K (rowRename f R), pathWeight ys := by
  classical
  rw [← allPaths_image_eq_retained f hf fixOld hU R hm hR hd hn,
    Finset.sum_image (pathRename_injective f).injOn]
  simp only [pathRename_weight]
  exact normalizer_eq_allPaths_sum N K R


/-- The actual time-indexed trajectory of the signed list, with no extra branch steps. -/
def trajectory (R : Edges) (xs : List (Edges × ℤ)) : ℕ → Edges
  | 0 => R
  | t+1 => match xs with
    | [] => ∅
    | x::ys => trajectory x.1 ys t

@[simp] theorem trajectory_zero (R : Edges) (xs : List (Edges × ℤ)) : trajectory R xs 0 = R := by rw [trajectory]
@[simp] theorem trajectory_succ (R : Edges) (x : Edges × ℤ) (xs : List (Edges × ℤ)) (t : ℕ) :
    trajectory R (x::xs) (t+1) = trajectory x.1 xs t := rfl

theorem validPath_trajectory_steps {N K : ℕ} (xs : List (Edges × ℤ)) (R : Edges)
    (hp : ValidPath N K R xs) :
    ∀ t < xs.length, ∃ z, ChosenBranch N K (trajectory R xs t) (trajectory R xs (t+1)) z := by
  induction xs generalizing R with
  | nil => simp
  | cons x xs ih =>
    intro t ht
    cases t with
    | zero => exact ⟨x.2, by simpa only [trajectory_zero, trajectory_succ] using hp.1⟩
    | succ t => exact ih x.1 hp.2 t (by simpa using ht)

/-- Every encountered appended row, including the initial state and deleted rows. -/
def pathHistory (n : ℕ) (R : Edges) : List (Edges × ℤ) → Finset ℕ
  | [] => (rows R).filter (n < ·)
  | x::xs => (rows R).filter (n < ·) ∪ pathHistory n x.1 xs

theorem mem_pathHistory (n : ℕ) (R : Edges) (xs : List (Edges × ℤ)) (i : ℕ) :
    i ∈ pathHistory n R xs ↔ ∃ t ≤ xs.length, n < i ∧ ∃ j, (i,j) ∈ trajectory R xs t := by
  induction xs generalizing R with
  | nil => simp [pathHistory, rows, trajectory, Prod.exists, and_comm]
  | cons x xs ih =>
    simp only [pathHistory, Finset.mem_union, Finset.mem_filter, rows,
      Finset.mem_image, Prod.exists, List.length_cons]
    constructor
    · rintro (⟨⟨a,b,he,hai⟩,hni⟩ | htail)
      · subst a; exact ⟨0, by omega, hni, b, he⟩
      · obtain ⟨t, ht, hni, j, he⟩ := (ih x.1).mp htail
        exact ⟨t+1, by omega, hni, j, he⟩
    · rintro ⟨t, ht, hni, j, he⟩
      cases t with
      | zero => exact Or.inl ⟨⟨i,j,he,rfl⟩,hni⟩
      | succ t => exact Or.inr ((ih x.1).mpr ⟨t, by omega, hni, j, he⟩)

theorem pathHistory_eq_historyRows (n : ℕ) (R : Edges) (xs : List (Edges × ℤ)) :
    pathHistory n R xs = historyRows n (trajectory R xs) xs.length := by
  ext i
  rw [mem_pathHistory, mem_historyRows]

/-- The existing persistent-token theorem now applies to the actual signed list paths. -/
theorem validPath_history_bound {N K n d : ℕ} (R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (hp : ValidPath N K R xs) : (pathHistory n R xs).card ≤ R.card := by
  rw [pathHistory_eq_historyRows]
  simpa only [trajectory_zero] using actual_path_history_bound (trajectory R xs)
    (by simpa only [trajectory_zero] using hm) (by simpa only [trajectory_zero] using hd) hn
    (validPath_trajectory_steps xs R hp)

theorem validPath_marked_history {N K n d i j : ℕ} (R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (hp : ValidPath N K R xs) (hi : n < i) (he : (i,j) ∈ R) :
    i ∈ pathHistory n R xs ∧ 1 ≤ (pathHistory n R xs).card ∧ (pathHistory n R xs).card ≤ R.card := by
  rw [pathHistory_eq_historyRows]
  simpa only [trajectory_zero] using marked_actual_path_history_bound (trajectory R xs)
    (by simpa only [trajectory_zero] using hm) (by simpa only [trajectory_zero] using hd) hn
    (validPath_trajectory_steps xs R hp) hi (by simpa only [trajectory_zero] using he)


theorem appended_row_filter_rename (f : ℕ ↪ ℕ) (hf : StrictMono f) (n : ℕ)
    (hfn : f n = n) (R : Edges) :
    (rows (rowRename f R)).filter (n < ·) = ((rows R).filter (n < ·)).map f := by
  ext i
  simp only [rows_rename, Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨⟨j, hj, hji⟩, hni⟩
    have hnj : n < j := hf.lt_iff_lt.mp (by simpa only [hfn, hji] using hni)
    exact ⟨j, ⟨hj,hnj⟩,hji⟩
  · rintro ⟨j, ⟨hj,hnj⟩,hji⟩
    exact ⟨⟨j,hj,hji⟩, by simpa only [hfn,hji] using hf hnj⟩

/-- Compression preserves the entire encountered support as an actual finite-set image. -/
theorem pathHistory_rename (f : ℕ ↪ ℕ) (hf : StrictMono f) (n : ℕ)
    (fixOld : ∀ i ≤ n, f i = i) (R : Edges) (xs : List (Edges × ℤ)) :
    pathHistory n (rowRename f R) (pathRename f xs) = (pathHistory n R xs).map f := by
  induction xs generalizing R with
  | nil => exact appended_row_filter_rename f hf n (fixOld n le_rfl) R
  | cons x xs ih =>
    simp only [pathRename_cons, pathHistory, signedRename, Finset.map_union]
    rw [appended_row_filter_rename f hf n (fixOld n le_rfl), ih]

/-- A mapped path uses exactly the image of a specified encountered row set. -/
theorem pathHistory_exact_iff (f : ℕ ↪ ℕ) (hf : StrictMono f) (n : ℕ)
    (fixOld : ∀ i ≤ n, f i = i) (R : Edges) (xs : List (Edges × ℤ)) (S : Finset ℕ) :
    pathHistory n (rowRename f R) (pathRename f xs) = S.map f ↔ pathHistory n R xs = S := by
  rw [pathHistory_rename f hf n fixOld]
  exact (Finset.map_injective f).eq_iff

theorem child_row_mem_pathHistory (n : ℕ) (R : Edges) (xs : List (Edges × ℤ))
    (x : Edges × ℤ) (hx : x ∈ xs) (e : ℕ × ℕ) (he : e ∈ x.1) (hn : n < e.1) :
    e.1 ∈ pathHistory n R xs := by
  induction xs generalizing R with
  | nil => simp at hx
  | cons y ys ih =>
    apply Finset.mem_union_right
    rcases List.mem_cons.mp hx with hxy | htail
    · subst x
      have hr : e.1 ∈ (rows y.1).filter (n < ·) :=
        Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e,he,rfl⟩,hn⟩
      cases ys with
      | nil => exact hr
      | cons z zs => exact Finset.mem_union_left _ hr
    · exact ih y.1 htail

/-- Fixed old rows and supported entire appended history imply support at every child. -/
theorem history_supported_implies_pathSupported (f : ℕ ↪ ℕ) (n : ℕ)
    (fixOld : ∀ i ≤ n, f i = i) (R : Edges) (xs : List (Edges × ℤ))
    (hh : ∀ i ∈ pathHistory n R xs, i ∈ Set.range f) : PathSupported f xs := by
  intro x hx e he
  by_cases hi : e.1 ≤ n
  · exact ⟨e.1, fixOld e.1 hi⟩
  · exact hh e.1 (child_row_mem_pathHistory n R xs x hx e he (by omega))

noncomputable def historyPaths (N K n : ℕ) (R : Edges) (S : Finset ℕ) : Finset (List (Edges × ℤ)) := by
  classical
  exact (allPaths N K R).filter (fun xs => pathHistory n R xs = S)

/-- Exact history fibers correspond; the large fiber needs no extra support filter. -/
theorem historyPaths_image_eq (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i ≤ n, f i = i)
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N K)
    (hd : R.card ≤ d) (hn : 2*d ≤ n) (S : Finset ℕ) :
    (historyPaths N K n R S).image (pathRename f) =
      historyPaths N' K n (rowRename f R) (S.map f) := by
  classical
  have hm' := (matching_rename f (Function.Embedding.refl ℕ) R).mpr hm
  have hR' := rowRename_grid f hU R hR
  ext ys
  simp only [historyPaths, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨xs, ⟨hx,hh⟩, rfl⟩
    refine ⟨?_, (pathHistory_exact_iff f hf n fixOld R xs S).mpr hh⟩
    apply (mem_allPaths_iff _ _ hm' hR').mpr
    exact (validPath_compression_iff f hf fixOld hU xs R hm hd hn).mpr
      ((mem_allPaths_iff R xs hm hR).mp hx)
  · rintro ⟨hy,hh⟩
    have hs : PathSupported f ys := by
      apply history_supported_implies_pathSupported f n fixOld (rowRename f R) ys
      intro i hi
      rw [hh] at hi
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
      exact ⟨j,hj⟩
    obtain ⟨xs,hxs,hp⟩ := valid_retained_preimage f hf fixOld hU R hm hd hn ys hs
      ((mem_allPaths_iff _ _ hm' hR').mp hy)
    refine ⟨xs, ⟨(mem_allPaths_iff R xs hm hR).mpr hp, ?_⟩, hxs⟩
    apply (pathHistory_exact_iff f hf n fixOld R xs S).mp
    simpa only [hxs] using hh

/-- Equality of the signed sums for a fixed entire encountered support. -/
theorem historyPaths_sum_eq (f : ℕ ↪ ℕ) (hf : StrictMono f)
    {N N' K n d : ℕ} (fixOld : ∀ i ≤ n, f i = i)
    (hU : ∀ i, f i ∈ Finset.Icc 1 N' ↔ i ∈ Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N K)
    (hd : R.card ≤ d) (hn : 2*d ≤ n) (S : Finset ℕ) :
    (∑ xs ∈ historyPaths N K n R S, pathWeight xs) =
      ∑ ys ∈ historyPaths N' K n (rowRename f R) (S.map f), pathWeight ys := by
  classical
  rw [← historyPaths_image_eq f hf fixOld hU R hm hR hd hn S,
    Finset.sum_image (pathRename_injective f).injOn]
  simp only [pathRename_weight]

/-- A concrete selector at a row which the gap embedding really moves. -/
theorem chosen_five_singleton : chosenRewrite {(5,1)} = .column 1 {(5,1)} := by
  have hr : rowFailures {(5,1)} = ∅ := by decide
  have hc : columnFailures {(5,1)} = {1} := by decide
  have hp : rowPrefix (transpose {(5,1)}) 1 = {(1,5)} := by decide
  have hm : chosenLongest {(1,5)} = {(1,5)} := by
    apply chosenLongest_unique
    · decide
    · intro D hD
      have hl : longestChains {(1,5)} = {{(1,5)}} := by decide
      rw [hl] at hD
      have he := Finset.mem_singleton.mp hD
      subst D
      exact le_refl _
  have hcc : chosenColumnChain {(5,1)} 1 = {(5,1)} := by
    rw [chosenColumnChain, hp, hm]
    decide
  unfold chosenRewrite
  simp only [hr, Finset.not_nonempty_empty, ↓reduceDIte, hc, Finset.singleton_nonempty,
    Finset.min'_singleton, hcc]

def smallGapPath : List (Edges × ℤ) := [({(5,1)},-1),(∅,1)]
def largeGapPath : List (Edges × ℤ) := [({(6,1)},-1),(∅,1)]

theorem smallGapPath_valid : ValidPath 5 2 {(1,1)} smallGapPath := by
  constructor
  · rw [ChosenBranch, chosen_singleton_example]
    refine ⟨{(5,1)}, Or.inr ?_, ?_, ?_⟩ <;> decide
  · constructor
    · rw [ChosenBranch, chosen_five_singleton]
      unfold ColumnBranch
      refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide
    · rfl

theorem gap_path_map : pathRename gapEmbedding smallGapPath = largeGapPath := by decide

theorem gap_initial_fixed : rowRename gapEmbedding {(1,1)} = {(1,1)} := by decide

theorem largeGapPath_valid : ValidPath 7 2 {(1,1)} largeGapPath := by
  have h := (validPath_compression_iff gapEmbedding gapRow_strictMono gap_fixes_old
    gap_universe_preimage smallGapPath {(1,1)} (by decide) (d:=1) (by decide) (by decide)).mpr smallGapPath_valid
  simpa only [gap_initial_fixed, gap_path_map] using h

theorem gap_history_nonvacuous :
    pathHistory 4 {(1,1)} smallGapPath = {5} ∧
    pathHistory 4 {(1,1)} largeGapPath = {6} ∧
    pathWeight smallGapPath = -1 ∧ pathWeight largeGapPath = -1 := by decide

theorem gap_actual_history_bound : (pathHistory 4 {(1,1)} smallGapPath).card ≤ 1 :=
  validPath_history_bound (n:=4) (d:=1) {(1,1)} smallGapPath (by decide) (by decide)
    (by decide) smallGapPath_valid

attribute [local irreducible] allPaths retainedPaths

theorem gap_retained_membership : largeGapPath ∈ retainedPaths gapEmbedding 7 2 {(1,1)} := by
  have heq := allPaths_image_eq_retained gapEmbedding gapRow_strictMono gap_fixes_old
    gap_universe_preimage (K:=2) {(1,1)} (by decide) (by decide) (d:=1) (by decide) (by decide)
  rw [gap_initial_fixed] at heq
  rw [← heq]
  apply Finset.mem_image.mpr
  exact ⟨smallGapPath, (mem_allPaths_iff (N:=5) (K:=2) {(1,1)} smallGapPath
    (by decide) (by decide)).mpr smallGapPath_valid, gap_path_map⟩

/-- Final emptiness alone does not characterize a retained path. -/
theorem deleted_label_path_not_retained :
    ValidPath 7 2 {(1,1)} smallGapPath ∧ ¬ PathSupported gapEmbedding smallGapPath := by
  constructor
  · constructor
    · rw [ChosenBranch, chosen_singleton_example]
      refine ⟨{(5,1)}, Or.inr ?_, ?_, ?_⟩ <;> decide
    · constructor
      · rw [ChosenBranch, chosen_five_singleton]
        unfold ColumnBranch
        refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide
      · rfl
  · intro hs
    have he := hs ({(5,1)},-1) (by simp [smallGapPath]) (5,1) (by simp)
    obtain ⟨j,hj⟩ := he
    change gapRow j = 5 at hj
    dsimp [gapRow] at hj
    split_ifs at hj <;> omega

theorem gap_marked_history_after_deletion :
    5 ∈ pathHistory 4 {(5,1)} [(∅,1)] ∧
    1 ≤ (pathHistory 4 {(5,1)} [(∅,1)]).card ∧
    (pathHistory 4 {(5,1)} [(∅,1)]).card ≤ 1 := by
  apply validPath_marked_history (N:=5) (K:=2) (n:=4) (d:=1) (j:=1)
      {(5,1)} [(∅,1)] (by decide) (by decide) (by decide) ?_ (by decide) (by decide)
  constructor
  · rw [ChosenBranch, chosen_five_singleton]
    unfold ColumnBranch
    refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide
  · rfl

end SelfContainedCycle041
