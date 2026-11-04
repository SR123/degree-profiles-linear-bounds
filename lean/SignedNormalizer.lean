import ActualTokens

namespace SelfContainedCycle040
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle039

/-- Signs are derived from the actual injection formulas. -/
theorem neg_one_pow_sign (k : ℕ) : (-1 : ℤ)^k = 1 ∨ (-1 : ℤ)^k = -1 := by
  induction k with
  | zero => simp
  | succ k ih => rcases ih with h | h <;> simp [pow_succ, h]

theorem branch_sign {P C Q : Edges} {B T : Finset ℕ} {z : ℤ}
    (h : Branch P C B T Q z) : z = 1 ∨ z = -1 := by
  obtain ⟨M, h, _, _⟩ := h
  rcases h with h | h
  · rw [h.2.2.2]; exact neg_one_pow_sign M.card
  · exact Or.inr h.2.2.2.2

theorem chosenBranch_sign {N K : ℕ} {R Q : Edges} {z : ℤ}
    (h : ChosenBranch N K R Q z) : z = 1 ∨ z = -1 := by
  unfold ChosenBranch at h
  split at h
  · exact branch_sign h
  · exact branch_sign h
  · exact h.elim

theorem actual_row_sign_unique {R C Q : Edges} {a N K : ℕ} {z w : ℤ}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hf : FirstRowAt R a)
    (hC : C ∈ longestChains (rowPrefix R a))
    (hz : Branch (R \ C) C (freeBefore (Finset.Icc 1 N) R a)
      (targetRows (Finset.Icc 1 N) R C a) Q z)
    (hw : Branch (R \ C) C (freeBefore (Finset.Icc 1 N) R a)
      (targetRows (Finset.Icc 1 N) R C a) Q w) : z = w := by
  obtain ⟨hsub, hc⟩ := (mem_chains _ _).mp (Finset.mem_filter.mp hC).1
  have hCR : C ⊆ R := hsub.trans (Finset.filter_subset _ _)
  have positive := grid_positive hR
  obtain ⟨e, he, hea⟩ := first_failed_longest_has_endpoint positive hf hC
  have heG := Finset.mem_product.mp (hR (hCR he))
  have ha : a ≤ N := by simpa only [hea] using (Finset.mem_Icc.mp heG.1).2
  exact branch_sign_unique (chain_isMatching hc)
    (failed_longest_chain_guard ha positive hf.1 hC)
    (complement_columns_disjoint hm hCR) hz hw

theorem chosenBranch_sign_unique {R Q : Edges} {N K : ℕ} {z w : ℤ}
    (hm : IsMatching R) (hR : R ⊆ grid N K)
    (hz : ChosenBranch N K R Q z) (hw : ChosenBranch N K R Q w) : z = w := by
  unfold ChosenBranch chosenRewrite at hz hw
  split_ifs at hz hw with hr hc
  · exact actual_row_sign_unique hm hR (min_row_failure_is_first R hr)
      (chosenLongest_spec _).1 hz hw
  · apply actual_row_sign_unique ((matching_transpose R).mpr hm) (transpose_subset_grid hR)
      ((firstColumnAt_iff R _).mp (min_column_failure_is_first R hc)) (chosenLongest_spec _).1
    · simpa only [ColumnBranch, chosenColumnChain, transpose_transpose, transpose_sdiff] using hz
    · simpa only [ColumnBranch, chosenColumnChain, transpose_transpose, transpose_sdiff] using hw
  · exact hz.elim

/-- Explicit finite enumeration: actual grid subsets paired with the two proved signs. -/
noncomputable def children (N K : ℕ) (R : Edges) : Finset (Edges × ℤ) := by
  classical
  exact ((grid N K).powerset.product {1,-1}).filter (fun x => ChosenBranch N K R x.1 x.2)

theorem mem_children_iff {N K : ℕ} {R Q : Edges} {z : ℤ}
    (hR : R ⊆ grid N K) : (Q,z) ∈ children N K R ↔ ChosenBranch N K R Q z := by
  classical
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (chosenBranch_closed hR h).2, ?_⟩, h⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton] using chosenBranch_sign h

theorem child_closed {N K : ℕ} {R : Edges} {x : Edges × ℤ}
    (hR : R ⊆ grid N K) (hx : x ∈ children N K R) :
    IsMatching x.1 ∧ x.1 ⊆ grid N K :=
  chosenBranch_closed hR ((mem_children_iff hR).mp hx)

theorem child_rank_lt {N K : ℕ} {R : Edges} {x : Edges × ℤ}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hx : x ∈ children N K R) :
    rank (grid N K) (N+K) x.1 < rank (grid N K) (N+K) R :=
  chosenBranch_rank_lt hm hR ((mem_children_iff hR).mp hx)

theorem children_unique_target {N K : ℕ} {R : Edges}
    (hm : IsMatching R) (hR : R ⊆ grid N K) :
    Set.InjOn Prod.fst (children N K R : Set (Edges × ℤ)) := by
  intro x hx y hy hxy
  apply Prod.ext hxy
  apply chosenBranch_sign_unique hm hR ((mem_children_iff hR).mp hx)
  simpa only [hxy] using (mem_children_iff hR).mp hy

theorem children_terminal {N K : ℕ} {R : Edges} (h : chosenRewrite R = .terminal) :
    children N K R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hb := (Finset.mem_filter.mp hx).2
  simp only [ChosenBranch, h] at hb

/-- Rank zero is possible only at the empty matching. -/
theorem rank_zero_iff (N K : ℕ) (R : Edges) :
    rank (grid N K) (N+K) R = 0 ↔ R = ∅ := by
  constructor
  · intro h
    have hc : R.card = 0 := by
      unfold rank at h
      nlinarith
    exact Finset.card_eq_zero.mp hc
  · rintro rfl; simp [rank, weightSum]

theorem children_empty (N K : ℕ) : children N K ∅ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hlt := child_rank_lt (by simp [IsMatching]) (Finset.empty_subset _) hx
  simp [rank, weightSum] at hlt

/-- A finite unfolding. Empty is a leaf at every cutoff, not a self-loop. -/
noncomputable def truncated (N K : ℕ) : ℕ → Edges → ℤ
  | 0, R => if R = ∅ then 1 else 0
  | t+1, R => if R = ∅ then 1 else ∑ x ∈ children N K R, x.2 * truncated N K t x.1

@[simp] theorem truncated_empty (N K t : ℕ) : truncated N K t ∅ = 1 := by
  cases t <;> simp [truncated]

/-- The proved rank makes an additional unfolding immaterial after the bound. -/
theorem truncated_stable_step (N K t : ℕ) (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K)
    (ht : rank (grid N K) (N+K) R ≤ t) :
    truncated N K (t+1) R = truncated N K t R := by
  induction t generalizing R with
  | zero =>
    have hz : R = ∅ := (rank_zero_iff N K R).mp (by omega)
    simp [hz]
  | succ t ih =>
    by_cases hz : R = ∅
    · simp [hz]
    · simp only [truncated, if_neg hz]
      apply Finset.sum_congr rfl
      intro x hx
      have hcl := child_closed hR hx
      have hlt := child_rank_lt hm hR hx
      exact congrArg (fun v : ℤ => x.2 * v) (ih x.1 hcl.1 hcl.2 (by omega))

noncomputable def normalizer (N K : ℕ) (R : Edges) : ℤ :=
  truncated N K (rank (grid N K) (N+K) R) R

theorem normalizer_eq_truncated {N K : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (t : ℕ)
    (ht : rank (grid N K) (N+K) R ≤ t) :
    normalizer N K R = truncated N K t R := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [truncated_stable_step N K t R hm hR ht]; exact ih

/-- Actual recursion with no supplied normalization hypothesis. -/
theorem normalizer_recursion {N K : ℕ} (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) :
    normalizer N K R = if R = ∅ then 1 else
      ∑ x ∈ children N K R, x.2 * normalizer N K x.1 := by
  rw [normalizer_eq_truncated R hm hR (rank (grid N K) (N+K) R + 1) (by omega)]
  rw [truncated]
  split_ifs with hz
  · rfl
  · apply Finset.sum_congr rfl
    intro x hx
    have hcl := child_closed hR hx
    have hlt := child_rank_lt hm hR hx
    rw [← normalizer_eq_truncated x.1 hcl.1 hcl.2 _ (by omega)]

@[simp] theorem normalizer_empty (N K : ℕ) : normalizer N K ∅ = 1 := by
  simp [normalizer]

theorem normalizer_terminal {N K : ℕ} {R : Edges}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hne : R ≠ ∅)
    (ht : chosenRewrite R = .terminal) : normalizer N K R = 0 := by
  rw [normalizer_recursion R hm hR, if_neg hne, children_terminal ht]
  simp


/-- Uniqueness concerns this concrete deterministic rewrite recursion. -/
theorem normalizer_unique {N K : ℕ} (f : Edges → ℤ)
    (hf : ∀ R, IsMatching R → R ⊆ grid N K →
      f R = if R = ∅ then 1 else ∑ x ∈ children N K R, x.2 * f x.1) :
    ∀ R, IsMatching R → R ⊆ grid N K → f R = normalizer N K R := by
  intro R
  induction R using (measure (fun R => rank (grid N K) (N+K) R)).wf.induction with
  | h R ih =>
    intro hm hR
    rw [hf R hm hR, normalizer_recursion R hm hR]
    split_ifs
    · rfl
    · apply Finset.sum_congr rfl
      intro x hx
      have hcl := child_closed hR hx
      exact congrArg (fun v : ℤ => x.2 * v) (ih x.1 (child_rank_lt hm hR hx) hcl.1 hcl.2)

/-- A path records every signed child; its only leaf is the empty matching. -/
def ValidPath (N K : ℕ) : Edges → List (Edges × ℤ) → Prop
  | R, [] => R = ∅
  | R, x :: xs => ChosenBranch N K R x.1 x.2 ∧ ValidPath N K x.1 xs

noncomputable def paths (N K : ℕ) : ℕ → Edges → Finset (List (Edges × ℤ))
  | 0, R => if R = ∅ then {[]} else ∅
  | t+1, R => if R = ∅ then {[]} else
      (children N K R).biUnion (fun x => (paths N K t x.1).image (List.cons x))

@[simp] theorem paths_empty (N K t : ℕ) : paths N K t ∅ = {[]} := by
  cases t <;> simp [paths]

theorem validPath_empty_iff (N K : ℕ) (xs : List (Edges × ℤ)) :
    ValidPath N K ∅ xs ↔ xs = [] := by
  cases xs with
  | nil => simp [ValidPath]
  | cons x xs =>
    have hn : ¬ ChosenBranch N K ∅ x.1 x.2 := by
      intro h
      have hh := (mem_children_iff (N:=N) (K:=K) (Finset.empty_subset _)).mpr h
      rw [children_empty] at hh
      exact Finset.notMem_empty _ hh
    simp [ValidPath, hn]

/-- Exact membership, including the real length and no padded terminal loops. -/
theorem mem_paths_iff (N K t : ℕ) (R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hR : R ⊆ grid N K) :
    xs ∈ paths N K t R ↔ ValidPath N K R xs ∧ xs.length ≤ t := by
  classical
  induction t generalizing R xs with
  | zero =>
    cases xs with
    | nil => by_cases hz : R = ∅ <;> simp [paths, ValidPath, hz]
    | cons x xs => by_cases hz : R = ∅ <;> simp [paths, hz]
  | succ t ih =>
    by_cases hz : R = ∅
    · subst R
      simp only [paths_empty, Finset.mem_singleton, validPath_empty_iff]
      constructor
      · intro h; subst xs; simp
      · exact And.left
    · cases xs with
      | nil => simp [paths, hz, ValidPath]
      | cons x xs =>
        simp only [paths, if_neg hz, Finset.mem_biUnion, Finset.mem_image,
          List.cons.injEq, ValidPath, List.length_cons]
        constructor
        · rintro ⟨y, hy, ys, hys, hyx, hysxs⟩
          subst y; subst ys
          have hcl := child_closed hR hy
          have hp := (ih x.1 xs hcl.1 hcl.2).mp hys
          exact ⟨⟨(mem_children_iff hR).mp hy, hp.1⟩, by omega⟩
        · rintro ⟨⟨hx, hxs⟩, hlen⟩
          have hcl := chosenBranch_closed hR hx
          exact ⟨x, (mem_children_iff hR).mpr hx, xs,
            (ih x.1 xs hcl.1 hcl.2).mpr ⟨hxs, by omega⟩, rfl, rfl⟩

theorem validPath_length_le_rank {N K : ℕ} (xs : List (Edges × ℤ)) (R : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hp : ValidPath N K R xs) :
    xs.length ≤ rank (grid N K) (N+K) R := by
  induction xs generalizing R with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := hp
    have hcl := chosenBranch_closed hR hx
    have hlen := ih x.1 hcl.1 hcl.2 hxs
    have hlt := chosenBranch_rank_lt hm hR hx
    simp only [List.length_cons]
    omega

noncomputable def allPaths (N K : ℕ) (R : Edges) : Finset (List (Edges × ℤ)) :=
  paths N K (rank (grid N K) (N+K) R) R

theorem mem_allPaths_iff {N K : ℕ} (R : Edges) (xs : List (Edges × ℤ))
    (hm : IsMatching R) (hR : R ⊆ grid N K) :
    xs ∈ allPaths N K R ↔ ValidPath N K R xs := by
  rw [allPaths, mem_paths_iff N K _ R xs hm hR]
  exact ⟨And.left, fun h => ⟨h, validPath_length_le_rank xs R hm hR h⟩⟩

def pathWeight : List (Edges × ℤ) → ℤ
  | [] => 1
  | x :: xs => x.2 * pathWeight xs


theorem prefixed_paths_disjoint (N K t : ℕ) (R : Edges) :
    (children N K R : Set (Edges × ℤ)).PairwiseDisjoint
      (fun x => (paths N K t x.1).image (List.cons x)) := by
  classical
  intro x hx y hy hxy
  apply Finset.disjoint_left.mpr
  intro xs hxs hys
  obtain ⟨as, _, ha⟩ := Finset.mem_image.mp hxs
  obtain ⟨bs, _, hb⟩ := Finset.mem_image.mp hys
  exact hxy (List.cons.inj (ha.trans hb.symm)).1

/-- Finite unfolding equals the genuine signed path sum at the same cutoff. -/
theorem truncated_eq_path_sum (N K t : ℕ) (R : Edges) :
    truncated N K t R = ∑ xs ∈ paths N K t R, pathWeight xs := by
  classical
  induction t generalizing R with
  | zero => by_cases hz : R = ∅ <;> simp [truncated, paths, hz, pathWeight]
  | succ t ih =>
    by_cases hz : R = ∅
    · simp [hz, pathWeight]
    · rw [truncated, paths, if_neg hz, if_neg hz,
        Finset.sum_biUnion (prefixed_paths_disjoint N K t R)]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_image (fun a _ b _ h => (List.cons.inj h).2)]
      simp only [pathWeight]
      rw [← Finset.mul_sum, ih x.1]

/-- The recursion has exactly the sum of all finite actual paths to empty. -/
theorem normalizer_eq_allPaths_sum (N K : ℕ) (R : Edges) :
    normalizer N K R = ∑ xs ∈ allPaths N K R, pathWeight xs :=
  truncated_eq_path_sum N K _ R


attribute [local irreducible] allPaths

/-- Non-vacuity: both a direct positive path and a longer negative path occur. -/
theorem direct_positive_path : ValidPath 3 2 {(1,1)} [(∅,1)] := by
  constructor
  · rw [ChosenBranch, chosen_singleton_example]
    refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide
  · rfl

theorem indirect_negative_path : ValidPath 3 2 {(1,1)} [({(3,1)},-1),(∅,1)] := by
  constructor
  · rw [ChosenBranch, chosen_singleton_example]
    refine ⟨{(3,1)}, Or.inr ?_, ?_, ?_⟩ <;> decide
  · constructor
    · rw [ChosenBranch, chosen_appended_singleton]
      unfold ColumnBranch
      refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide
    · rfl

theorem actual_paths_nonvacuous :
    [(∅,1)] ∈ allPaths 3 2 {(1,1)} ∧
    [({(3,1)},-1),(∅,1)] ∈ allPaths 3 2 {(1,1)} ∧
    pathWeight [(∅,1)] = 1 ∧ pathWeight [({(3,1)},-1),(∅,1)] = -1 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact (mem_allPaths_iff (N:=3) (K:=2) {(1,1)} [(∅,1)] (by decide) (by decide)).mpr direct_positive_path
  · exact (mem_allPaths_iff (N:=3) (K:=2) {(1,1)} [({(3,1)},-1),(∅,1)] (by decide) (by decide)).mpr indirect_negative_path

theorem no_empty_padding (N K : ℕ) : ¬ ValidPath N K ∅ [(∅,1)] := by
  simp [validPath_empty_iff]

theorem positive_terminal_example : chosenRewrite {(2,2)} = .terminal := by
  have hr : rowFailures {(2,2)} = ∅ := by decide
  have hc : columnFailures {(2,2)} = ∅ := by decide
  simp [chosenRewrite, hr, hc]

theorem positive_terminal_normalizer : normalizer 2 2 {(2,2)} = 0 :=
  normalizer_terminal (by decide) (by decide) (by decide) positive_terminal_example


theorem one_square_lower : ChosenBranch 1 1 {(1,1)} ∅ 1 := by
  rw [ChosenBranch, chosen_singleton_example]
  refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide

theorem one_square_children : children 1 1 {(1,1)} = {(∅,1)} := by
  classical
  ext x
  constructor
  · intro hx
    have hb := (mem_children_iff (by decide : ({(1,1)} : Edges) ⊆ grid 1 1)).mp hx
    have hcl := child_closed (by decide : ({(1,1)} : Edges) ⊆ grid 1 1) hx
    have hg : grid 1 1 = {(1,1)} := by decide
    rw [hg] at hcl
    rcases Finset.subset_singleton_iff.mp hcl.2 with he | he
    · have hz : x.2 = 1 := chosenBranch_sign_unique (by decide) (by decide) hb (he.symm ▸ one_square_lower)
      exact Finset.mem_singleton.mpr (Prod.ext he hz)
    · have hlt := child_rank_lt (by decide) (by decide) hx
      rw [he] at hlt
      omega
  · intro hx
    have he := Finset.mem_singleton.mp hx
    subst x
    exact (mem_children_iff (by decide)).mpr one_square_lower

theorem one_square_normalizer : normalizer 1 1 {(1,1)} = 1 := by
  rw [normalizer_recursion _ (by decide) (by decide), if_neg (by decide), one_square_children]
  simp

end SelfContainedCycle040
