import PermutationEvaluation

namespace SelfContainedCycle046
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle040 SelfContainedCycle045

@[simp] theorem empty_terminal : chosenRewrite (∅ : Edges) = .terminal := by decide

/-- Degree is nonincreasing for every actual selected row child. -/
theorem row_child_card_le {N K a : ℕ} {R C : Edges} {x : Edges × ℤ}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hc : chosenRewrite R = .row a C)
    (hx : x ∈ children N K R) : x.1.card ≤ R.card := by
  obtain ⟨hC,hB⟩ := row_choice_data hR hc
  have hb := (mem_children_iff hR).mp hx
  rw [ChosenBranch,hc] at hb
  have h := branch_card_le (matching_subset hm hC) hB (complement_columns_disjoint hm hC) hb
  simpa only [Finset.sdiff_union_of_subset hC] using h

/-- Degree is nonincreasing for every actual child, including selected column rewrites. -/
theorem child_card_le {N K : ℕ} {R : Edges} {x : Edges × ℤ}
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hx : x ∈ children N K R) : x.1.card ≤ R.card := by
  cases hc : chosenRewrite R with
  | terminal => rw [children_terminal hc] at hx; exact (Finset.notMem_empty _ hx).elim
  | row a C => exact row_child_card_le hm hR hc hx
  | column a C =>
    have hx' : signedTranspose x ∈ children K N (transpose R) := by
      rw [← children_column_transpose hR hc]
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
    have h := row_child_card_le ((matching_transpose R).mpr hm) (transpose_subset_grid hR)
      (column_choice_transposes hc) hx'
    simpa only [signedTranspose,transpose,Finset.card_map] using h

/-- A finite unfolding that retains every terminal leaf, rather than just the empty one. -/
noncomputable def leafTruncated (N K : ℕ) : ℕ → Edges → Edges → ℤ
  | 0,R,T => if chosenRewrite R = .terminal then if R = T then 1 else 0 else 0
  | t+1,R,T => if chosenRewrite R = .terminal then if R = T then 1 else 0 else
      ∑ x ∈ children N K R, x.2 * leafTruncated N K t x.1 T

theorem leafTruncated_terminal (N K t : ℕ) (R T : Edges) (ht : chosenRewrite R = .terminal) :
    leafTruncated N K t R T = if R=T then 1 else 0 := by
  cases t <;> simp only [leafTruncated,if_pos ht]

/-- An additional unfolding is immaterial once the actual rank bound is reached. -/
theorem leafTruncated_stable_step (N K t : ℕ) (R T : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (ht : rank (grid N K) (N+K) R ≤ t) :
    leafTruncated N K (t+1) R T = leafTruncated N K t R T := by
  induction t generalizing R with
  | zero =>
    have hz : R=∅ := (rank_zero_iff N K R).mp (by omega)
    subst R
    simp [leafTruncated]
  | succ t ih =>
    by_cases hz : chosenRewrite R = .terminal
    · rw [leafTruncated_terminal N K _ R T hz,leafTruncated_terminal N K _ R T hz]
    · simp only [leafTruncated,if_neg hz]
      apply Finset.sum_congr rfl
      intro x hx
      have hcl := child_closed hR hx
      have hlt := child_rank_lt hm hR hx
      exact congrArg (fun z : ℤ => x.2*z) (ih x.1 hcl.1 hcl.2 (by omega))

noncomputable def leafCoeff (N K : ℕ) (R T : Edges) : ℤ :=
  leafTruncated N K (rank (grid N K) (N+K) R) R T

theorem leafCoeff_eq_truncated {N K : ℕ} (R T : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (t : ℕ) (ht : rank (grid N K) (N+K) R ≤ t) :
    leafCoeff N K R T = leafTruncated N K t R T := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [leafTruncated_stable_step N K t R T hm hR ht]; exact ih

/-- Exact recursion of the constructed full terminal coefficient. -/
theorem leafCoeff_recursion {N K : ℕ} (R T : Edges) (hm : IsMatching R) (hR : R ⊆ grid N K) :
    leafCoeff N K R T = if chosenRewrite R = .terminal then if R=T then 1 else 0 else
      ∑ x ∈ children N K R, x.2 * leafCoeff N K x.1 T := by
  rw [leafCoeff_eq_truncated R T hm hR (rank (grid N K) (N+K) R+1) (by omega),leafTruncated]
  by_cases ht : chosenRewrite R = .terminal
  · rw [if_pos ht,if_pos ht]
  · rw [if_neg ht,if_neg ht]
    apply Finset.sum_congr rfl
    intro x hx
    have hcl := child_closed hR hx
    have hlt := child_rank_lt hm hR hx
    rw [← leafCoeff_eq_truncated x.1 T hcl.1 hcl.2 _ (by omega)]

theorem leafCoeff_terminal (N K : ℕ) (R T : Edges) (ht : chosenRewrite R = .terminal) :
    leafCoeff N K R T = if R=T then 1 else 0 := leafTruncated_terminal N K _ R T ht

/-- A nonzero coefficient forces actual terminal support and the input matching's degree cap. -/
theorem leafTruncated_support (N K t : ℕ) (R T : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hv : leafTruncated N K t R T ≠ 0) :
    IsMatching T ∧ T ⊆ grid N K ∧ chosenRewrite T = .terminal ∧ T.card ≤ R.card := by
  induction t generalizing R with
  | zero =>
    by_cases ht : chosenRewrite R = .terminal
    · by_cases heq : R=T
      · subst T; exact ⟨hm,hR,ht,le_rfl⟩
      · simp [leafTruncated,ht,heq] at hv
    · simp [leafTruncated,ht] at hv
  | succ t ih =>
    by_cases ht : chosenRewrite R = .terminal
    · by_cases heq : R=T
      · subst T; exact ⟨hm,hR,ht,le_rfl⟩
      · simp [leafTruncated,ht,heq] at hv
    · rw [leafTruncated,if_neg ht] at hv
      obtain ⟨x,hx,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
      have hval : leafTruncated N K t x.1 T ≠ 0 := (mul_ne_zero_iff.mp hv).2
      have hcl := child_closed hR hx
      obtain ⟨hTm,hTg,hTt,hTc⟩ := ih x.1 hcl.1 hcl.2 hval
      exact ⟨hTm,hTg,hTt,hTc.trans (child_card_le hm hR hx)⟩

theorem leafCoeff_support {N K : ℕ} (R T : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hv : leafCoeff N K R T ≠ 0) :
    IsMatching T ∧ T ⊆ grid N K ∧ chosenRewrite T = .terminal ∧ T.card ≤ R.card :=
  leafTruncated_support N K _ R T hm hR hv

/-- All terminal matchings are explicitly enumerated in a finite ambient powerset. -/
noncomputable def terminalFamily (N K : ℕ) : Finset Edges :=
  ((grid N K).powerset).filter (fun T => IsMatching T ∧ chosenRewrite T = .terminal)

theorem mem_terminalFamily (N K : ℕ) (T : Edges) :
    T ∈ terminalFamily N K ↔ T ⊆ grid N K ∧ IsMatching T ∧ chosenRewrite T = .terminal := by
  simp only [terminalFamily,Finset.mem_filter,Finset.mem_powerset]

/-- The actual empty-leaf coordinate agrees with the already constructed scalar normalizer. -/
theorem leafCoeff_empty {N K : ℕ} (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N K) :
    leafCoeff N K R ∅ = normalizer N K R := by
  apply normalizer_unique (fun Q => leafCoeff N K Q ∅) _ R hm hR
  intro Q hQm hQg
  change leafCoeff N K Q ∅ = if Q=∅ then 1 else ∑ x ∈ children N K Q, x.2 * leafCoeff N K x.1 ∅
  rw [leafCoeff_recursion Q ∅ hQm hQg]
  by_cases hQ : Q=∅
  · subst Q; simp
  · by_cases ht : chosenRewrite Q = .terminal
    · rw [if_pos ht,if_neg hQ,if_neg hQ,children_terminal ht]
      simp
    · rw [if_neg ht,if_neg hQ]

/-- Coefficients outside the explicitly enumerated terminal family vanish. -/
theorem leafCoeff_eq_zero_outside {N K : ℕ} (R T : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hT : T ∉ terminalFamily N K) :
    leafCoeff N K R T = 0 := by
  by_contra h
  obtain ⟨hTm,hTg,hTt,_⟩ := leafCoeff_support R T hm hR h
  exact hT ((mem_terminalFamily N K T).mpr ⟨hTg,hTm,hTt⟩)

/-- The expansion cannot introduce leaves of greater matching degree. -/
theorem leafCoeff_eq_zero_above_degree {N K : ℕ} (R T : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) (hT : R.card < T.card) :
    leafCoeff N K R T = 0 := by
  by_contra h
  exact (leafCoeff_support R T hm hR h).2.2.2.not_gt hT

/-- Full reduction preserves every actual square permutation evaluation. -/
theorem leafCoeff_evaluation {π : Edges} {N : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N)
    (hπr : rows π = Finset.Icc 1 N) (hπc : cols π = Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N N) :
    permutationEval π R = ∑ T ∈ terminalFamily N N, leafCoeff N N R T * permutationEval π T := by
  induction R using (measure (fun R => rank (grid N N) (N+N) R)).wf.induction with
  | h R ih =>
    by_cases ht : chosenRewrite R = .terminal
    · have hmem := (mem_terminalFamily N N R).mpr ⟨hR,hm,ht⟩
      simp_rw [leafCoeff_terminal N N R _ ht]
      simp [hmem]
    · calc
        permutationEval π R = ∑ x ∈ children N N R, x.2 * permutationEval π x.1 :=
          chosen_children_evaluation hπ hπg hπr hπc hm hR ht
        _ = ∑ x ∈ children N N R, x.2 *
            (∑ T ∈ terminalFamily N N, leafCoeff N N x.1 T * permutationEval π T) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hcl := child_closed hR hx
          rw [ih x.1 (child_rank_lt hm hR hx) hcl.1 hcl.2]
        _ = ∑ T ∈ terminalFamily N N, leafCoeff N N R T * permutationEval π T := by
          simp_rw [Finset.mul_sum,← mul_assoc]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro T hT
          rw [leafCoeff_recursion R T hm hR,if_neg ht,Finset.sum_mul]

/-- Explicit degree-bounded version of the actual terminal expansion. -/
theorem leafCoeff_evaluation_bounded {π : Edges} {N d : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N)
    (hπr : rows π = Finset.Icc 1 N) (hπc : cols π = Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N N) (hd : R.card ≤ d) :
    permutationEval π R = ∑ T ∈ (terminalFamily N N).filter (fun T => T.card ≤ d),
      leafCoeff N N R T * permutationEval π T := by
  rw [leafCoeff_evaluation hπ hπg hπr hπc R hm hR,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  split_ifs with hTd
  · rfl
  · rw [leafCoeff_eq_zero_above_degree R T hm hR (by omega),zero_mul]

/-- The full finite expansion casts to any coefficient ring; no finiteness or characteristic is used. -/
theorem leafCoeff_evaluation_cast {F : Type*} [CommRing F] {π : Edges} {N : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N)
    (hπr : rows π = Finset.Icc 1 N) (hπc : cols π = Finset.Icc 1 N)
    (R : Edges) (hm : IsMatching R) (hR : R ⊆ grid N N) :
    (permutationEval π R : F) = ∑ T ∈ terminalFamily N N,
      (leafCoeff N N R T : F) * (permutationEval π T : F) := by
  have h := congrArg (fun z : ℤ => (z:F)) (leafCoeff_evaluation hπ hπg hπr hπc R hm hR)
  simpa only [Int.cast_sum,Int.cast_mul] using h

/-- Uniqueness is for the actual deterministic terminal recursion. -/
theorem leafCoeff_unique {N K : ℕ} (f : Edges → Edges → ℤ)
    (hf : ∀ R T, IsMatching R → R ⊆ grid N K →
      f R T = if chosenRewrite R = .terminal then if R=T then 1 else 0 else
        ∑ x ∈ children N K R, x.2 * f x.1 T) :
    ∀ R T, IsMatching R → R ⊆ grid N K → f R T = leafCoeff N K R T := by
  intro R
  induction R using (measure (fun R => rank (grid N K) (N+K) R)).wf.induction with
  | h R ih =>
    intro T hm hR
    rw [hf R T hm hR,leafCoeff_recursion R T hm hR]
    by_cases ht : chosenRewrite R = .terminal
    · rw [if_pos ht,if_pos ht]
    · rw [if_neg ht,if_neg ht]
      apply Finset.sum_congr rfl
      intro x hx
      have hcl := child_closed hR hx
      rw [ih x.1 (child_rank_lt hm hR hx) T hcl.1 hcl.2]

/-- Terminal for the actual selector means that every row and column prefix passes. -/
theorem terminal_iff_no_failures (R : Edges) :
    chosenRewrite R = .terminal ↔ (∀ a, ¬ RowFails R a) ∧ (∀ a, ¬ ColumnFails R a) := by
  by_cases hr : (rowFailures R).Nonempty
  · rw [chosenRewrite,dif_pos hr]
    constructor
    · intro h; contradiction
    · intro h
      obtain ⟨a,ha⟩ := hr
      exact (h.1 a ((mem_rowFailures R a).mp ha)).elim
  · by_cases hc : (columnFailures R).Nonempty
    · rw [chosenRewrite,dif_neg hr,dif_pos hc]
      constructor
      · intro h; contradiction
      · intro h
        obtain ⟨a,ha⟩ := hc
        exact (h.2 a ((mem_columnFailures R a).mp ha)).elim
    · rw [chosenRewrite,dif_neg hr,dif_neg hc]
      constructor
      · intro _
        exact ⟨fun a h => hr ⟨a,(mem_rowFailures R a).mpr h⟩,
          fun a h => hc ⟨a,(mem_columnFailures R a).mpr h⟩⟩
      · intro _; rfl

/-- Empty and positive terminal leaves have their actual Kronecker coefficients. -/
theorem empty_leaf_formula (N K : ℕ) (T : Edges) :
    leafCoeff N K ∅ T = if ∅=T then 1 else 0 := leafCoeff_terminal N K ∅ T empty_terminal

theorem positive_terminal_leaf_formula (T : Edges) :
    leafCoeff 2 2 {(2,2)} T = if {(2,2)}=T then 1 else 0 :=
  leafCoeff_terminal 2 2 {(2,2)} T positive_terminal_example

/-- Exact two-by-two column reduction for every terminal coordinate. -/
theorem column_two_leaf_formula (T : Edges) :
    leafCoeff 2 2 {(2,1)} T = (if ∅=T then 1 else 0) - (if {(2,2)}=T then 1 else 0) := by
  rw [leafCoeff_recursion _ T (by decide) (by decide),if_neg (by decide),column_two_children]
  simp [empty_leaf_formula,positive_terminal_leaf_formula,sub_eq_add_neg]
  split_ifs <;> norm_num

/-- The two row branches cancel in the empty coordinate and leave the positive terminal monomial. -/
theorem row_two_leaf_formula (T : Edges) :
    leafCoeff 2 2 {(1,1)} T = if {(2,2)}=T then 1 else 0 := by
  rw [leafCoeff_recursion _ T (by decide) (by decide),if_neg (by decide),row_two_children]
  simp [empty_leaf_formula,column_two_leaf_formula]

theorem row_two_empty_cancellation :
    leafCoeff 2 2 {(1,1)} ∅ = 0 ∧ leafCoeff 2 2 {(1,1)} {(2,2)} = 1 := by
  simp [row_two_leaf_formula]

theorem column_two_signed_leaves :
    leafCoeff 2 2 {(2,1)} ∅ = 1 ∧ leafCoeff 2 2 {(2,1)} {(2,2)} = -1 := by
  simp [column_two_leaf_formula]

theorem positive_terminal_is_retained :
    leafCoeff 2 2 {(2,2)} {(2,2)} = 1 ∧ normalizer 2 2 {(2,2)} = 0 := by
  simp [positive_terminal_leaf_formula,positive_terminal_normalizer]

/-- An actual rank-stable unfolding instance for arbitrarily many extra steps. -/
theorem arbitrary_extra_unfoldings (N K s : ℕ) (R T : Edges)
    (hm : IsMatching R) (hR : R ⊆ grid N K) :
    leafTruncated N K (rank (grid N K) (N+K) R+s) R T = leafCoeff N K R T := by
  exact (leafCoeff_eq_truncated R T hm hR _ (by omega)).symm

/-- Terminal leaves coincide with the explicit admissible prefix inequalities. -/
theorem terminal_iff_prefix_bounds (R : Edges) :
    chosenRewrite R = .terminal ↔
      (∀ a, chainHeight (rowPrefix R a) ≤ a - (rows (rowPrefix R a)).card) ∧
      (∀ a, chainHeight (columnPrefix R a) ≤ a - (cols (columnPrefix R a)).card) := by
  rw [terminal_iff_no_failures]
  simp only [RowFails,ColumnFails,not_lt]

/-- The actual reduction of a finite integer linear combination of matching monomials. -/
noncomputable def reduceFinite (N K : ℕ) (A : Finset Edges) (w : Edges → ℤ) (T : Edges) : ℤ :=
  ∑ R ∈ A, w R * leafCoeff N K R T

theorem reduceFinite_add (N K : ℕ) (A : Finset Edges) (u v : Edges → ℤ) (T : Edges) :
    reduceFinite N K A (fun R => u R + v R) T = reduceFinite N K A u T + reduceFinite N K A v T := by
  simp [reduceFinite,add_mul,Finset.sum_add_distrib]

/-- Empty-coordinate compatibility holds for the actual finite linear combination map. -/
theorem reduceFinite_empty {N K : ℕ} (A : Finset Edges) (w : Edges → ℤ)
    (hA : ∀ R ∈ A, IsMatching R ∧ R ⊆ grid N K) :
    reduceFinite N K A w ∅ = ∑ R ∈ A, w R * normalizer N K R := by
  apply Finset.sum_congr rfl
  intro R hR
  rw [leafCoeff_empty R (hA R hR).1 (hA R hR).2]

/-- Finite integer linear combinations preserve evaluations under the actual constructed map. -/
theorem reduceFinite_evaluation {π : Edges} {N : ℕ}
    (hπ : IsMatching π) (hπg : π ⊆ grid N N)
    (hπr : rows π = Finset.Icc 1 N) (hπc : cols π = Finset.Icc 1 N)
    (A : Finset Edges) (w : Edges → ℤ) (hA : ∀ R ∈ A, IsMatching R ∧ R ⊆ grid N N) :
    (∑ R ∈ A, w R * permutationEval π R) =
      ∑ T ∈ terminalFamily N N, reduceFinite N N A w T * permutationEval π T := by
  calc
    (∑ R ∈ A, w R * permutationEval π R) =
        ∑ R ∈ A, w R * (∑ T ∈ terminalFamily N N, leafCoeff N N R T * permutationEval π T) := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [leafCoeff_evaluation hπ hπg hπr hπc R (hA R hR).1 (hA R hR).2]
    _ = _ := by
      simp_rw [Finset.mul_sum,← mul_assoc]
      rw [Finset.sum_comm]
      simp only [reduceFinite,Finset.sum_mul]

/-- The reduced linear combination has only admissible leaves within the actual input degree cap. -/
theorem reduceFinite_support {N K d : ℕ} (A : Finset Edges) (w : Edges → ℤ) (T : Edges)
    (hA : ∀ R ∈ A, IsMatching R ∧ R ⊆ grid N K ∧ R.card ≤ d)
    (hv : reduceFinite N K A w T ≠ 0) :
    T ∈ terminalFamily N K ∧ T.card ≤ d := by
  obtain ⟨R,hR,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have hc := leafCoeff_support R T (hA R hR).1 (hA R hR).2.1 (mul_ne_zero_iff.mp hv).2
  exact ⟨(mem_terminalFamily N K T).mpr ⟨hc.2.1,hc.1,hc.2.2.1⟩,hc.2.2.2.trans (hA R hR).2.2⟩

end SelfContainedCycle046
