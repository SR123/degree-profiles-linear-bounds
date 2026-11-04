import BlockMinimum

namespace SelfContainedCycle052
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle045 SelfContainedCycle046
open SelfContainedCycle047 SelfContainedCycle048 SelfContainedCycle050 SelfContainedCycle051

/-- Actual square permutations are finite matching edge sets covering both sides. -/
def SquarePermutation (N : ℕ) (π : Edges) : Prop :=
  IsMatching π ∧ rows π=Finset.Icc 1 N ∧ cols π=Finset.Icc 1 N

theorem squarePermutation_grid {N : ℕ} {π : Edges} (hπ : SquarePermutation N π) :
    π ⊆ grid N N := by
  intro e he
  apply Finset.mem_product.mpr
  constructor
  · rw [← hπ.2.1]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  · rw [← hπ.2.2]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩

theorem blockPermutation_square {N : ℕ} {R : Edges} (hm : IsMatching R)
    (hR : R ⊆ grid N N) (ht : chosenRewrite R = .terminal) (σ : Choices hm hR ht) :
    SquarePermutation N (blockPermutation hm hR ht σ) :=
  ⟨blockPermutation_matching hm hR ht σ,blockPermutation_rows hm hR ht σ,
    blockPermutation_cols hm hR ht σ⟩

/-- Below the chosen rank, every off-diagonal integer moment vanishes. -/
theorem moment_zero_of_rank_le {N : ℕ} {R P : Edges} (hm : IsMatching R)
    (hR : R ⊆ grid N N) (ht : chosenRewrite R = .terminal)
    (hneq : P ≠ R) (hrank : rank (grid N N) (N+N) P ≤ rank (grid N N) (N+N) R) :
    blockMoment hm hR ht P = 0 := by
  by_cases hsmall : P.card < R.card
  · exact blockMoment_below_degree hm hR ht P hsmall
  have hcard : P.card=R.card := by
    by_contra h
    have hbig : R.card < P.card := by omega
    have hlt := rank_lt_of_card_lt (H:=N+N) hR hbig
    omega
  by_contra hv
  have hw := exact_degree_moment_strict_minimum hm hR ht P hcard hv hneq
  have hlt := rank_lt_of_equal_card (G:=grid N N) (H:=N+N) hcard.symm hw
  omega

/-- Every zero evaluation relation gives a zero relation under each actual signed moment. -/
theorem moment_sum_eq_zero {F : Type*} [CommRing F] {N : ℕ} {R : Edges}
    (hm : IsMatching R) (hR : R ⊆ grid N N) (ht : chosenRewrite R = .terminal)
    (S : Finset Edges) (c : Edges → F)
    (heval : ∀ π, SquarePermutation N π → ∑ P ∈ S, c P * (permutationEval π P : F) = 0) :
    ∑ P ∈ S, c P * (blockMoment hm hR ht P : F) = 0 := by
  classical
  calc
    _ = ∑ σ : Choices hm hR ht, (blockWeight hm hR ht σ : F) *
        (∑ P ∈ S, c P * (permutationEval (blockPermutation hm hR ht σ) P : F)) := by
      simp only [blockMoment,Int.cast_sum,Int.cast_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro P _
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      rw [heval _ (blockPermutation_square hm hR ht σ),mul_zero]

/-- Integral independence, valid over every commutative ring including rings with zero divisors. -/
theorem terminal_evaluations_independent {F : Type*} [CommRing F] (N : ℕ)
    (S : Finset Edges) (c : Edges → F)
    (hS : ∀ R ∈ S, R ∈ terminalFamily N N)
    (heval : ∀ π, SquarePermutation N π → ∑ R ∈ S, c R * (permutationEval π R : F) = 0) :
    ∀ R ∈ S, c R = 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨Q,hQS,hQnz⟩ := h
  let nz := S.filter (fun R => c R ≠ 0)
  have hnon : nz.Nonempty := ⟨Q,Finset.mem_filter.mpr ⟨hQS,hQnz⟩⟩
  obtain ⟨R,hRnz,hmax⟩ := Finset.exists_max_image nz (rank (grid N N) (N+N)) hnon
  obtain ⟨hRS,hcnz⟩ := Finset.mem_filter.mp hRnz
  obtain ⟨hRg,hm,ht⟩ := (mem_terminalFamily N N R).mp (hS R hRS)
  have hsum := moment_sum_eq_zero hm hRg ht S c heval
  have hoff : ∀ P ∈ S, P ≠ R → c P * (blockMoment hm hRg ht P : F) = 0 := by
    intro P hPS hne
    by_cases hz : c P=0
    · rw [hz,zero_mul]
    · have hp := hmax P (Finset.mem_filter.mpr ⟨hPS,hz⟩)
      rw [moment_zero_of_rank_le hm hRg ht hne hp,Int.cast_zero,mul_zero]
  rw [Finset.sum_eq_single R hoff (fun h => (h hRS).elim)] at hsum
  exact hcnz ((diagonal_moment_cast_isUnit (F:=F) hm hRg ht).mul_left_eq_zero.mp hsum)

/-- Two coefficient vectors on the actual terminal family with equal evaluations coincide. -/
theorem terminal_coefficients_unique {F : Type*} [CommRing F] (N : ℕ) (c d : Edges → F)
    (heval : ∀ π, SquarePermutation N π →
      ∑ R ∈ terminalFamily N N, c R * (permutationEval π R : F) =
      ∑ R ∈ terminalFamily N N, d R * (permutationEval π R : F)) :
    ∀ R ∈ terminalFamily N N, c R=d R := by
  have h := terminal_evaluations_independent N (terminalFamily N N) (fun R => c R-d R)
    (fun _ h => h) (by
      intro π hπ
      simp only [sub_mul,Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (heval π hπ))
  intro R hR
  exact sub_eq_zero.mp (h R hR)

/-- The constructed reduction is the unique terminal expansion of each matching's evaluation. -/
theorem leafCoeff_expansion_unique {F : Type*} [CommRing F] {N : ℕ} (P : Edges)
    (hm : IsMatching P) (hP : P ⊆ grid N N) (c : Edges → F)
    (heval : ∀ π, SquarePermutation N π →
      ∑ R ∈ terminalFamily N N, c R * (permutationEval π R : F) = (permutationEval π P : F)) :
    ∀ R ∈ terminalFamily N N, c R = (leafCoeff N N P R : F) := by
  apply terminal_coefficients_unique N c (fun R => (leafCoeff N N P R : F))
  intro π hπ
  rw [heval π hπ]
  exact leafCoeff_evaluation_cast hπ.1 (squarePermutation_grid hπ) hπ.2.1 hπ.2.2 P hm hP

/-- Vanishing finite combinations have every actual reduced coordinate zero. -/
theorem reduced_coordinates_of_zero_evaluation {F : Type*} [CommRing F] {N : ℕ}
    (S : Finset Edges) (c : Edges → F)
    (hS : ∀ P ∈ S, IsMatching P ∧ P ⊆ grid N N)
    (heval : ∀ π, SquarePermutation N π → ∑ P ∈ S, c P * (permutationEval π P : F) = 0) :
    ∀ R ∈ terminalFamily N N, ∑ P ∈ S, c P * (leafCoeff N N P R : F) = 0 := by
  apply terminal_evaluations_independent N (terminalFamily N N)
    (fun R => ∑ P ∈ S, c P * (leafCoeff N N P R : F)) (fun _ h => h)
  intro π hπ
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ P ∈ S, c P * (permutationEval π P : F) := by
      apply Finset.sum_congr rfl
      intro P hPS
      rw [leafCoeff_evaluation_cast hπ.1 (squarePermutation_grid hπ) hπ.2.1 hπ.2.2
        P (hS P hPS).1 (hS P hPS).2,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R _
      ring
    _ = 0 := heval π hπ

/-- A nontrivial characteristic-two instance includes the empty and the unequal-complement example. -/
theorem characteristic_two_independence_example (a b : ZMod 2)
    (h : ∀ π, SquarePermutation 6 π →
      a * (permutationEval π ∅ : ZMod 2) + b * (permutationEval π exampleMatching : ZMod 2) = 0) :
    a=0 ∧ b=0 := by
  let S : Finset Edges := {∅,exampleMatching}
  let c : Edges → ZMod 2 := fun R => if R=∅ then a else b
  have hs : ∀ R ∈ S, R ∈ terminalFamily 6 6 := by
    intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact (mem_terminalFamily _ _ _).mpr ⟨Finset.empty_subset _,by simp [IsMatching],empty_terminal⟩
    · have hR' := Finset.mem_singleton.mp hR
      subst R
      exact (mem_terminalFamily _ _ _).mpr ⟨example_grid,example_matching,example_terminal⟩
  have hev : ∀ π, SquarePermutation 6 π → ∑ R ∈ S, c R * (permutationEval π R : ZMod 2)=0 := by
    intro π hπ
    have hn : (∅ : Edges) ≠ exampleMatching := by decide
    simpa [S,c,hn,Ne.symm hn] using h π hπ
  have hi := terminal_evaluations_independent 6 S c hs hev
  constructor
  · simpa [c] using hi ∅ (by simp [S])
  · simpa [c,exampleMatching] using hi exampleMatching (by simp [S])

/-- The theorem also applies to coefficients with zero divisors, without cancellation assumptions. -/
theorem zero_divisor_coefficients_example (a b : ZMod 4)
    (h : ∀ π, SquarePermutation 2 π →
      a + b * (permutationEval π {(2,2)} : ZMod 4) = 0) : a=0 ∧ b=0 := by
  let S : Finset Edges := {∅,{(2,2)}}
  let c : Edges → ZMod 4 := fun R => if R=∅ then a else b
  have hs : ∀ R ∈ S, R ∈ terminalFamily 2 2 := by
    intro R hR
    rcases Finset.mem_insert.mp hR with rfl | hR
    · exact (mem_terminalFamily _ _ _).mpr ⟨Finset.empty_subset _,by simp [IsMatching],empty_terminal⟩
    · have hR' := Finset.mem_singleton.mp hR
      subst R
      exact (mem_terminalFamily _ _ _).mpr ⟨by decide,by decide,by decide⟩
  have hev : ∀ π, SquarePermutation 2 π → ∑ R ∈ S, c R * (permutationEval π R : ZMod 4)=0 := by
    intro π hπ
    simpa [S,c] using h π hπ
  have hi := terminal_evaluations_independent 2 S c hs hev
  constructor
  · simpa [c] using hi ∅ (by simp [S])
  · simpa [c] using hi {(2,2)} (by simp [S])

/-- Extend the actual terminal coefficient by zero on collision monomials. -/
noncomputable def squareLeafCoeff (N : ℕ) (P T : Edges) : ℤ :=
  if IsMatching P then leafCoeff N N P T else 0

theorem squareLeafCoeff_matching {N : ℕ} {P : Edges} (hm : IsMatching P) (T : Edges) :
    squareLeafCoeff N P T = leafCoeff N N P T := by simp [squareLeafCoeff,hm]

theorem squareLeafCoeff_collision {N : ℕ} {P : Edges} (hm : ¬ IsMatching P) (T : Edges) :
    squareLeafCoeff N P T = 0 := by simp [squareLeafCoeff,hm]

theorem permutationEval_collision {π P : Edges} (hπ : IsMatching π) (hP : ¬ IsMatching P) :
    permutationEval π P=0 := by
  have hn : ¬ P ⊆ π := fun h => hP (matching_subset hπ h)
  simp [permutationEval,hn]

/-- Every square-supported monomial, including collisions, has the actual terminal expansion. -/
theorem squareLeafCoeff_evaluation {N : ℕ} {π : Edges} (hπ : SquarePermutation N π)
    (P : Edges) (hP : P ⊆ grid N N) :
    permutationEval π P = ∑ T ∈ terminalFamily N N, squareLeafCoeff N P T * permutationEval π T := by
  by_cases hm : IsMatching P
  · simp only [squareLeafCoeff_matching hm]
    exact leafCoeff_evaluation hπ.1 (squarePermutation_grid hπ) hπ.2.1 hπ.2.2 P hm hP
  · simp only [squareLeafCoeff_collision hm,zero_mul,Finset.sum_const_zero]
    exact permutationEval_collision hπ.1 hm

/-- The ordinary totality identity at an actual permutation, with no normalization assumed. -/
theorem permutationEval_row_sum {N : ℕ} {π : Edges} (hπ : SquarePermutation N π)
    (P : Edges) {i : ℕ} (hi : i ∈ Finset.Icc 1 N) :
    (∑ j ∈ Finset.Icc 1 N, permutationEval π (insert (i,j) P)) = permutationEval π P := by
  have hir : i ∈ rows π := by rw [hπ.2.1]; exact hi
  obtain ⟨e,he,hei⟩ := Finset.mem_image.mp hir
  have hej : e.2 ∈ Finset.Icc 1 N := by
    rw [← hπ.2.2]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hmem : (i,e.2) ∈ π := by simpa only [← hei] using he
  rw [Finset.sum_eq_single e.2]
  · simp only [permutationEval,Finset.insert_subset_iff,hmem,true_and]
  · intro j _ hj
    have hn : (i,j) ∉ π := by
      intro h
      have heq := hπ.1 (i,j) h (i,e.2) hmem (Or.inl rfl)
      exact hj (congrArg Prod.snd heq)
    simp [permutationEval,Finset.insert_subset_iff,hn]
  · intro h
    exact (h hej).elim

/-- The column identity is proved directly, without a transpose-equivariance premise. -/
theorem permutationEval_col_sum {N : ℕ} {π : Edges} (hπ : SquarePermutation N π)
    (P : Edges) {j : ℕ} (hj : j ∈ Finset.Icc 1 N) :
    (∑ i ∈ Finset.Icc 1 N, permutationEval π (insert (i,j) P)) = permutationEval π P := by
  have hjc : j ∈ cols π := by rw [hπ.2.2]; exact hj
  obtain ⟨e,he,hej⟩ := Finset.mem_image.mp hjc
  have hei : e.1 ∈ Finset.Icc 1 N := by
    rw [← hπ.2.1]
    exact Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hmem : (e.1,j) ∈ π := by simpa only [← hej] using he
  rw [Finset.sum_eq_single e.1]
  · simp only [permutationEval,Finset.insert_subset_iff,hmem,true_and]
  · intro i _ hi
    have hn : (i,j) ∉ π := by
      intro h
      have heq := hπ.1 (i,j) h (e.1,j) hmem (Or.inr rfl)
      exact hi (congrArg Prod.fst heq)
    simp [permutationEval,Finset.insert_subset_iff,hn]
  · intro h
    exact (h hei).elim

/-- Every actual leaf coordinate obeys all square row design equations. -/
theorem squareLeafCoeff_row_sum {N : ℕ} (P : Edges) (hP : P ⊆ grid N N)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 N) (T : Edges) (hT : T ∈ terminalFamily N N) :
    (∑ j ∈ Finset.Icc 1 N, squareLeafCoeff N (insert (i,j) P) T) = squareLeafCoeff N P T := by
  apply terminal_coefficients_unique (F:=ℤ) N
    (fun T => ∑ j ∈ Finset.Icc 1 N, squareLeafCoeff N (insert (i,j) P) T)
    (fun T => squareLeafCoeff N P T) ?_ T hT
  intro π hπ
  simp only [Int.cast_id,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j ∈ Finset.Icc 1 N, permutationEval π (insert (i,j) P) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (squareLeafCoeff_evaluation hπ _
        (Finset.insert_subset (Finset.mem_product.mpr ⟨hi,hj⟩) hP)).symm
    _ = permutationEval π P := permutationEval_row_sum hπ P hi
    _ = _ := squareLeafCoeff_evaluation hπ P hP

/-- Every actual leaf coordinate obeys all square column design equations. -/
theorem squareLeafCoeff_col_sum {N : ℕ} (P : Edges) (hP : P ⊆ grid N N)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 N) (T : Edges) (hT : T ∈ terminalFamily N N) :
    (∑ i ∈ Finset.Icc 1 N, squareLeafCoeff N (insert (i,j) P) T) = squareLeafCoeff N P T := by
  apply terminal_coefficients_unique (F:=ℤ) N
    (fun T => ∑ i ∈ Finset.Icc 1 N, squareLeafCoeff N (insert (i,j) P) T)
    (fun T => squareLeafCoeff N P T) ?_ T hT
  intro π hπ
  simp only [Int.cast_id,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i ∈ Finset.Icc 1 N, permutationEval π (insert (i,j) P) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (squareLeafCoeff_evaluation hπ _
        (Finset.insert_subset (Finset.mem_product.mpr ⟨hi,hj⟩) hP)).symm
    _ = permutationEval π P := permutationEval_col_sum hπ P hj
    _ = _ := squareLeafCoeff_evaluation hπ P hP

/-- Actual leaf coordinates are Kronecker-normalized on the terminal family. -/
theorem squareLeafCoeff_terminal {N : ℕ} (P T : Edges) (hm : IsMatching P)
    (ht : chosenRewrite P = .terminal) : squareLeafCoeff N P T = if P=T then 1 else 0 := by
  rw [squareLeafCoeff_matching hm,leafCoeff_terminal N N P T ht]

/-- Degree support is inherited from the actual finite reduction. -/
theorem squareLeafCoeff_above_degree {N : ℕ} (P T : Edges) (hP : P ⊆ grid N N)
    (hc : P.card < T.card) : squareLeafCoeff N P T=0 := by
  by_cases hm : IsMatching P
  · rw [squareLeafCoeff_matching hm,leafCoeff_eq_zero_above_degree P T hm hP hc]
  · exact squareLeafCoeff_collision hm T

noncomputable def squareDesign (N : ℕ) (P : Edges) : ℤ := squareLeafCoeff N P ∅

theorem empty_mem_terminalFamily (N : ℕ) : (∅ : Edges) ∈ terminalFamily N N :=
  (mem_terminalFamily _ _ _).mpr ⟨Finset.empty_subset _,by simp [IsMatching],empty_terminal⟩

theorem squareDesign_normalized (N : ℕ) : squareDesign N ∅ = 1 := by
  rw [squareDesign,squareLeafCoeff_terminal ∅ ∅ (by simp [IsMatching]) empty_terminal,if_pos rfl]

theorem squareDesign_row_sum {N : ℕ} (P : Edges) (hP : P ⊆ grid N N)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 N) :
    (∑ j ∈ Finset.Icc 1 N, squareDesign N (insert (i,j) P)) = squareDesign N P :=
  squareLeafCoeff_row_sum P hP hi ∅ (empty_mem_terminalFamily N)

theorem squareDesign_col_sum {N : ℕ} (P : Edges) (hP : P ⊆ grid N N)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 N) :
    (∑ i ∈ Finset.Icc 1 N, squareDesign N (insert (i,j) P)) = squareDesign N P :=
  squareLeafCoeff_col_sum P hP hj ∅ (empty_mem_terminalFamily N)

theorem squareDesign_collision {N : ℕ} {P : Edges} (hm : ¬ IsMatching P) : squareDesign N P=0 :=
  squareLeafCoeff_collision hm ∅

/-- Exact compatibility with the earlier scalar normalizer, rather than a new unrelated design. -/
theorem squareDesign_eq_normalizer {N : ℕ} (P : Edges) (hm : IsMatching P) (hP : P ⊆ grid N N) :
    squareDesign N P=SelfContainedCycle040.normalizer N N P := by
  rw [squareDesign,squareLeafCoeff_matching hm,leafCoeff_empty P hm hP]

/-- Square design equations survive every coefficient-ring base change. -/
theorem squareDesign_row_sum_cast {F : Type*} [CommRing F] {N : ℕ}
    (P : Edges) (hP : P ⊆ grid N N) {i : ℕ} (hi : i ∈ Finset.Icc 1 N) :
    (∑ j ∈ Finset.Icc 1 N, (squareDesign N (insert (i,j) P) : F)) = (squareDesign N P : F) := by
  have h := congrArg (fun z : ℤ => (z:F)) (squareDesign_row_sum P hP hi)
  simpa only [Int.cast_sum] using h

theorem squareDesign_col_sum_cast {F : Type*} [CommRing F] {N : ℕ}
    (P : Edges) (hP : P ⊆ grid N N) {j : ℕ} (hj : j ∈ Finset.Icc 1 N) :
    (∑ i ∈ Finset.Icc 1 N, (squareDesign N (insert (i,j) P) : F)) = (squareDesign N P : F) := by
  have h := congrArg (fun z : ℤ => (z:F)) (squareDesign_col_sum P hP hj)
  simpa only [Int.cast_sum] using h

/-- Both a diagonal and a non-diagonal actual square permutation are present. -/
theorem actual_square_permutation_examples :
    SquarePermutation 2 {(1,1),(2,2)} ∧ SquarePermutation 2 {(1,2),(2,1)} ∧
    SquarePermutation 6 {(1,1),(2,2),(3,5),(4,3),(5,4),(6,6)} := by
  unfold SquarePermutation
  decide

/-- The constructed scalar design has explicit normalized two-by-two values. -/
theorem actual_square_design_example :
    squareDesign 2 ∅=1 ∧ squareDesign 2 {(1,1)}=0 ∧ squareDesign 2 {(1,2)}=1 ∧
    squareDesign 2 {(2,1)}=1 ∧ squareDesign 2 {(2,2)}=0 ∧
    squareDesign 2 {(1,1),(1,2)}=0 := by
  have h22 : squareDesign 2 {(2,2)}=0 := by
    rw [squareDesign,squareLeafCoeff_terminal _ _ (by decide) (by decide),if_neg (by decide)]
  have hr1 := squareDesign_row_sum (N:=2) ∅ (Finset.empty_subset _) (i:=1) (by decide)
  have hr2 := squareDesign_row_sum (N:=2) ∅ (Finset.empty_subset _) (i:=2) (by decide)
  have hc2 := squareDesign_col_sum (N:=2) ∅ (Finset.empty_subset _) (j:=2) (by decide)
  have hI : Finset.Icc 1 2 = {1,2} := by decide
  simp [hI,Finset.sum_insert,squareDesign_normalized,h22] at hr1 hr2 hc2
  refine ⟨squareDesign_normalized _,?_,hc2,hr2,h22,squareDesign_collision (by decide)⟩
  omega

/-- The same concrete normalization survives characteristic two and a ring with zero divisors. -/
theorem square_design_base_change_examples :
    (squareDesign 2 ∅ : ZMod 2)=1 ∧ (squareDesign 2 {(1,2)} : ZMod 2)=1 ∧
    (squareDesign 2 ∅ : ZMod 4)=1 ∧ (squareDesign 2 {(1,1),(1,2)} : ZMod 4)=0 := by
  simp only [actual_square_design_example.1,actual_square_design_example.2.2.1,
    actual_square_design_example.2.2.2.2.2,Int.cast_one,Int.cast_zero,and_self]

end SelfContainedCycle052
