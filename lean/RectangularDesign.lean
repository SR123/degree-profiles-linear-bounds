import IntegralIndependence

namespace SelfContainedCycle053
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle040 SelfContainedCycle043 SelfContainedCycle044
open SelfContainedCycle045 SelfContainedCycle052

/-- The actual rectangular normalizer, extended by zero on collision monomials. -/
noncomputable def rectCoefficient (n m : ℕ) (P : Edges) : ℤ :=
  if IsMatching P then normalizer n m P else 0

theorem rectCoefficient_matching (n m : ℕ) (P : Edges) (hm : IsMatching P) :
    rectCoefficient n m P=normalizer n m P := by simp [rectCoefficient,hm]

theorem rectCoefficient_collision (n m : ℕ) (P : Edges) (hm : ¬ IsMatching P) :
    rectCoefficient n m P=0 := by simp [rectCoefficient,hm]

theorem rectCoefficient_empty (n m : ℕ) : rectCoefficient n m ∅=1 := by
  simp [rectCoefficient,IsMatching]

theorem nonmatching_insert {P : Edges} (hP : ¬ IsMatching P) (e : ℕ × ℕ) :
    ¬ IsMatching (insert e P) := fun h => hP (matching_subset h (Finset.subset_insert _ _))

theorem grid_into_square {n m : ℕ} (h : n ≤ m) : grid n m ⊆ grid m m := by
  intro e he
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp he
  have hb := Finset.mem_Icc.mp hi
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb.1,hb.2.trans h⟩,hj⟩

theorem insert_grid {n m i j : ℕ} {P : Edges} (hP : P ⊆ grid n m)
    (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 m) :
    insert (i,j) P ⊆ grid n m := Finset.insert_subset (Finset.mem_product.mpr ⟨hi,hj⟩) hP

theorem inserted_card_bound (P : Edges) (e : ℕ × ℕ) : (insert e P).card ≤ P.card+1 :=
  Finset.card_insert_le _ _

/-- Agreement with the existing square design, including collision terms. -/
theorem rectCoefficient_square {N : ℕ} (P : Edges) (hP : P ⊆ grid N N) :
    rectCoefficient N N P=squareDesign N P := by
  by_cases hm : IsMatching P
  · rw [rectCoefficient_matching _ _ _ hm,squareDesign_eq_normalizer P hm hP]
  · rw [rectCoefficient_collision _ _ _ hm,squareDesign_collision hm]

/-- Transfer of the constructed coefficient, without a matching premise on its input. -/
theorem squareDesign_transfer {F : Type*} [CommRing F] {p a n m d : ℕ}
    (hp : p.Prime) [CharP F p] (P : Edges) (hP : P ⊆ grid n m)
    (hd : P.card ≤ d) (hn : 2*d ≤ n) (hdq : d < p^a) (hnm : n ≤ m)
    (hdiv : p^a ∣ m-n) : (squareDesign m P : F)=(rectCoefficient n m P : F) := by
  by_cases hm : IsMatching P
  · rw [squareDesign_eq_normalizer P hm (hP.trans (grid_into_square hnm)),
      rectCoefficient_matching _ _ _ hm]
    exact square_coefficient_transfer hp P hm hP hd hn hdq hnm hdiv
  · rw [squareDesign_collision hm,rectCoefficient_collision _ _ _ hm]

/-- An appended row in an already occupied column is a genuine collision. -/
theorem appended_occupied_collision {n m i j : ℕ} (P : Edges) (hP : P ⊆ grid n m)
    (hi : n < i) (hj : j ∈ cols P) : ¬ IsMatching (insert (i,j) P) := by
  intro hm
  obtain ⟨e,he,hej⟩ := Finset.mem_image.mp hj
  have heq := hm (i,j) (Finset.mem_insert_self _ _) e (Finset.mem_insert_of_mem he) (Or.inr hej.symm)
  have hr := congrArg Prod.fst heq
  have hb := (Finset.mem_Icc.mp (Finset.mem_product.mp (hP he)).1).2
  dsimp only at hr
  omega

/-- The actual omitted square-column terms vanish in all input cases. -/
theorem squareDesign_appended_sum_zero {F : Type*} [CommRing F] {p a n m d j : ℕ}
    (hp : p.Prime) [CharP F p] (P : Edges) (hP : P ⊆ grid n m)
    (hj : j ∈ Finset.Icc 1 m) (hd : P.card+1 ≤ d) (hn : 2*d ≤ n)
    (hdq : d < p^a) (hnm : n ≤ m) (hdiv : p^a ∣ m-n) :
    (∑ i ∈ Finset.Icc (n+1) m, (squareDesign m (insert (i,j) P) : F))=0 := by
  by_cases hm : IsMatching P
  · by_cases hjused : j ∈ cols P
    · apply Finset.sum_eq_zero
      intro i hi
      have hn' := (Finset.mem_Icc.mp hi).1
      rw [squareDesign_collision (appended_occupied_collision P hP (by omega) hjused),Int.cast_zero]
    · calc
        _ = ∑ i ∈ Finset.Icc (n+1) m, (normalizer m m (addEdge P i j) : F) := by
          apply Finset.sum_congr rfl
          intro i hi
          obtain ⟨hil,hih⟩ := Finset.mem_Icc.mp hi
          have hmi : IsMatching (addEdge P i j) :=
            addEdge_matching P hm (new_row_unused (i:=i) P hP (by omega)) hjused
          have hig : i ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨by omega,hih⟩
          exact congrArg (fun z : ℤ => (z:F))
            (squareDesign_eq_normalizer (addEdge P i j) hmi
              (insert_grid (hP.trans (grid_into_square hnm)) hig hj))
        _ = 0 := square_appended_row_sum_zero hp P hm hP hj hjused hd hn hdq hnm hdiv
  · apply Finset.sum_eq_zero
    intro i _
    rw [squareDesign_collision (nonmatching_insert hm (i,j)),Int.cast_zero]

/-- The old row-index interval and appended interval form exactly the square interval. -/
theorem row_interval_partition {n m : ℕ} (hnm : n ≤ m) :
    Finset.Icc 1 n ∪ Finset.Icc (n+1) m = Finset.Icc 1 m := by
  ext i
  simp only [Finset.mem_union,Finset.mem_Icc]
  omega

theorem row_intervals_disjoint (n m : ℕ) : Disjoint (Finset.Icc 1 n) (Finset.Icc (n+1) m) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have h := Finset.mem_Icc.mp hi
  have h' := Finset.mem_Icc.mp hj
  omega

/-- The row equation for the actual rectangular coefficient in the proved degree range. -/
theorem rectCoefficient_row_sum {F : Type*} [CommRing F] {p a n m d i : ℕ}
    (hp : p.Prime) [CharP F p] (P : Edges) (hP : P ⊆ grid n m)
    (hi : i ∈ Finset.Icc 1 n) (hd : P.card+1 ≤ d) (hn : 2*d ≤ n)
    (hdq : d < p^a) (hnm : n ≤ m) (hdiv : p^a ∣ m-n) :
    (∑ j ∈ Finset.Icc 1 m, (rectCoefficient n m (insert (i,j) P) : F))=(rectCoefficient n m P : F) := by
  have him : i ∈ Finset.Icc 1 m := by
    obtain ⟨hil,hih⟩ := Finset.mem_Icc.mp hi
    exact Finset.mem_Icc.mpr ⟨hil,hih.trans hnm⟩
  calc
    _ = ∑ j ∈ Finset.Icc 1 m, (squareDesign m (insert (i,j) P) : F) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (squareDesign_transfer hp _ (insert_grid hP hi hj)
        ((inserted_card_bound P _).trans hd) hn hdq hnm hdiv).symm
    _ = (squareDesign m P : F) := squareDesign_row_sum_cast P (hP.trans (grid_into_square hnm)) him
    _ = _ := squareDesign_transfer hp P hP (by omega) hn hdq hnm hdiv

/-- The column equation includes the proved cancellation of all appended rows. -/
theorem rectCoefficient_col_sum {F : Type*} [CommRing F] {p a n m d j : ℕ}
    (hp : p.Prime) [CharP F p] (P : Edges) (hP : P ⊆ grid n m)
    (hj : j ∈ Finset.Icc 1 m) (hd : P.card+1 ≤ d) (hn : 2*d ≤ n)
    (hdq : d < p^a) (hnm : n ≤ m) (hdiv : p^a ∣ m-n) :
    (∑ i ∈ Finset.Icc 1 n, (rectCoefficient n m (insert (i,j) P) : F))=(rectCoefficient n m P : F) := by
  have hcol := squareDesign_col_sum_cast (F:=F) P (hP.trans (grid_into_square hnm)) hj
  rw [← row_interval_partition hnm,Finset.sum_union (row_intervals_disjoint n m),
    squareDesign_appended_sum_zero hp P hP hj hd hn hdq hnm hdiv,add_zero] at hcol
  calc
    _ = ∑ i ∈ Finset.Icc 1 n, (squareDesign m (insert (i,j) P) : F) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (squareDesign_transfer hp _ (insert_grid hP hi hj)
        ((inserted_card_bound P _).trans hd) hn hdq hnm hdiv).symm
    _ = (squareDesign m P : F) := hcol
    _ = _ := squareDesign_transfer hp P hP (by omega) hn hdq hnm hdiv

/-- Explicit matching-design equations; the construction below proves all of them. -/
def IsMatchingDesign {F : Type*} [CommRing F] (n m d : ℕ) (ψ : Edges → F) : Prop :=
  ψ ∅=1 ∧ (∀ P, ¬ IsMatching P → ψ P=0) ∧
    (∀ P, P ⊆ grid n m → P.card+1 ≤ d → ∀ i ∈ Finset.Icc 1 n,
      (∑ j ∈ Finset.Icc 1 m, ψ (insert (i,j) P))=ψ P) ∧
    (∀ P, P ⊆ grid n m → P.card+1 ≤ d → ∀ j ∈ Finset.Icc 1 m,
      (∑ i ∈ Finset.Icc 1 n, ψ (insert (i,j) P))=ψ P)

/-- A proved normalized rectangular design, not a hypothesized one. -/
theorem actual_rectangular_design {F : Type*} [CommRing F] {p a n m d : ℕ}
    (hp : p.Prime) [CharP F p] (hn : 2*d ≤ n) (hdq : d < p^a)
    (hnm : n ≤ m) (hdiv : p^a ∣ m-n) :
    IsMatchingDesign n m d (fun P => (rectCoefficient n m P : F)) := by
  refine ⟨by simp only [rectCoefficient_empty,Int.cast_one],?_,?_,?_⟩
  · intro P hm
    simp only [rectCoefficient_collision _ _ _ hm,Int.cast_zero]
  · intro P hP hd i hi
    exact rectCoefficient_row_sum hp P hP hi hd hn hdq hnm hdiv
  · intro P hP hd j hj
    exact rectCoefficient_col_sum hp P hP hj hd hn hdq hnm hdiv

/-- The concrete family has a constructed design at every degree strictly below q. -/
theorem concrete_family_design {F : Type*} [CommRing F] [CharP F 2] (a d : ℕ)
    (hd : d < 2^a) :
    IsMatchingDesign (3*2^a) (6*2^a) d (fun P => (rectCoefficient (3*2^a) (6*2^a) P : F)) := by
  apply actual_rectangular_design (p:=2) (a:=a) (by decide) (by omega) hd (by omega)
  have heq : 6*2^a-3*2^a=2^a*3 := by omega
  rw [heq]
  exact dvd_mul_right _ _

/-- All algebraic equations are retained under lowering the requested degree. -/
theorem matchingDesign_mono {F : Type*} [CommRing F] {n m d e : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) (he : e ≤ d) : IsMatchingDesign n m e ψ := by
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro P hP hd i hi
    exact h.2.2.1 P hP (hd.trans he) i hi
  · intro P hP hd j hj
    exact h.2.2.2 P hP (hd.trans he) j hj

/-- Transposition is applied to the completed design, not asserted of its deterministic normalizer. -/
theorem matchingDesign_transpose {F : Type*} [CommRing F] {n m d : ℕ} {ψ : Edges → F}
    (h : IsMatchingDesign n m d ψ) : IsMatchingDesign m n d (fun P => ψ (transpose P)) := by
  have hins : ∀ P i j, transpose (insert (i,j) P)=insert (j,i) (transpose P) := by
    intro P i j
    simp [transpose,Finset.map_insert,swapEmbedding]
  refine ⟨?_,?_,?_,?_⟩
  · simpa [transpose] using h.1
  · intro P hm
    exact h.2.1 (transpose P) (fun ht => hm ((matching_transpose P).mp ht))
  · intro P hP hd i hi
    have hc : (transpose P).card+1 ≤ d := by simpa using hd
    simpa only [hins] using h.2.2.2 (transpose P) (transpose_subset_grid hP) hc i hi
  · intro P hP hd j hj
    have hc : (transpose P).card+1 ≤ d := by simpa using hd
    simpa only [hins] using h.2.2.1 (transpose P) (transpose_subset_grid hP) hc j hj

/-- The actual constructed design has Boolean support idempotence under repeated insertion. -/
theorem rectCoefficient_repeat_insert (n m : ℕ) (P : Edges) (e : ℕ × ℕ) :
    rectCoefficient n m (insert e (insert e P))=rectCoefficient n m (insert e P) := by simp

/-- Proper rectangular parameters give a real normalized degree-two design in characteristic two. -/
theorem four_by_eight_design :
    IsMatchingDesign 4 8 2 (fun P => (rectCoefficient 4 8 P : ZMod 2)) :=
  actual_rectangular_design (p:=2) (a:=2) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Its transpose is explicitly constructed, rather than identified with another normalizer. -/
theorem eight_by_four_design :
    IsMatchingDesign 8 4 2 (fun P => (rectCoefficient 4 8 (transpose P) : ZMod 2)) :=
  matchingDesign_transpose four_by_eight_design

/-- The matching {(2,2)} is an actual terminal nonempty input in this rectangle. -/
theorem four_by_eight_terminal_value : rectCoefficient 4 8 {(2,2)}=0 := by
  rw [rectCoefficient_matching _ _ _ (by decide)]
  exact normalizer_terminal (by decide) (by decide) (by decide) positive_terminal_example

/-- Both occupied and unused-column cases are exercised at a nonempty old matching. -/
theorem four_by_eight_nonempty_equations :
    (rectCoefficient 4 8 ∅ : ZMod 2)=1 ∧
    (∑ j ∈ Finset.Icc 1 8, (rectCoefficient 4 8 (insert (1,j) {(2,2)}) : ZMod 2))=0 ∧
    (∑ i ∈ Finset.Icc 1 4, (rectCoefficient 4 8 (insert (i,2) {(2,2)}) : ZMod 2))=0 ∧
    (∑ i ∈ Finset.Icc 1 4, (rectCoefficient 4 8 (insert (i,3) {(2,2)}) : ZMod 2))=0 := by
  have hr := four_by_eight_design.2.2.1 {(2,2)} (by decide) (by decide) 1 (by decide)
  have hc2 := four_by_eight_design.2.2.2 {(2,2)} (by decide) (by decide) 2 (by decide)
  have hc3 := four_by_eight_design.2.2.2 {(2,2)} (by decide) (by decide) 3 (by decide)
  simp only [four_by_eight_terminal_value,Int.cast_zero] at hr hc2 hc3
  exact ⟨four_by_eight_design.1,hr,hc2,hc3⟩

/-- There is no actual covering matching in a four-by-eight rectangle. -/
theorem four_by_eight_no_covering_matching :
    ¬ ∃ P : Edges, IsMatching P ∧ rows P=Finset.Icc 1 4 ∧ cols P=Finset.Icc 1 8 := by
  rintro ⟨P,hm,hr,hc⟩
  have hh : (rows P).card=(cols P).card := (matching_rows_card hm).trans (matching_cols_card hm).symm
  rw [hr,hc] at hh
  norm_num at hh

/-- A normalized design on an unsatisfiable matching geometry is not the zero functional. -/
theorem four_by_eight_design_nonzero :
    (fun P => (rectCoefficient 4 8 P : ZMod 2)) ≠ (fun _ : Edges => 0) := by
  intro h
  have he := congrFun h ∅
  have hunit := four_by_eight_design.1
  have hc : (1 : ZMod 2)=0 := hunit.symm.trans he
  exact one_ne_zero hc

/-- Zero appended length and exponent-zero/degree-zero cases retain their precise budgets. -/
theorem boundary_design_examples :
    IsMatchingDesign 4 4 2 (fun P => (rectCoefficient 4 4 P : ZMod 2)) ∧
    IsMatchingDesign 3 6 0 (fun P => (rectCoefficient 3 6 P : ZMod 2)) ∧
    (∑ i ∈ Finset.Icc 5 4, (squareDesign 4 (insert (i,1) ∅) : ZMod 2))=0 := by
  refine ⟨?_,?_,?_⟩
  · exact actual_rectangular_design (p:=2) (a:=2) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact concrete_family_design 0 0 (by decide)
  · simp

/-- Odd-characteristic compatibility uses the same proved construction. -/
theorem characteristic_three_design :
    IsMatchingDesign 4 7 2 (fun P => (rectCoefficient 4 7 P : ZMod 3)) :=
  actual_rectangular_design (p:=3) (a:=1) (by decide) (by decide) (by decide) (by decide) (by decide)

end SelfContainedCycle053
