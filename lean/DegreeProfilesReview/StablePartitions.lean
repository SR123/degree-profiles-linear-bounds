/-
Prompt 02, elementary layer: bounded-tail partitions, first-row deletion,
strict stability, p-regularity and dominance.

This file deliberately imports nothing beyond the Lean core library.  It
contains no categorical statement and no external mathematical hypothesis.

Conventions.  A partition is a weakly decreasing list of positive natural
numbers.  `a :: μ` has first row `a` and tail `μ`; `tailSize (a :: μ) = μ.sum`.
-/

namespace DegreeProfilesReview.StablePartitions

/-! ### Basic definitions -/

/-- A weakly decreasing list of positive naturals. -/
def IsPartition (l : List Nat) : Prop :=
  l.Pairwise (fun x y => y ≤ x) ∧ ∀ x ∈ l, 0 < x

/-- `l` is a partition of `t`. -/
def IsPartitionOf (t : Nat) (l : List Nat) : Prop :=
  IsPartition l ∧ l.sum = t

/-- First row (0 for the empty partition). -/
def firstRow : List Nat → Nat
  | [] => 0
  | a :: _ => a

/-- Tail size `|λ| - λ₁`. -/
def tailSize : List Nat → Nat
  | [] => 0
  | _ :: μ => μ.sum

/-- Bounded-tail partitions of `t`: the label set of `C_(t,r)`. -/
def BoundedTail (t r : Nat) (l : List Nat) : Prop :=
  IsPartitionOf t l ∧ tailSize l ≤ r

/-- `p`-regular: no positive part occurs `p` or more times. -/
def PRegular (p : Nat) (l : List Nat) : Prop :=
  ∀ x, 0 < x → l.count x < p

/-- Remove `q` boxes from the first row. -/
def delFirst (q : Nat) : List Nat → List Nat
  | [] => []
  | a :: μ => (a - q) :: μ

/-- Add `q` boxes to the first row. -/
def addFirst (q : Nat) : List Nat → List Nat
  | [] => [q]
  | a :: μ => (a + q) :: μ

/-- The printed Definition 6.1.1(2) of Hone et al. v2 (non-strict at the
boundary `2λ₁ = N + q`). -/
def QStablePrinted (q N : Nat) (l : List Nat) : Prop :=
  IsPartitionOf N l ∧ tailSize l < q ∧ (N < 3 * q → N + q ≤ 2 * firstRow l)

/-- The strict version used by the repair. -/
def QStableStrict (q N : Nat) (l : List Nat) : Prop :=
  IsPartitionOf N l ∧ tailSize l < q ∧ N + q < 2 * firstRow l

/-- Dominance order on lists (partial sums); sizes are compared separately. -/
def Dominates (l l' : List Nat) : Prop :=
  ∀ k, (l'.take k).sum ≤ (l.take k).sum

/-! ### Small list lemmas -/

theorem mem_le_sum {μ : List Nat} {x : Nat} (hx : x ∈ μ) : x ≤ μ.sum := by
  induction μ with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp hx with h | h
    · omega
    · have := ih h; omega

theorem count_eq_zero_of_forall_lt {μ : List Nat} {x : Nat}
    (h : ∀ y ∈ μ, y < x) : μ.count x = 0 := by
  apply List.count_eq_zero.mpr
  intro hx
  exact Nat.lt_irrefl _ (h x hx)

theorem count_cons_nat (a x : Nat) (μ : List Nat) :
    (a :: μ).count x = μ.count x + (if a = x then 1 else 0) := by
  rw [List.count_cons]
  by_cases h : a = x
  · simp [h]
  · simp [h]

/-! ### The shape of a bounded-tail partition -/

/-- A bounded-tail partition of a size exceeding `2r` is `a :: μ` with
`a + μ.sum = t`, `μ.sum ≤ r`, and hence `a > μ.sum`. -/
theorem boundedTail_shape {t r : Nat} {l : List Nat} (ht : 2 * r < t)
    (h : BoundedTail t r l) :
    ∃ a μ, l = a :: μ ∧ a + μ.sum = t ∧ μ.sum ≤ r ∧ μ.sum < a := by
  obtain ⟨⟨_, hsum⟩, htail⟩ := h
  cases l with
  | nil => simp at hsum; omega
  | cons a μ =>
    refine ⟨a, μ, rfl, ?_, ?_, ?_⟩
    · simpa [List.sum_cons] using hsum
    · simpa [tailSize] using htail
    · have h1 : a + μ.sum = t := by simpa [List.sum_cons] using hsum
      have h2 : μ.sum ≤ r := by simpa [tailSize] using htail
      omega

/-- Prompt 02, item 2 (first half): in the strict range the first row is
strictly larger than its entire tail, hence than every other part. -/
theorem firstRow_gt_tailSize {t r : Nat} {l : List Nat} (ht : 2 * r < t)
    (h : BoundedTail t r l) : tailSize l < firstRow l := by
  obtain ⟨a, μ, rfl, _, _, h3⟩ := boundedTail_shape ht h
  simpa [tailSize, firstRow] using h3

theorem firstRow_gt_parts {t r : Nat} {a : Nat} {μ : List Nat} (ht : 2 * r < t)
    (h : BoundedTail t r (a :: μ)) : ∀ x ∈ μ, x < a := by
  intro x hx
  have h1 := firstRow_gt_tailSize ht h
  have h2 := mem_le_sum hx
  simp [tailSize, firstRow] at h1
  omega

/-! ### Deletion and addition are mutually inverse on bounded-tail labels -/

theorem isPartition_cons {a : Nat} {μ : List Nat} :
    IsPartition (a :: μ) ↔ (∀ x ∈ μ, x ≤ a) ∧ 0 < a ∧ IsPartition μ := by
  unfold IsPartition
  rw [List.pairwise_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h3 a (List.mem_cons_self), h2, fun x hx => h3 x (List.mem_cons_of_mem _ hx)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h3⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h2
    · exact h4 x hx

/-- Prompt 02, item 1 (deletion lands in the target set, is sorted, keeps the tail). -/
theorem delFirst_boundedTail {q r n : Nat} (hn : 2 * r < n)
    {l : List Nat} (h : BoundedTail (n + q) r l) :
    BoundedTail n r (delFirst q l) ∧ tailSize (delFirst q l) = tailSize l ∧
      addFirst q (delFirst q l) = l := by
  obtain ⟨a, μ, rfl, h1, h2, _⟩ := boundedTail_shape (t := n + q) (by omega) h
  obtain ⟨⟨hp, _⟩, _⟩ := h
  rw [isPartition_cons] at hp
  obtain ⟨_, _, hμ⟩ := hp
  have hparts : ∀ x ∈ μ, x ≤ a - q := by
    intro x hx
    have := mem_le_sum hx
    omega
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact isPartition_cons.mpr ⟨hparts, by omega, hμ⟩
  · simp only [delFirst, List.sum_cons]; omega
  · simpa [delFirst, tailSize] using h2
  · simp [delFirst, tailSize]
  · simp only [delFirst, addFirst]
    congr 1
    omega

/-- Prompt 02, item 1 (addition lands in the source set and inverts deletion). -/
theorem addFirst_boundedTail {q r n : Nat} (hn : 2 * r < n)
    {l : List Nat} (h : BoundedTail n r l) :
    BoundedTail (n + q) r (addFirst q l) ∧ tailSize (addFirst q l) = tailSize l ∧
      delFirst q (addFirst q l) = l := by
  obtain ⟨a, μ, rfl, h1, h2, _⟩ := boundedTail_shape hn h
  obtain ⟨⟨hp, _⟩, _⟩ := h
  rw [isPartition_cons] at hp
  obtain ⟨hle, hpos, hμ⟩ := hp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact isPartition_cons.mpr ⟨fun x hx => Nat.le_trans (hle x hx) (Nat.le_add_right _ _),
      by omega, hμ⟩
  · simp only [addFirst, List.sum_cons]; omega
  · simpa [addFirst, tailSize] using h2
  · simp [addFirst, tailSize]
  · simp [delFirst, addFirst]

/-- Deletion is injective on the source label set. -/
theorem delFirst_injOn {q r n : Nat} (hn : 2 * r < n)
    {l l' : List Nat} (h : BoundedTail (n + q) r l) (h' : BoundedTail (n + q) r l')
    (e : delFirst q l = delFirst q l') : l = l' := by
  rw [← (delFirst_boundedTail hn h).2.2, ← (delFirst_boundedTail hn h').2.2, e]

/-- Deletion is surjective onto the target label set. -/
theorem delFirst_surjOn {q r n : Nat} (hn : 2 * r < n)
    {m : List Nat} (h : BoundedTail n r m) :
    ∃ l, BoundedTail (n + q) r l ∧ delFirst q l = m :=
  ⟨addFirst q m, (addFirst_boundedTail hn h).1, (addFirst_boundedTail hn h).2.2⟩

/-- Prompt 02, item 1 (strict stability): every bounded-tail label of `N = n+q`
lies strictly inside the printed stable range. -/
theorem boundedTail_strictStable {q r n : Nat} (hq : r < q) (hn : 2 * r < n)
    {l : List Nat} (h : BoundedTail (n + q) r l) : QStableStrict q (n + q) l := by
  obtain ⟨a, μ, rfl, h1, h2, _⟩ := boundedTail_shape (t := n + q) (by omega) h
  refine ⟨h.1, ?_, ?_⟩
  · simp only [tailSize]; omega
  · simp only [firstRow]; omega

theorem QStableStrict.printed {q N : Nat} {l : List Nat} (h : QStableStrict q N l) :
    QStablePrinted q N l :=
  ⟨h.1, h.2.1, fun _ => Nat.le_of_lt h.2.2⟩

/-! ### p-regularity is preserved in the strict range -/

/-- If the first part of `a :: μ` and of `a' :: μ` both exceed every part of `μ`,
then the two lists have the same `p`-regularity (for `p ≥ 2`).  This is the
"unique largest part" argument; it does not use congruences of sizes. -/
theorem pRegular_cons_iff_of_gt {p a a' : Nat} {μ : List Nat} (hp : 2 ≤ p)
    (ha : ∀ x ∈ μ, x < a) (ha' : ∀ x ∈ μ, x < a') :
    PRegular p (a :: μ) ↔ PRegular p (a' :: μ) := by
  have key : ∀ b : Nat, (∀ x ∈ μ, x < b) →
      (PRegular p (b :: μ) ↔ PRegular p μ) := by
    intro b hb
    constructor
    · intro h x hx
      have := h x hx
      rw [count_cons_nat] at this
      omega
    · intro h x hx
      rw [count_cons_nat]
      by_cases hbx : b = x
      · subst hbx
        rw [count_eq_zero_of_forall_lt hb]
        simp; omega
      · simp [hbx]; exact h x hx
  rw [key a ha, key a' ha']

/-- Prompt 02, item 2: first-row deletion preserves and reflects `p`-regularity on
bounded-tail labels whenever `n > 2r`.  The empty tail is covered.  (The hypothesis
`q > r` is not needed for this partition-level statement; it enters through stability,
`boundedTail_strictStable`, and through the fixed-support argument of the manuscript.) -/
theorem pRegular_delFirst_iff {p q r n : Nat} (hp : 2 ≤ p) (hn : 2 * r < n)
    {l : List Nat} (h : BoundedTail (n + q) r l) :
    PRegular p l ↔ PRegular p (delFirst q l) := by
  obtain ⟨a, μ, rfl, h1, h2, _⟩ := boundedTail_shape (t := n + q) (by omega) h
  simp only [delFirst]
  apply pRegular_cons_iff_of_gt hp
  · intro x hx; have := mem_le_sum hx; omega
  · intro x hx; have := mem_le_sum hx; omega

/-! ### Dominance is preserved and reflected -/

theorem take_sum_cons_sub {q a : Nat} (hqa : q ≤ a) (μ : List Nat) (k : Nat) :
    (((a - q) :: μ).take (k + 1)).sum + q = ((a :: μ).take (k + 1)).sum := by
  simp only [List.take_succ_cons, List.sum_cons]
  omega

/-- Prompt 02, item 3: for two labels whose first rows are at least `q`, dominance
before deletion is equivalent to dominance after deletion: every nonempty initial
partial sum drops by exactly `q`. -/
theorem dominates_delFirst_iff {q a a' : Nat} {μ μ' : List Nat}
    (ha : q ≤ a) (ha' : q ≤ a') :
    Dominates (a :: μ) (a' :: μ') ↔
      Dominates (delFirst q (a :: μ)) (delFirst q (a' :: μ')) := by
  simp only [delFirst]
  constructor
  · intro h k
    cases k with
    | zero => simp
    | succ k =>
      have h1 := take_sum_cons_sub ha μ k
      have h2 := take_sum_cons_sub ha' μ' k
      have := h (k + 1)
      omega
  · intro h k
    cases k with
    | zero => simp
    | succ k =>
      have h1 := take_sum_cons_sub ha μ k
      have h2 := take_sum_cons_sub ha' μ' k
      have := h (k + 1)
      omega

/-- Dominance version on the actual label sets. -/
theorem dominates_delFirst_iff_boundedTail {q r n : Nat} (hn : 2 * r < n)
    {l l' : List Nat} (h : BoundedTail (n + q) r l) (h' : BoundedTail (n + q) r l') :
    Dominates l l' ↔ Dominates (delFirst q l) (delFirst q l') := by
  obtain ⟨a, μ, rfl, h1, h2, _⟩ := boundedTail_shape (t := n + q) (by omega) h
  obtain ⟨a', μ', rfl, h1', h2', _⟩ := boundedTail_shape (t := n + q) (by omega) h'
  exact dominates_delFirst_iff (by omega) (by omega)

/-- The reversed order (the highest-weight order when labels are recorded through the
fixed bijection `λ ↦ λᵗ` and the order is *defined* as reversed dominance of `λ`)
is preserved as well.  The separate classical fact that transposition reverses
dominance is *not* proved here; see `DEPENDENCIES.md`. -/
theorem reversed_dominates_delFirst_iff {q r n : Nat} (hn : 2 * r < n)
    {l l' : List Nat} (h : BoundedTail (n + q) r l) (h' : BoundedTail (n + q) r l') :
    Dominates l' l ↔ Dominates (delFirst q l') (delFirst q l) :=
  dominates_delFirst_iff_boundedTail hn h' h

/-! ### The non-strict boundary: exact classification of the failure -/

/-- Shape lemma in the printed (non-strict) range, for target rank `n ≥ 1`. -/
theorem printed_shape {q n : Nat} (hn : 1 ≤ n) {l : List Nat}
    (h : QStablePrinted q (n + q) l) :
    ∃ a μ, l = a :: μ ∧ a + μ.sum = n + q ∧ μ.sum < q ∧ μ.sum + q ≤ a := by
  obtain ⟨⟨_, hsum⟩, htail, hb⟩ := h
  cases l with
  | nil => simp at hsum; omega
  | cons a μ =>
    have h1 : a + μ.sum = n + q := by simpa [List.sum_cons] using hsum
    have h2 : μ.sum < q := by simpa [tailSize] using htail
    refine ⟨a, μ, rfl, h1, h2, ?_⟩
    by_cases h3 : n + q < 3 * q
    · have := hb h3
      simp only [firstRow] at this
      omega
    · omega

/-- In the printed range the deleted shape is still a partition (for `n ≥ 1`). -/
theorem delFirst_isPartitionOf_printed {q n : Nat} (hn : 1 ≤ n) {l : List Nat}
    (h : QStablePrinted q (n + q) l) : IsPartitionOf n (delFirst q l) := by
  obtain ⟨a, μ, rfl, h1, h2, h3⟩ := printed_shape hn h
  obtain ⟨⟨hp, _⟩, _, _⟩ := h
  rw [isPartition_cons] at hp
  obtain ⟨_, _, hμ⟩ := hp
  refine ⟨isPartition_cons.mpr ⟨?_, by omega, hμ⟩, ?_⟩
  · intro x hx; have := mem_le_sum hx; omega
  · simp only [delFirst, List.sum_cons]; omega

/-- A list of positive numbers one of whose members equals the whole sum is a singleton. -/
theorem eq_singleton_of_mem_eq_sum {μ : List Nat} (hpos : ∀ x ∈ μ, 0 < x)
    {x : Nat} (hx : x ∈ μ) (hsum : x = μ.sum) : μ = [x] := by
  induction μ with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.sum_cons] at hsum
    rcases List.mem_cons.mp hx with rfl | h
    · have hys : ys.sum = 0 := by omega
      cases ys with
      | nil => rfl
      | cons z zs =>
        have hz := hpos z (by simp)
        rw [List.sum_cons] at hys
        omega
    · have h1 := mem_le_sum h
      have h2 := hpos y (by simp)
      omega

/-- **Exact classification of the boundary defect.**  In the *printed* stable range
(target rank `n ≥ 1`, `p ≥ 2`), deletion of `q` from the first row preserves and
reflects `p`-regularity *unless* `p = 2` and the label is the two-row boundary shape
`(b+q, b)`.  -/
theorem pRegular_delFirst_iff_printed {p q n : Nat} (hp : 2 ≤ p) (hn : 1 ≤ n)
    {l : List Nat} (h : QStablePrinted q (n + q) l)
    (hexc : ¬ (p = 2 ∧ ∃ b, l = [b + q, b])) :
    PRegular p l ↔ PRegular p (delFirst q l) := by
  obtain ⟨a, μ, rfl, h1, h2, h3⟩ := printed_shape hn h
  obtain ⟨⟨hpart, _⟩, _, _⟩ := h
  rw [isPartition_cons] at hpart
  obtain ⟨_, _, hμ⟩ := hpart
  simp only [delFirst]
  by_cases hstrict : ∀ x ∈ μ, x < a - q
  · apply pRegular_cons_iff_of_gt hp
    · intro x hx; have := hstrict x hx; omega
    · exact hstrict
  · -- some tail part equals `a - q`, forcing `μ = [a - q]`
    have hex : ∃ x, x ∈ μ ∧ ¬ x < a - q := by
      apply Classical.byContradiction
      intro hne
      apply hstrict
      intro x hx
      apply Classical.byContradiction
      intro hx'
      exact hne ⟨x, hx, hx'⟩
    obtain ⟨x, hx, hxa⟩ := hex
    have hxs := mem_le_sum hx
    have hxe : x = μ.sum := by omega
    have hsing : μ = [x] := eq_singleton_of_mem_eq_sum hμ.2 hx hxe
    have hax : a - q = x := by omega
    subst hsing
    have hp2 : p ≠ 2 := by
      intro hp2
      apply hexc
      refine ⟨hp2, x, ?_⟩
      have : a = x + q := by omega
      rw [this]
    -- both `[a, x]` and `[x, x]` are `p`-regular when `p ≥ 3`
    constructor
    · intro _ y _
      rw [hax]
      rw [count_cons_nat, count_cons_nat]
      simp only [List.count_nil]
      split <;> omega
    · intro _ y _
      rw [count_cons_nat, count_cons_nat]
      simp only [List.count_nil]
      split <;> split <;> omega

/-- The exceptional family really is exceptional: for `p = 2`, `1 ≤ b < q`, the label
`(b+q, b)` satisfies the printed stability conditions for `N = 2b + q`, is 2-regular,
and its deleted shape `(b, b)` is 2-singular. -/
theorem boundary_family {q b : Nat} (hb : 1 ≤ b) (hbq : b < q) :
    QStablePrinted q (2 * b + q) [b + q, b] ∧
      2 * firstRow [b + q, b] = (2 * b + q) + q ∧
      PRegular 2 [b + q, b] ∧ ¬ PRegular 2 (delFirst q [b + q, b]) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [isPartition_cons]
    refine ⟨?_, by omega, ?_⟩
    · intro x hx; simp at hx; omega
    · rw [isPartition_cons]
      exact ⟨(by intro x hx; cases hx), (by omega), ⟨List.Pairwise.nil, (by intro x hx; cases hx)⟩⟩
  · simp; omega
  · simp [tailSize]; omega
  · intro _; simp [firstRow]; omega
  · simp [firstRow]; omega
  · intro y _
    rw [count_cons_nat, count_cons_nat]
    simp only [List.count_nil]
    split <;> split <;> omega
  · intro h
    have := h b (by omega)
    simp [delFirst] at this

/-- The boundary family never meets the strict hypotheses: if `(b+q, b)` had tail at most
`r`, then its target rank `2b` would not exceed `2r`. -/
theorem boundary_family_not_strict {q b r : Nat}
    (h : BoundedTail (2 * b + q) r [b + q, b]) : ¬ 2 * r < 2 * b := by
  have : tailSize [b + q, b] ≤ r := h.2
  simp [tailSize] at this
  omega

/-! ### The concrete boundary example of the audit: q = 2, N = 4, n = 2 -/

/-- `(3,1)` satisfies the printed stability conditions for `q = 2`, `N = 4`, with
equality `2λ₁ = N + q`; it is 2-regular; its deleted shape is `(1,1)`, a 2-singular
partition of the target rank `2 = 4 - 2`. -/
theorem example_31 :
    QStablePrinted 2 4 [3, 1] ∧ 2 * firstRow [3, 1] = 4 + 2 ∧
      delFirst 2 [3, 1] = [1, 1] ∧ IsPartitionOf 2 [1, 1] ∧
      PRegular 2 [3, 1] ∧ ¬ PRegular 2 [1, 1] ∧ ¬ QStableStrict 2 4 [3, 1] := by
  have h := boundary_family (q := 2) (b := 1) (by omega) (by omega)
  refine ⟨h.1, h.2.1, rfl, ?_, h.2.2.1, h.2.2.2, ?_⟩
  · exact delFirst_isPartitionOf_printed (q := 2) (n := 2) (by omega) h.1
  · intro hs
    have := hs.2.2
    simp [firstRow] at this

/-- No admissible `r` exists for the boundary example: `q = 2 > r ≥ 1` forces `r = 1`,
and then `n = 2 > 2r` fails. -/
theorem example_31_outside_strict_range : ¬ ∃ r, 1 ≤ r ∧ r < 2 ∧ 2 * r < 2 := by
  rintro ⟨r, h1, h2, h3⟩
  omega

/-! ### The onset used by the manuscript -/

/-- With `r = k d + s` the rank condition `n > 2r` is literally `n ≥ 2(kd+s)+1`:
no extra factor or hidden rank requirement. -/
theorem onset_iff (k d s n : Nat) : 2 * (k * d + s) < n ↔ 2 * (k * d + s) + 1 ≤ n := by
  omega

end DegreeProfilesReview.StablePartitions
