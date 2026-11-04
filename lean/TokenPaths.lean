import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
Concrete edge updates and the whole-history appended-row bound from Cycle033.
Rows are positive natural labels, with old rows at most n. Tokens are Fin r.
An absent token cannot return. Row updates can replace/delete only old-row
tokens and retain columns. Column updates retain rows and may delete tokens.

These updates include every injection term of the written reduction, but this
file does NOT formalize the deterministic reduction tree, its locality, the
binomial grouping, normalization, or an NS/PC degree endpoint.
-/

namespace SelfContainedCycle034

abbrev State (r : ℕ) := Fin r → Option (ℕ × ℕ)

def RowStep {r : ℕ} (n : ℕ) (s t : State r) : Prop :=
  ∀ k, match s k with
  | none => t k = none
  | some e => t k = some e ∨
      (e.1 ≤ n ∧ (t k = none ∨ ∃ i, t k = some (i, e.2)))

def ColumnStep {r : ℕ} (s t : State r) : Prop :=
  ∀ k, match s k with
  | none => t k = none
  | some e => t k = none ∨ ∃ j, t k = some (e.1, j)

def Step {r : ℕ} (n : ℕ) (s t : State r) : Prop :=
  RowStep n s t ∨ ColumnStep s t

/-- An actual replacement term, retaining each selected token by its column. -/
def rowBranch {r : ℕ} (s : State r) (C : Finset (Fin r))
    (replacement : Fin r → Option ℕ) : State r := fun k =>
  if k ∈ C then (s k).bind (fun e => (replacement k).map (fun i => (i, e.2)))
  else s k

/-- The transposed replacement term, retaining each selected token by its row. -/
def columnBranch {r : ℕ} (s : State r) (C : Finset (Fin r))
    (replacement : Fin r → Option ℕ) : State r := fun k =>
  if k ∈ C then (s k).bind (fun e => (replacement k).map (fun j => (e.1, j)))
  else s k

theorem rowBranch_step {r n : ℕ} (s : State r) (C : Finset (Fin r))
    (replacement : Fin r → Option ℕ)
    (old : ∀ k ∈ C, ∀ i j, s k = some (i, j) → i ≤ n) :
    RowStep n s (rowBranch s C replacement) := by
  intro k
  cases hs : s k with
  | none => simp [rowBranch, hs]
  | some e =>
    rcases e with ⟨i, j⟩
    by_cases hk : k ∈ C
    · right
      refine ⟨old k hk i j hs, ?_⟩
      cases hr : replacement k with
      | none => exact Or.inl (by simp [rowBranch, hk, hs, hr])
      | some a => exact Or.inr ⟨a, by simp [rowBranch, hk, hs, hr]⟩
    · left
      simp [rowBranch, hk, hs]

theorem columnBranch_step {r : ℕ} (s : State r) (C : Finset (Fin r))
    (replacement : Fin r → Option ℕ) :
    ColumnStep s (columnBranch s C replacement) := by
  intro k
  cases hs : s k with
  | none => simp [columnBranch, hs]
  | some e =>
    rcases e with ⟨i, j⟩
    by_cases hk : k ∈ C
    · cases hr : replacement k with
      | none => exact Or.inl (by simp [columnBranch, hk, hs, hr])
      | some a => exact Or.inr ⟨a, by simp [columnBranch, hk, hs, hr]⟩
    · exact Or.inr ⟨j, by simp [columnBranch, hk, hs]⟩

/-- The numerical bound used for every failed prefix, with no asymptotic proviso. -/
theorem failed_prefix_lt_twice {a used chain degree : ℕ}
    (hu : used ≤ degree) (hc : chain ≤ degree)
    (hf : a - used < chain) : a < 2 * degree := by omega

theorem failed_prefix_old {a used chain degree d n : ℕ}
    (hu : used ≤ degree) (hc : chain ≤ degree)
    (hf : a - used < chain) (hd : degree ≤ d) (hn : 2 * d ≤ n) :
    a < n := by
  have h := failed_prefix_lt_twice hu hc hf
  omega

def prefixRows (R : Finset (ℕ × ℕ)) (a : ℕ) : Finset ℕ :=
  (R.filter (fun e => e.1 ≤ a)).image Prod.fst

/-- Cardinal hypotheses in the numerical lemma follow from the actual edge sets. -/
theorem edge_prefix_bound (R C : Finset (ℕ × ℕ)) (a : ℕ)
    (hC : C ⊆ R) (hf : a - (prefixRows R a).card < C.card) :
    a < 2 * R.card := by
  have hu : (prefixRows R a).card ≤ R.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le R _)
  exact failed_prefix_lt_twice hu (Finset.card_le_card hC) hf

theorem edge_prefix_old (R C : Finset (ℕ × ℕ)) {a d n : ℕ}
    (hC : C ⊆ R) (hf : a - (prefixRows R a).card < C.card)
    (hd : R.card ≤ d) (hn : 2 * d ≤ n) : a < n := by
  have h := edge_prefix_bound R C a hC hf
  omega

/-- A selected row chain inside a failed prefix really satisfies the old-row guard. -/
theorem rowBranch_step_of_failed_prefix {r n a used chain degree d : ℕ}
    (s : State r) (C : Finset (Fin r)) (replacement : Fin r → Option ℕ)
    (inside : ∀ k ∈ C, ∀ i j, s k = some (i, j) → i ≤ a)
    (hu : used ≤ degree) (hc : chain ≤ degree) (hf : a - used < chain)
    (hd : degree ≤ d) (hn : 2 * d ≤ n) :
    RowStep n s (rowBranch s C replacement) := by
  apply rowBranch_step
  intro k hk i j hs
  have h := failed_prefix_old hu hc hf hd hn
  have hi := inside k hk i j hs
  omega

def Frozen {r : ℕ} (s : State r) (k : Fin r) (i : ℕ) : Prop :=
  s k = none ∨ ∃ j, s k = some (i, j)

theorem step_absent {r n : ℕ} {s t : State r} (h : Step n s t)
    (k : Fin r) (hs : s k = none) : t k = none := by
  rcases h with h | h <;> simpa [RowStep, ColumnStep, hs] using h k

theorem step_frozen {r n i : ℕ} {s t : State r} (h : Step n s t)
    (k : Fin r) (hi : n < i) (hs : Frozen s k i) : Frozen t k i := by
  rcases hs with hs | ⟨j, hs⟩
  · exact Or.inl (step_absent h k hs)
  · rcases h with h | h
    · have hk := h k
      simp only [hs] at hk
      rcases hk with hk | ⟨hbad, _⟩
      · exact Or.inr ⟨j, hk⟩
      · omega
    · simpa only [Frozen, hs] using h k

/-- Persistence for a finite prefix of a run; steps after T are irrelevant. -/
theorem run_frozen {r n T a b i : ℕ} (run : ℕ → State r)
    (steps : ∀ t < T, Step n (run t) (run (t + 1)))
    (hab : a ≤ b) (hb : b ≤ T) (k : Fin r) (hi : n < i)
    (ha : Frozen (run a) k i) : Frozen (run b) k i := by
  induction b, hab using Nat.le_induction with
  | base => exact ha
  | succ b hab ih =>
    apply step_frozen (steps b (by omega)) k hi
    exact ih (by omega)

theorem same_appended_row {r n T a b i j c e : ℕ} (run : ℕ → State r)
    (steps : ∀ t < T, Step n (run t) (run (t + 1)))
    (ha : a ≤ T) (hb : b ≤ T) (k : Fin r)
    (hi : n < i) (hj : n < j)
    (hsa : run a k = some (i, c)) (hsb : run b k = some (j, e)) : i = j := by
  rcases le_total a b with hab | hba
  · have h := run_frozen run steps hab hb k hi (Or.inr ⟨c, hsa⟩)
    rcases h with h | ⟨z, h⟩ <;> simp_all
  · have h := run_frozen run steps hba ha k hj (Or.inr ⟨e, hsb⟩)
    rcases h with h | ⟨z, h⟩ <;> simp_all

def rowsAt {r : ℕ} (n : ℕ) (s : State r) (k : Fin r) : Finset ℕ :=
  match s k with
  | none => ∅
  | some e => if n < e.1 then {e.1} else ∅

theorem mem_rowsAt {r n i : ℕ} (s : State r) (k : Fin r) :
    i ∈ rowsAt n s k ↔ n < i ∧ ∃ j, s k = some (i, j) := by
  cases hs : s k with
  | none => simp [rowsAt, hs]
  | some e =>
    rcases e with ⟨a, b⟩
    by_cases h : n < a <;> simp [rowsAt, hs, h] <;> omega

def seenBy {r : ℕ} (n : ℕ) (run : ℕ → State r) (T : ℕ) (k : Fin r) : Finset ℕ :=
  (Finset.range (T + 1)).biUnion (fun t => rowsAt n (run t) k)

theorem mem_seenBy {r n T i : ℕ} (run : ℕ → State r) (k : Fin r) :
    i ∈ seenBy n run T k ↔ ∃ t ≤ T, n < i ∧ ∃ j, run t k = some (i, j) := by
  simp only [seenBy, Finset.mem_biUnion, Finset.mem_range, mem_rowsAt,
    Nat.lt_succ_iff]

theorem seenBy_card_le_one {r n T : ℕ} (run : ℕ → State r)
    (steps : ∀ t < T, Step n (run t) (run (t + 1))) (k : Fin r) :
    (seenBy n run T k).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨a, ha, hi, c, hsa⟩ := (mem_seenBy run k).mp hi
  obtain ⟨b, hb, hj, e, hsb⟩ := (mem_seenBy run k).mp hj
  exact same_appended_row run steps ha hb k hi hj hsa hsb

def seen {r : ℕ} (n : ℕ) (run : ℕ → State r) (T : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (seenBy n run T)

/-- All distinct appended labels ever encountered, even by subsequently deleted tokens. -/
theorem whole_history_bound {r n T : ℕ} (run : ℕ → State r)
    (steps : ∀ t < T, Step n (run t) (run (t + 1))) :
    (seen n run T).card ≤ r := by
  calc
    (seen n run T).card ≤ ∑ k : Fin r, (seenBy n run T k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k : Fin r, 1 := Finset.sum_le_sum (fun k _ => seenBy_card_le_one run steps k)
    _ = r := by simp

/-- Non-vacuity: two appended rows are encountered and then both tokens are deleted. -/
def deletionRun : ℕ → State 2 := fun t k =>
  if t = 0 then some (k.val + 1, k.val + 1)
  else if t = 1 then some (k.val + 5, k.val + 1)
  else none

theorem deletionRun_steps : ∀ t < 2, Step 4 (deletionRun t) (deletionRun (t + 1)) := by
  intro t ht
  interval_cases t
  · left
    intro k
    simp only [deletionRun, ↓reduceIte]
    right
    refine ⟨?_, Or.inr ⟨k.val + 5, rfl⟩⟩
    have hk := k.isLt
    omega
  · right
    intro k
    simp [deletionRun]

theorem deletionRun_history : seen 4 deletionRun 2 = {5, 6} := by decide

theorem deletionRun_final_empty : ∀ k, deletionRun 2 k = none := by
  intro k
  rfl

theorem deletionRun_bound_is_tight : (seen 4 deletionRun 2).card = 2 := by decide

end SelfContainedCycle034
