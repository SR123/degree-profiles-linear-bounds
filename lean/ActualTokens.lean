import BranchDecrease

namespace SelfContainedCycle039

open SelfContainedCycle034 SelfContainedCycle035 SelfContainedCycle036
open SelfContainedCycle037 SelfContainedCycle038

def tokenEdges {r : ℕ} (s : State r) : Edges :=
  Finset.univ.biUnion (fun k => (s k).toFinset)

@[simp] theorem mem_tokenEdges {r : ℕ} (s : State r) (e : ℕ × ℕ) :
    e ∈ tokenEdges s ↔ ∃ k, s k = some e := by
  simp [tokenEdges, Option.mem_toFinset]

def UniqueTokens {r : ℕ} (s : State r) : Prop :=
  ∀ k l e, s k = some e → s l = some e → k = l

def Represents {r : ℕ} (s : State r) (R : Edges) : Prop := tokenEdges s = R ∧ UniqueTokens s

def KeyInjective (key : (ℕ × ℕ) → ℕ) (R : Edges) : Prop :=
  ∀ e ∈ R, ∀ e' ∈ R, key e = key e' → e = e'

theorem matching_row_key {R : Edges} (h : IsMatching R) : KeyInjective Prod.fst R :=
  fun e he e' he' hkey => h e he e' he' (Or.inl hkey)

theorem matching_column_key {R : Edges} (h : IsMatching R) : KeyInjective Prod.snd R :=
  fun e he e' he' hkey => h e he e' he' (Or.inr hkey)

/-- Actual lookup in the target matching; uniqueness is proved from matching below. -/
noncomputable def lookup (key : (ℕ × ℕ) → ℕ) (Q : Edges) (j : ℕ) : Option (ℕ × ℕ) := by
  classical
  exact if h : ∃ e ∈ Q, key e = j then some (Classical.choose h) else none

theorem lookup_some_iff (key : (ℕ × ℕ) → ℕ) (Q : Edges) (j : ℕ)
    (hinj : KeyInjective key Q) (x : ℕ × ℕ) :
    lookup key Q j = some x ↔ x ∈ Q ∧ key x = j := by
  classical
  unfold lookup
  split_ifs with h
  · have hs := Classical.choose_spec h
    simp only [Option.some.injEq]
    constructor
    · intro heq
      simpa only [heq] using hs
    · intro hx
      exact hinj _ hs.1 x hx.1 (hs.2.trans hx.2.symm)
  · constructor
    · intro heq
      cases heq
    · intro hx
      exact (h ⟨x, hx⟩).elim

/-- Preserve a token's chosen coordinate, deleting it if the target has no such edge. -/
noncomputable def transport {r : ℕ} (key : (ℕ × ℕ) → ℕ) (Q : Edges) (s : State r) : State r :=
  fun k => (s k).bind (fun e => lookup key Q (key e))

theorem transport_some_iff {r : ℕ} (key : (ℕ × ℕ) → ℕ) (Q : Edges) (s : State r)
    (hinj : KeyInjective key Q) (k : Fin r) (x : ℕ × ℕ) :
    transport key Q s k = some x ↔ ∃ e, s k = some e ∧ x ∈ Q ∧ key x = key e := by
  cases hs : s k with
  | none => simp [transport, hs]
  | some e => simp [transport, hs, lookup_some_iff key Q (key e) hinj]

/-- Transport represents exactly the target matching, with no duplicate present token. -/
theorem transport_represents {r : ℕ} (key : (ℕ × ℕ) → ℕ) (R Q : Edges) (s : State r)
    (hrep : Represents s R) (hR : KeyInjective key R) (hQ : KeyInjective key Q)
    (hkeys : Q.image key ⊆ R.image key) : Represents (transport key Q s) Q := by
  have source_mem : ∀ k e, s k = some e → e ∈ R := by
    intro k e hs
    rw [← hrep.1]
    exact (mem_tokenEdges s e).mpr ⟨k, hs⟩
  constructor
  · ext x
    rw [mem_tokenEdges]
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨e, _, hx, _⟩ := (transport_some_iff key Q s hQ k x).mp hk
      exact hx
    · intro hx
      obtain ⟨e, he, hekey⟩ := Finset.mem_image.mp (hkeys (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      have he' : e ∈ tokenEdges s := hrep.1.symm ▸ he
      obtain ⟨k, hk⟩ := (mem_tokenEdges s e).mp he'
      exact ⟨k, (transport_some_iff key Q s hQ k x).mpr ⟨e, hk, hx, hekey.symm⟩⟩
  · intro k l x hk hl
    obtain ⟨e, hke, _, hkey⟩ := (transport_some_iff key Q s hQ k x).mp hk
    obtain ⟨e', hle, _, hkey'⟩ := (transport_some_iff key Q s hQ l x).mp hl
    have hee' := hR e (source_mem k e hke) e' (source_mem l e' hle) (hkey.symm.trans hkey')
    exact hrep.2 k l e hke (hee'.symm ▸ hle)

/-- Lookup by row gives exactly the concrete column-token rule, including deletions. -/
theorem transport_columnStep {r : ℕ} (Q : Edges) (s : State r) (hm : IsMatching Q) :
    ColumnStep s (transport Prod.fst Q s) := by
  intro k
  cases hs : s k with
  | none => simp [transport, hs]
  | some e =>
    cases ht : transport Prod.fst Q s k with
    | none => exact Or.inl rfl
    | some x =>
      obtain ⟨e', he', _, hx⟩ := (transport_some_iff Prod.fst Q s (matching_row_key hm) k x).mp ht
      have heq : e = e' := Option.some.inj (hs.symm.trans he')
      subst e'
      exact Or.inr ⟨x.2, congrArg some (Prod.ext hx rfl)⟩


/-- Rows beyond the old prefix are retained verbatim, so the concrete row-token rule applies. -/
theorem transport_rowStep {r n : ℕ} (R Q : Edges) (s : State r)
    (hrep : Represents s R) (hm : IsMatching Q)
    (hkeep : ∀ e ∈ R, n < e.1 → e ∈ Q) : RowStep n s (transport Prod.snd Q s) := by
  intro k
  cases hs : s k with
  | none => simp [transport, hs]
  | some e =>
    by_cases hold : e.1 ≤ n
    · right
      refine ⟨hold, ?_⟩
      cases ht : transport Prod.snd Q s k with
      | none => exact Or.inl rfl
      | some x =>
        obtain ⟨e', he', _, hx⟩ :=
          (transport_some_iff Prod.snd Q s (matching_column_key hm) k x).mp ht
        have heq : e = e' := Option.some.inj (hs.symm.trans he')
        subst e'
        exact Or.inr ⟨x.1, congrArg some (Prod.ext rfl hx)⟩
    · left
      have heR : e ∈ R := by rw [← hrep.1]; exact (mem_tokenEdges s e).mpr ⟨k, hs⟩
      have heQ := hkeep e heR (by omega)
      exact (transport_some_iff Prod.snd Q s (matching_column_key hm) k e).mpr ⟨e, hs, heQ, rfl⟩

/-- The actual row branch retains its context and only uses source columns. -/
theorem branch_column_subset {R C Q : Edges} {B T : Finset ℕ} {z : ℤ}
    (hCR : C ⊆ R) (hb : Branch (R \ C) C B T Q z) : cols Q ⊆ cols R := by
  obtain ⟨M, hm, _, rfl⟩ := hb
  intro j hj
  obtain ⟨e, he, hej⟩ := Finset.mem_image.mp hj
  rcases Finset.mem_union.mp he with heP | heM
  · exact Finset.mem_image.mpr ⟨e, (Finset.mem_sdiff.mp heP).1, hej⟩
  · have hjC := replacement_cols_subset hm (Finset.mem_image.mpr ⟨e, heM, hej⟩)
    obtain ⟨e', he', he'j⟩ := Finset.mem_image.mp hjC
    exact Finset.mem_image.mpr ⟨e', hCR he', he'j⟩

theorem branch_keeps_context {R C Q : Edges} {B T : Finset ℕ} {z : ℤ}
    (hb : Branch (R \ C) C B T Q z) : R \ C ⊆ Q := by
  obtain ⟨M, _, _, rfl⟩ := hb
  exact Finset.subset_union_left

theorem branch_matching {P C Q : Edges} {B T : Finset ℕ} {z : ℤ}
    (hb : Branch P C B T Q z) : IsMatching Q := by
  obtain ⟨M, _, hm, rfl⟩ := hb
  exact hm

/-- Every actual row reduction admits the concrete, exact token transport. -/
theorem rowReduction_tokens {r n d N : ℕ} {R Q : Edges} (s : State r)
    (hrep : Represents s R) (hm : IsMatching R) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (hred : RowReduction N R Q) :
    Represents (transport Prod.snd Q s) Q ∧ RowStep n s (transport Prod.snd Q s) := by
  obtain ⟨a, C, z, hf, hC, hb⟩ := hred
  have hsub := ((mem_chains _ _).mp (Finset.mem_filter.mp hC).1).1
  have hCR : C ⊆ R := hsub.trans (Finset.filter_subset _ _)
  have ha := rowFails_old hf.1 hd hn
  have hmQ := branch_matching hb
  have hkeep : ∀ e ∈ R, n < e.1 → e ∈ Q := by
    intro e he hnew
    have heC : e ∉ C := by
      intro heC
      have hea := (Finset.mem_filter.mp (hsub heC)).2
      omega
    exact branch_keeps_context hb (Finset.mem_sdiff.mpr ⟨he, heC⟩)
  exact ⟨transport_represents Prod.snd R Q s hrep (matching_column_key hm)
    (matching_column_key hmQ) (branch_column_subset hCR hb), transport_rowStep R Q s hrep hmQ hkeep⟩


theorem rowReduction_column_subset {N : ℕ} {R Q : Edges} (h : RowReduction N R Q) : cols Q ⊆ cols R := by
  obtain ⟨a, C, z, _, hC, hb⟩ := h
  have hsub := ((mem_chains _ _).mp (Finset.mem_filter.mp hC).1).1
  exact branch_column_subset (hsub.trans (Finset.filter_subset _ _)) hb

theorem rowReduction_matching {N : ℕ} {R Q : Edges} (h : RowReduction N R Q) : IsMatching Q := by
  obtain ⟨a, C, z, _, _, hb⟩ := h
  exact branch_matching hb

@[simp] theorem cols_transpose (R : Edges) : cols (transpose R) = rows R := by
  have h := rows_transpose (transpose R)
  simpa only [transpose_transpose] using h.symm

/-- Column transport preserves row labels and exactly represents the actual column child. -/
theorem columnReduction_tokens {r K : ℕ} {R Q : Edges} (s : State r)
    (hrep : Represents s R) (hm : IsMatching R)
    (hred : RowReduction K (transpose R) (transpose Q)) :
    Represents (transport Prod.fst Q s) Q ∧ ColumnStep s (transport Prod.fst Q s) := by
  have hmQ := (matching_transpose Q).mp (rowReduction_matching hred)
  have hkeys := rowReduction_column_subset hred
  simp only [cols_transpose] at hkeys
  exact ⟨transport_represents Prod.fst R Q s hrep (matching_row_key hm) (matching_row_key hmQ) hkeys,
    transport_columnStep Q s hmQ⟩

/-- A fully defined update selected by the actual orientation; absent tokens cannot return. -/
noncomputable def nextTokens {r : ℕ} (R Q : Edges) (s : State r) : State r :=
  match chosenRewrite R with
  | .row _ _ => transport Prod.snd Q s
  | .column _ _ => transport Prod.fst Q s
  | .terminal => s

/-- The former abstract token premise is discharged for every actual selected signed branch. -/
theorem chosenBranch_tokens {r n d N K : ℕ} {R Q : Edges} {z : ℤ} (s : State r)
    (hrep : Represents s R) (hm : IsMatching R) (hd : R.card ≤ d) (hn : 2*d ≤ n)
    (hb : ChosenBranch N K R Q z) :
    Represents (nextTokens R Q s) Q ∧ Step n s (nextTokens R Q s) := by
  unfold ChosenBranch chosenRewrite at hb
  unfold nextTokens chosenRewrite
  split_ifs at hb ⊢ with hr hc
  · have h := rowReduction_tokens s hrep hm hd hn
      (show RowReduction N R Q from ⟨_, _, z, min_row_failure_is_first R hr, (chosenLongest_spec _).1, hb⟩)
    exact ⟨h.1, Or.inl h.2⟩
  · have hred : RowReduction K (transpose R) (transpose Q) := by
      let a := (columnFailures R).min' hc
      refine ⟨a, chosenLongest (rowPrefix (transpose R) a), z, ?_, (chosenLongest_spec _).1, ?_⟩
      · exact (firstColumnAt_iff R a).mp (min_column_failure_is_first R hc)
      · simpa only [ColumnBranch, chosenColumnChain, transpose_transpose, transpose_sdiff] using hb
    have h := columnReduction_tokens s hrep hm hred
    exact ⟨h.1, Or.inr h.2⟩
  · exact hb.elim


theorem tokenEdges_card_le {r : ℕ} (s : State r) : (tokenEdges s).card ≤ r := by
  calc
    (tokenEdges s).card ≤ ∑ k : Fin r, ((s k).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _k : Fin r, 1 := by
      apply Finset.sum_le_sum
      intro k _
      cases s k <;> simp
    _ = r := by simp

theorem represented_card_le {r : ℕ} {s : State r} {R : Edges} (h : Represents s R) : R.card ≤ r := by
  rw [← h.1]
  exact tokenEdges_card_le s

/-- An actual matching starts with precisely one token for each edge. -/
noncomputable def initialTokens (R : Edges) : State R.card :=
  fun k => some ((R.equivFin.symm k).val)

theorem initialTokens_represents (R : Edges) : Represents (initialTokens R) R := by
  constructor
  · ext e
    rw [mem_tokenEdges]
    constructor
    · rintro ⟨k, hk⟩
      have heq := Option.some.inj hk
      exact heq ▸ (R.equivFin.symm k).property
    · intro he
      refine ⟨R.equivFin ⟨e, he⟩, ?_⟩
      simp [initialTokens]
  · intro k l e hk hl
    apply R.equivFin.symm.injective
    apply Subtype.ext
    exact (Option.some.inj hk).trans (Option.some.inj hl).symm

theorem chosenBranch_matching {N K : ℕ} {R Q : Edges} {z : ℤ}
    (h : ChosenBranch N K R Q z) : IsMatching Q := by
  rcases chosenBranch_is_reduction h with hr | hc
  · exact rowReduction_matching hr
  · exact (matching_transpose Q).mp (rowReduction_matching hc)

/-- The lifted state is constructed recursively, not supplied as a simulation premise. -/
noncomputable def tokenRun {r : ℕ} (path : ℕ → Edges) (s₀ : State r) : ℕ → State r
  | 0 => s₀
  | t+1 => nextTokens (path t) (path (t+1)) (tokenRun path s₀ t)

theorem tokenRun_correct {r n d N K T : ℕ} (path : ℕ → Edges) (s₀ : State r)
    (hrep : Represents s₀ (path 0)) (hm : IsMatching (path 0))
    (hr : r ≤ d) (hn : 2*d ≤ n)
    (steps : ∀ t < T, ∃ z, ChosenBranch N K (path t) (path (t+1)) z) :
    ∀ t ≤ T, Represents (tokenRun path s₀ t) (path t) ∧ IsMatching (path t) := by
  intro t
  induction t with
  | zero => intro _; exact ⟨hrep, hm⟩
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    obtain ⟨z, hz⟩ := steps t (by omega)
    have hd := (represented_card_le hprev.1).trans hr
    have hnext := chosenBranch_tokens (tokenRun path s₀ t) hprev.1 hprev.2 hd hn hz
    exact ⟨hnext.1, chosenBranch_matching hz⟩

theorem tokenRun_steps {r n d N K T : ℕ} (path : ℕ → Edges) (s₀ : State r)
    (hrep : Represents s₀ (path 0)) (hm : IsMatching (path 0))
    (hr : r ≤ d) (hn : 2*d ≤ n)
    (steps : ∀ t < T, ∃ z, ChosenBranch N K (path t) (path (t+1)) z) :
    ∀ t < T, Step n (tokenRun path s₀ t) (tokenRun path s₀ (t+1)) := by
  intro t ht
  have hvalid := tokenRun_correct path s₀ hrep hm hr hn steps t (by omega)
  obtain ⟨z, hz⟩ := steps t ht
  exact (chosenBranch_tokens (tokenRun path s₀ t) hvalid.1 hvalid.2
    ((represented_card_le hvalid.1).trans hr) hn hz).2

/-- Degree control now follows along actual paths from the constructed token representation. -/
theorem actual_path_card_le_initial {n d N K T : ℕ} (path : ℕ → Edges)
    (hm : IsMatching (path 0)) (hd : (path 0).card ≤ d) (hn : 2*d ≤ n)
    (steps : ∀ t < T, ∃ z, ChosenBranch N K (path t) (path (t+1)) z) :
    ∀ t ≤ T, (path t).card ≤ (path 0).card := by
  intro t ht
  have hvalid := tokenRun_correct path (initialTokens (path 0)) (initialTokens_represents _) hm hd hn steps t ht
  exact represented_card_le hvalid.1


/-- All appended row labels present anywhere in the actual finite edge history. -/
def historyRows (n : ℕ) (path : ℕ → Edges) (T : ℕ) : Finset ℕ :=
  (Finset.range (T+1)).biUnion (fun t => (rows (path t)).filter (fun i => n < i))

theorem mem_historyRows (n : ℕ) (path : ℕ → Edges) (T i : ℕ) :
    i ∈ historyRows n path T ↔ ∃ t ≤ T, n < i ∧ ∃ j, (i,j) ∈ path t := by
  simp only [historyRows, Finset.mem_biUnion, Finset.mem_range, Nat.lt_succ_iff,
    Finset.mem_filter, rows, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, ⟨e, he, hei⟩, hi⟩
    exact ⟨t, ht, hi, e.2, by simpa only [← hei] using he⟩
  · rintro ⟨t, ht, hi, j, he⟩
    exact ⟨t, ht, ⟨(i,j), he, rfl⟩, hi⟩

/-- The history set is proved equal to the token history; it is not postulated. -/
theorem historyRows_eq_seen {r n T : ℕ} (path : ℕ → Edges) (run : ℕ → State r)
    (hrep : ∀ t ≤ T, Represents (run t) (path t)) : historyRows n path T = seen n run T := by
  ext i
  rw [mem_historyRows]
  simp only [seen, Finset.mem_biUnion, Finset.mem_univ, true_and, mem_seenBy]
  constructor
  · rintro ⟨t, ht, hi, j, hij⟩
    rw [← (hrep t ht).1] at hij
    obtain ⟨k, hk⟩ := (mem_tokenEdges (run t) (i,j)).mp hij
    exact ⟨k, t, ht, hi, j, hk⟩
  · rintro ⟨k, t, ht, hi, j, hk⟩
    refine ⟨t, ht, hi, j, ?_⟩
    rw [← (hrep t ht).1]
    exact (mem_tokenEdges (run t) (i,j)).mpr ⟨k, hk⟩

/-- The actual selected rewrite path encounters at most its initial number of appended rows. -/
theorem actual_path_history_bound {n d N K T : ℕ} (path : ℕ → Edges)
    (hm : IsMatching (path 0)) (hd : (path 0).card ≤ d) (hn : 2*d ≤ n)
    (steps : ∀ t < T, ∃ z, ChosenBranch N K (path t) (path (t+1)) z) :
    (historyRows n path T).card ≤ (path 0).card := by
  let s₀ := initialTokens (path 0)
  have hrep : Represents s₀ (path 0) := initialTokens_represents _
  have hvalid := tokenRun_correct path s₀ hrep hm hd hn steps
  rw [historyRows_eq_seen path (tokenRun path s₀) (fun t ht => (hvalid t ht).1)]
  exact whole_history_bound (tokenRun path s₀) (tokenRun_steps path s₀ hrep hm hd hn steps)

/-- Initial marked appended labels remain in the history even if the final state deletes them. -/
theorem initial_mark_in_history {n T i j : ℕ} (path : ℕ → Edges)
    (hi : n < i) (he : (i,j) ∈ path 0) : i ∈ historyRows n path T :=
  (mem_historyRows n path T i).mpr ⟨0, Nat.zero_le _, hi, j, he⟩

theorem marked_actual_path_history_bound {n d N K T i j : ℕ} (path : ℕ → Edges)
    (hm : IsMatching (path 0)) (hd : (path 0).card ≤ d) (hn : 2*d ≤ n)
    (steps : ∀ t < T, ∃ z, ChosenBranch N K (path t) (path (t+1)) z)
    (hi : n < i) (he : (i,j) ∈ path 0) :
    i ∈ historyRows n path T ∧ 1 ≤ (historyRows n path T).card ∧
      (historyRows n path T).card ≤ (path 0).card := by
  have hmem := initial_mark_in_history (T := T) path hi he
  exact ⟨hmem, Finset.card_pos.mpr ⟨i, hmem⟩, actual_path_history_bound path hm hd hn steps⟩


/-- A real path introduces row3 above the old prefix2 and then deletes its only edge. -/
def deletionPath (t : ℕ) : Edges :=
  if t = 0 then {(1,1)} else if t = 1 then {(3,1)} else ∅

theorem chosen_appended_singleton : chosenRewrite {(3,1)} = .column 1 {(3,1)} := by
  have hr : rowFailures {(3,1)} = ∅ := by decide
  have hc : columnFailures {(3,1)} = {1} := by decide
  have hp : rowPrefix (transpose {(3,1)}) 1 = {(1,3)} := by decide
  have hm : chosenLongest {(1,3)} = {(1,3)} := by
    apply chosenLongest_unique
    · decide
    · intro D hD
      have hl : longestChains {(1,3)} = {{(1,3)}} := by decide
      rw [hl] at hD
      have hD' := Finset.mem_singleton.mp hD
      subst D
      exact le_refl _
  have hcc : chosenColumnChain {(3,1)} 1 = {(3,1)} := by
    rw [chosenColumnChain, hp, hm]
    decide
  unfold chosenRewrite
  simp only [hr, Finset.not_nonempty_empty, ↓reduceDIte, hc, Finset.singleton_nonempty,
    Finset.min'_singleton, hcc]

theorem deletionPath_actual_steps :
    ∀ t < 2, ∃ z, ChosenBranch 3 2 (deletionPath t) (deletionPath (t+1)) z := by
  intro t ht
  interval_cases t
  · refine ⟨-1, ?_⟩
    change ChosenBranch 3 2 {(1,1)} {(3,1)} (-1)
    rw [ChosenBranch, chosen_singleton_example]
    refine ⟨{(3,1)}, Or.inr ?_, ?_, ?_⟩ <;> decide
  · refine ⟨1, ?_⟩
    change ChosenBranch 3 2 {(3,1)} ∅ 1
    rw [ChosenBranch, chosen_appended_singleton]
    unfold ColumnBranch
    refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide

theorem deletionPath_actual_history : historyRows 2 deletionPath 2 = {3} := by decide

theorem deletionPath_final_empty : deletionPath 2 = ∅ := by decide

theorem deletionPath_bound_from_actual :
    (historyRows 2 deletionPath 2).card ≤ (deletionPath 0).card :=
  actual_path_history_bound deletionPath (by decide) (d := 1) (by decide) (by decide)
    deletionPath_actual_steps

/-- A marked initial appended row remains counted after the actual column step deletes it. -/
def markedDeletionPath (t : ℕ) : Edges := if t = 0 then {(3,1)} else ∅

theorem markedDeletionPath_actual_steps :
    ∀ t < 1, ∃ z, ChosenBranch 3 2 (markedDeletionPath t) (markedDeletionPath (t+1)) z := by
  intro t ht
  have ht0 : t = 0 := by omega
  subst t
  refine ⟨1, ?_⟩
  change ChosenBranch 3 2 {(3,1)} ∅ 1
  rw [ChosenBranch, chosen_appended_singleton]
  unfold ColumnBranch
  refine ⟨∅, Or.inl ?_, ?_, ?_⟩ <;> decide

theorem markedDeletionPath_bound_from_actual :
    3 ∈ historyRows 2 markedDeletionPath 1 ∧
      1 ≤ (historyRows 2 markedDeletionPath 1).card ∧
      (historyRows 2 markedDeletionPath 1).card ≤ (markedDeletionPath 0).card :=
  marked_actual_path_history_bound markedDeletionPath (by decide) (d := 1) (by decide) (by decide)
    markedDeletionPath_actual_steps (i := 3) (j := 1) (by decide) (by decide)

/-- Without the old-prefix size condition, an actual one-token history can use two appended labels. -/
theorem outside_old_prefix_counterexample :
    (historyRows 0 deletionPath 2).card = 2 ∧ (deletionPath 0).card = 1 := by decide

end SelfContainedCycle039
