/-
Claude, 27 Sep 2026.  Undecidability, part B2: the switch, direction (i).

If the run of `M` never halts before time `n`, the standard structure on `Fin n` is a model of
`θ_M`: the order is `<`, `o = 0`, `e = n - 1`, `S(j) = min(j+1, n-1)`, `C_r(j)` is the value of
counter `r` at time `j` (at most `j`, so it fits), and `Q_ℓ(j)` holds iff the normalized state at
time `j` is `ℓ`.  In particular a non-halting machine gives models of every size `n ≥ 1`
(manuscript `lem:switch` (i), including `n = 1`).
-/
import UCounter

set_option autoImplicit false

namespace ClaudeUndec

section Std
variable (P : Prog) (n : ℕ) (hn : 0 < n)

/-- The standard structure of the run on `Fin n`. -/
def stdStr : Str (Fin n) where
  rel R l := if R = 0 then l.headD ⟨0, hn⟩ < l.tail.headD ⟨0, hn⟩
    else P.norm (P.cfg (l.headD ⟨0, hn⟩).val).1 = R - 1
  fn f l := if f = 0 then ⟨0, hn⟩ else if f = 1 then ⟨n - 1, by omega⟩
    else if f = 2 then ⟨min ((l.headD ⟨0, hn⟩).val + 1) (n - 1), by omega⟩
    else ⟨(P.cfg (l.headD ⟨0, hn⟩).val).2 (f - 3),
      lt_of_le_of_lt (P.cfg_le _ _) (l.headD ⟨0, hn⟩).2⟩

variable {P n hn}

theorem std_lt (a b : Fin n) : (stdStr P n hn).rel 0 [a, b] ↔ a < b := by
  simp [stdStr]
theorem std_q (ℓ : ℕ) (a : Fin n) :
    (stdStr P n hn).rel (1 + ℓ) [a] ↔ P.norm (P.cfg a.val).1 = ℓ := by
  simp [stdStr]
theorem std_o : ((stdStr P n hn).fn 0 []).val = 0 := by simp [stdStr]
theorem std_e : ((stdStr P n hn).fn 1 []).val = n - 1 := by simp [stdStr]
theorem std_S (a : Fin n) : ((stdStr P n hn).fn 2 [a]).val = min (a.val + 1) (n - 1) := by
  simp [stdStr]
theorem std_C (r : ℕ) (a : Fin n) :
    ((stdStr P n hn).fn (3 + r) [a]).val = (P.cfg a.val).2 r := by
  simp [stdStr, show 3 + r ≠ 1 by omega, show 3 + r ≠ 2 by omega]

end Std

/-! ### Facts about runs -/

namespace Prog
variable (P : Prog)

theorem norm_le (ℓ : ℕ) : P.norm ℓ ≤ P.length := min_le_right _ _

theorem state_of_norm {ℓ s : ℕ} (hs : P.norm s = ℓ) (hℓ : ℓ < P.length) : s = ℓ := by
  unfold norm at hs; omega

theorem halt_of_norm {ℓ s : ℕ} (hs : P.norm s = ℓ) (hh : P.IsHaltSt ℓ) : P.IsHaltSt s := by
  unfold norm at hs
  rcases hh with h | h
  · left; omega
  · by_cases hsl : s < P.length
    · right; have : s = ℓ := by omega
      subst this; exact h
    · left; omega

theorem step_inc {c : ℕ × (ℕ → ℕ)} {r ℓ' : ℕ} (h : P[c.1]? = some (Sum.inl (r, ℓ'))) :
    P.step c = (ℓ', Function.update c.2 r (c.2 r + 1)) := by
  unfold step; rw [h]

theorem step_dec_zero {c : ℕ × (ℕ → ℕ)} {r ℓ₀ ℓ₁ : ℕ}
    (h : P[c.1]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) (hz : c.2 r = 0) :
    P.step c = (ℓ₀, c.2) := by
  unfold step; rw [h]; simp [hz]

theorem step_dec_pos {c : ℕ × (ℕ → ℕ)} {r ℓ₀ ℓ₁ : ℕ}
    (h : P[c.1]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) (hz : c.2 r ≠ 0) :
    P.step c = (ℓ₁, Function.update c.2 r (c.2 r - 1)) := by
  unfold step; rw [h]; simp [hz]

theorem instrCnt_lt {ℓ : ℕ} {i : Instr} (h : P[ℓ]? = some i) : instrCnt i < P.ncnt := by
  unfold ncnt
  have hm : instrCnt i ∈ P.map instrCnt :=
    List.mem_map.mpr ⟨i, List.mem_of_getElem? h, rfl⟩
  have := le_foldr_max _ _ hm
  omega

end Prog

/-! ### Direction (i) -/

section Model
variable (P : Prog) {n : ℕ} (hn : 0 < n) (σ : ℕ → Fin n)

/-- The premise `t ≠ e ∧ Q_ℓ(t) ∧ v = S(t)` of a transition, in the standard structure. -/
theorem std_pre (ℓ : ℕ) (hℓ : ℓ ≤ P.length) (rest : Clause) :
    clauseHolds (theta P) (stdStr P n hn) σ (pre ℓ ++ rest) ↔
      ((σ 1).val ≠ n - 1 ∨ (σ 0).val = (σ 1).val ∨ P.norm (P.cfg (σ 0).val).1 ≠ ℓ ∨
        (σ 2).val ≠ min ((σ 0).val + 1) (n - 1)) ∨
      clauseHolds (theta P) (stdStr P n hn) σ rest := by
  simp only [pre, List.cons_append, clauseHolds_cons, litHolds_pos, litHolds_neg, holds_isE,
    holds_eq, holds_qA P (h := hℓ), holds_sOf, std_q, Fin.ext_iff, std_e, std_S, List.nil_append]
  tauto

theorem base_ok (hnh : ∀ j < n, ¬ P.IsHaltSt (P.cfg j).1) {c : Clause}
    (hc : c ∈ baseClauses P) : clauseHolds (theta P) (stdStr P n hn) σ c := by
  simp only [baseClauses, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_filter, List.mem_range, List.not_mem_nil, or_false] at hc
  rcases hc with (((h | h | h | h | h | h | h | h | h | h) | ⟨a, ha, b, hb, h⟩) |
    ⟨r, hr, rfl⟩) | ⟨ℓ, ⟨hℓ, hh⟩, rfl⟩
  all_goals first
    | (subst h
       simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, litHolds_neg, holds_ltA,
         holds_isO, holds_isE, holds_sOf, holds_eq, std_lt, Fin.ext_iff, Fin.lt_def, std_o,
         std_e, std_S, or_false]
       omega)
    | skip
  · -- some state holds
    subst h
    refine ⟨pos (qA (P.norm (P.cfg (σ 0).val).1) 0),
      List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.lt_succ_of_le (P.norm_le _)), rfl⟩, ?_⟩
    rw [litHolds_pos, holds_qA P (h := P.norm_le _), std_q]
  · -- initial state
    subst h
    simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, litHolds_neg, holds_isO,
      holds_qA P (h := Nat.zero_le _), std_q, Fin.ext_iff, std_o, or_false]
    by_cases h1 : (σ 1).val = 0
    · right; rw [h1]; simp [Prog.cfg_zero, Prog.norm]
    · left; exact h1
  · -- at most one state
    split_ifs at h with hab
    · cases h
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_neg,
        holds_qA P (h := Nat.le_of_lt_succ ha), holds_qA P (h := Nat.le_of_lt_succ hb), std_q, or_false]
      omega
  · -- initial counters
    simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, litHolds_neg, holds_isO,
      holds_cOf P (hr := hr), holds_eq, Fin.ext_iff, std_o, std_C, or_false]
    by_cases h1 : (σ 1).val = 0
    · have : (P.cfg (σ 1).val).2 r = 0 := by rw [h1]; rfl
      omega
    · left; exact h1
  · -- the halting states never occur
    simp only [clauseHolds_cons, clauseHolds_nil, litHolds_neg,
      holds_qA P (h := Nat.le_of_lt_succ hℓ), std_q, or_false]
    intro hq
    exact hnh _ (σ 0).2 (P.halt_of_norm hq (of_decide_eq_true hh))

/-! #### Transitions -/

theorem next_inc {j ℓ r ℓ' : ℕ} (hst : (P.cfg j).1 = ℓ) (hi : P[ℓ]? = some (Sum.inl (r, ℓ'))) :
    (P.cfg (j + 1)).1 = ℓ' ∧ (P.cfg (j + 1)).2 r = (P.cfg j).2 r + 1 ∧
      ∀ r', r' ≠ r → (P.cfg (j + 1)).2 r' = (P.cfg j).2 r' := by
  rw [Prog.cfg_succ, P.step_inc (by rw [hst]; exact hi)]
  refine ⟨rfl, by simp, fun r' h => by simp [Function.update_of_ne h]⟩

theorem next_dec_zero {j ℓ r ℓ₀ ℓ₁ : ℕ} (hst : (P.cfg j).1 = ℓ)
    (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) (hz : (P.cfg j).2 r = 0) :
    (P.cfg (j + 1)).1 = ℓ₀ ∧ ∀ r', (P.cfg (j + 1)).2 r' = (P.cfg j).2 r' := by
  rw [Prog.cfg_succ, P.step_dec_zero (by rw [hst]; exact hi) hz]
  exact ⟨rfl, fun _ => rfl⟩

theorem next_dec_pos {j ℓ r ℓ₀ ℓ₁ : ℕ} (hst : (P.cfg j).1 = ℓ)
    (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) (hz : (P.cfg j).2 r ≠ 0) :
    (P.cfg (j + 1)).1 = ℓ₁ ∧ (P.cfg (j + 1)).2 r = (P.cfg j).2 r - 1 ∧
      ∀ r', r' ≠ r → (P.cfg (j + 1)).2 r' = (P.cfg j).2 r' := by
  rw [Prog.cfg_succ, P.step_dec_pos (by rw [hst]; exact hi) hz]
  refine ⟨rfl, by simp, fun r' h => by simp [Function.update_of_ne h]⟩

theorem trans_ok {ℓ : ℕ} (hℓ : ℓ < P.length) {i : Instr} (hi : P[ℓ]? = some i) {c : Clause}
    (hc : c ∈ transClauses P ℓ i) : clauseHolds (theta P) (stdStr P n hn) σ c := by
  have hcnt := P.instrCnt_lt hi
  have hT0 := (σ 0).2
  have hC : ∀ r, (P.cfg (σ 0).val).2 r ≤ (σ 0).val := fun r => P.cfg_le _ r
  have key : ∀ rest : Clause, (∀ (_ : (σ 1).val = n - 1) (_ : (σ 0).val < n - 1)
      (_ : (σ 2).val = (σ 0).val + 1) (_ : (P.cfg (σ 0).val).1 = ℓ),
      clauseHolds (theta P) (stdStr P n hn) σ rest) →
      clauseHolds (theta P) (stdStr P n hn) σ (pre ℓ ++ rest) := by
    intro rest h
    rw [std_pre P hn σ ℓ hℓ.le]
    by_cases hpre : (σ 1).val ≠ n - 1 ∨ (σ 0).val = (σ 1).val ∨
        P.norm (P.cfg (σ 0).val).1 ≠ ℓ ∨ (σ 2).val ≠ min ((σ 0).val + 1) (n - 1)
    · exact Or.inl hpre
    · push_neg at hpre
      obtain ⟨h1, h2, h3, h4⟩ := hpre
      exact Or.inr (h h1 (by omega) (by omega) (P.state_of_norm h3 hℓ))
  rcases i with ⟨r, ℓ'⟩ | ⟨r, ℓ₀, ℓ₁⟩ | u
  · simp only [Prog.instrCnt] at hcnt
    simp only [transClauses, sameClauses, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
    rcases hc with (rfl | rfl | rfl) | ⟨r', ⟨hr', hne⟩, rfl⟩
    · apply key; intro h1 hT hV hst
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_neg, holds_cOf P (hr := hcnt),
        holds_eq, Fin.ext_iff, std_C, or_false]
      have := hC r; omega
    · apply key; intro h1 hT hV hst
      obtain ⟨-, hn2, -⟩ := next_inc P hst hi
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_neg, litHolds_pos,
        holds_cOf P (hr := hcnt), holds_sOf, Fin.ext_iff, std_C, std_S, hV, or_false]
      have := hC r; omega
    · apply key; intro h1 hT hV hst
      obtain ⟨hn1, -, -⟩ := next_inc P hst hi
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos,
        holds_qA P (h := P.norm_le ℓ'), std_q, hV, hn1, or_false]
    · rw [List.append_nil]
      apply key; intro h1 hT hV hst
      obtain ⟨-, -, hn3⟩ := next_inc P hst hi
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_neg, litHolds_pos,
        holds_cOf P (hr := hr'), Fin.ext_iff, std_C, hV, hn3 r' hne, or_false]
      omega
  · simp only [Prog.instrCnt] at hcnt
    simp only [transClauses, sameClauses, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
    -- the branch premise `p = o ∧ c = C_r(t) ∧ (c = p or c ≠ p)`
    have zkey : ∀ rest : Clause, (∀ (_ : (σ 1).val = n - 1) (_ : (σ 0).val < n - 1)
        (_ : (σ 2).val = (σ 0).val + 1) (_ : (P.cfg (σ 0).val).1 = ℓ) (_ : (σ 5).val = 0)
        (_ : (σ 3).val = (P.cfg (σ 0).val).2 r) (_ : (P.cfg (σ 0).val).2 r = 0),
        clauseHolds (theta P) (stdStr P n hn) σ rest) →
        clauseHolds (theta P) (stdStr P n hn) σ
          (pre ℓ ++ ([neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5)] ++ rest)) := by
      intro rest h
      apply key
      intro h1 hT hV hst
      simp only [List.cons_append, List.nil_append, clauseHolds_cons, litHolds_neg, holds_isO,
        holds_cOf P (hr := hcnt), holds_eq, Fin.ext_iff, std_o, std_C]
      by_cases hp : (σ 5).val = 0
      · by_cases hc3 : (σ 3).val = (P.cfg (σ 0).val).2 r
        · by_cases h35 : (σ 3).val = (σ 5).val
          · exact Or.inr (Or.inr (Or.inr (h h1 hT hV hst hp hc3 (by omega))))
          · exact Or.inr (Or.inr (Or.inl h35))
        · exact Or.inr (Or.inl hc3)
      · exact Or.inl hp
    have pkey : ∀ rest : Clause, (∀ (_ : (σ 1).val = n - 1) (_ : (σ 0).val < n - 1)
        (_ : (σ 2).val = (σ 0).val + 1) (_ : (P.cfg (σ 0).val).1 = ℓ) (_ : (σ 5).val = 0)
        (_ : (σ 3).val = (P.cfg (σ 0).val).2 r) (_ : (P.cfg (σ 0).val).2 r ≠ 0),
        clauseHolds (theta P) (stdStr P n hn) σ rest) →
        clauseHolds (theta P) (stdStr P n hn) σ
          (pre ℓ ++ ([neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5)] ++ rest)) := by
      intro rest h
      apply key
      intro h1 hT hV hst
      simp only [List.cons_append, List.nil_append, clauseHolds_cons, litHolds_neg, litHolds_pos,
        holds_isO, holds_cOf P (hr := hcnt), holds_eq, Fin.ext_iff, std_o, std_C]
      by_cases hp : (σ 5).val = 0
      · by_cases hc3 : (σ 3).val = (P.cfg (σ 0).val).2 r
        · by_cases h35 : (σ 3).val = (σ 5).val
          · exact Or.inr (Or.inr (Or.inl h35))
          · exact Or.inr (Or.inr (Or.inr (h h1 hT hV hst hp hc3 (by omega))))
        · exact Or.inr (Or.inl hc3)
      · exact Or.inl hp
    rcases hc with ((rfl | rfl | rfl | rfl | rfl) | ⟨r', ⟨hr', hne⟩, rfl⟩) |
      ⟨r', ⟨hr', hne⟩, rfl⟩
    · have e : pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5), pos (cOf r 3 2)] =
          pre ℓ ++ ([neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5)] ++ [pos (cOf r 3 2)]) := rfl
      rw [e]; apply zkey; intro h1 hT hV hst hp hc3 hz
      obtain ⟨-, hn2⟩ := next_dec_zero P hst hi hz
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, holds_cOf P (hr := hcnt),
        Fin.ext_iff, std_C, hV, hn2, or_false]
      exact hc3
    · have e : pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5), pos (qA (P.norm ℓ₀) 2)] =
          pre ℓ ++ ([neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5)] ++
            [pos (qA (P.norm ℓ₀) 2)]) := rfl
      rw [e]; apply zkey; intro h1 hT hV hst hp hc3 hz
      obtain ⟨hn1, -⟩ := next_dec_zero P hst hi hz
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos,
        holds_qA P (h := P.norm_le ℓ₀), std_q, hV, hn1, or_false]
    · have e : pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5), neg (cOf r 6 2),
          pos (ltA 6 3)] = pre ℓ ++ ([neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5)] ++
            [neg (cOf r 6 2), pos (ltA 6 3)]) := rfl
      rw [e]; apply pkey; intro h1 hT hV hst hp hc3 hz
      obtain ⟨-, hn2, -⟩ := next_dec_pos P hst hi hz
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, litHolds_neg,
        holds_cOf P (hr := hcnt), holds_ltA, std_lt, Fin.ext_iff, Fin.lt_def, std_C, hV, hn2,
        or_false]
      omega
    · have e : pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5), neg (cOf r 6 2),
          neg (sOf 4 6), pos (Atom.eq 4 3)] = pre ℓ ++ ([neg (isO 5), neg (cOf r 3 0),
            pos (Atom.eq 3 5)] ++ [neg (cOf r 6 2), neg (sOf 4 6), pos (Atom.eq 4 3)]) := rfl
      rw [e]; apply pkey; intro h1 hT hV hst hp hc3 hz
      obtain ⟨-, hn2, -⟩ := next_dec_pos P hst hi hz
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, litHolds_neg,
        holds_cOf P (hr := hcnt), holds_sOf, holds_eq, Fin.ext_iff, std_C, std_S, hV, hn2,
        or_false]
      have := hC r; omega
    · have e : pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5), pos (qA (P.norm ℓ₁) 2)] =
          pre ℓ ++ ([neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5)] ++
            [pos (qA (P.norm ℓ₁) 2)]) := rfl
      rw [e]; apply pkey; intro h1 hT hV hst hp hc3 hz
      obtain ⟨hn1, -, -⟩ := next_dec_pos P hst hi hz
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos,
        holds_qA P (h := P.norm_le ℓ₁), std_q, hV, hn1, or_false]
    · rw [List.append_assoc]; apply zkey; intro h1 hT hV hst hp hc3 hz
      obtain ⟨-, hn2⟩ := next_dec_zero P hst hi hz
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, litHolds_neg,
        holds_cOf P (hr := hr'), Fin.ext_iff, std_C, hV, hn2 r', or_false]
      omega
    · rw [List.append_assoc]; apply pkey; intro h1 hT hV hst hp hc3 hz
      obtain ⟨-, -, hn3⟩ := next_dec_pos P hst hi hz
      simp only [clauseHolds_cons, clauseHolds_nil, litHolds_pos, litHolds_neg,
        holds_cOf P (hr := hr'), Fin.ext_iff, std_C, hV, hn3 r' hne, or_false]
      omega
  · simp [transClauses] at hc

/-- The standard structure is a model of `θ_M` if the run does not halt before time `n`. -/
theorem theta_std_model (hnh : ∀ j < n, ¬ P.IsHaltSt (P.cfg j).1) :
    IsModel (theta P) (stdStr P n hn) := by
  intro c hc σ
  simp only [theta, Sentence.clauses, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with hb | ⟨ℓ, hℓ, hcl⟩
  · exact base_ok P hn σ hnh hb
  · rcases h : P[ℓ]? with _ | i
    · rw [h] at hcl; simp at hcl
    · rw [h] at hcl; exact trans_ok P hn σ hℓ h hcl

end Model

/-! ### `θ_M` is well formed -/

section WF
variable (P : Prog)

theorem wf_ltA (i j : ℕ) : AtomWF (theta P) (ltA i j) := by
  refine ⟨?_, ?_⟩
  · show 0 < (thRels P).length; rw [thRels_length]; omega
  · rfl
theorem wf_qA {ℓ : ℕ} (h : ℓ ≤ P.length) (i : ℕ) : AtomWF (theta P) (qA ℓ i) := by
  refine ⟨?_, ?_⟩
  · show 1 + ℓ < (thRels P).length; rw [thRels_length]; omega
  · show 1 = (thRels P).getD (1 + ℓ) 0; rw [thRels_getD_q P h]
theorem wf_isO (u : ℕ) : AtomWF (theta P) (isO u) :=
  ⟨by show 0 < (thFuns P).length; rw [thFuns_length]; omega, rfl⟩
theorem wf_isE (u : ℕ) : AtomWF (theta P) (isE u) :=
  ⟨by show 1 < (thFuns P).length; rw [thFuns_length]; omega, rfl⟩
theorem wf_sOf (v t : ℕ) : AtomWF (theta P) (sOf v t) :=
  ⟨by show 2 < (thFuns P).length; rw [thFuns_length]; omega, rfl⟩
theorem wf_cOf {r : ℕ} (h : r < P.ncnt) (c t : ℕ) : AtomWF (theta P) (cOf r c t) := by
  refine ⟨?_, ?_⟩
  · show 3 + r < (thFuns P).length; rw [thFuns_length]; omega
  · show 1 = (thFuns P).getD (3 + r) 0; rw [thFuns_getD_C P h]
theorem wf_eq (i j : ℕ) : AtomWF (theta P) (Atom.eq i j) := trivial

theorem wf_pre {ℓ : ℕ} (h : ℓ ≤ P.length) : ∀ l ∈ pre ℓ, AtomWF (theta P) l.2 := by
  intro l hl
  simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  exacts [wf_isE P 1, wf_eq P 0 1, wf_qA P h 0, wf_sOf P 2 0]

/-- `θ_M` is well formed. -/
theorem theta_WF : WF (theta P) := by
  intro c hc
  simp only [theta, Sentence.clauses, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with hb | ⟨ℓ, hℓ, hcl⟩
  · simp only [baseClauses, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
      List.mem_filterMap, List.mem_filter, List.mem_range, List.not_mem_nil, or_false] at hb
    rcases hb with (((h | h | h | h | h | h | h | h | h | h) | ⟨a, ha, b, hb, h⟩) |
      ⟨r, hr, rfl⟩) | ⟨ℓ, ⟨hℓ, -⟩, rfl⟩
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact wf_ltA P _ _
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_ltA P _ _, wf_ltA P _ _, wf_ltA P _ _⟩
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_ltA P _ _, wf_eq P _ _, wf_ltA P _ _⟩
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_isO P _, wf_eq P _ _, wf_ltA P _ _⟩
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_isE P _, wf_eq P _ _, wf_ltA P _ _⟩
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_isE P _, wf_sOf P _ _, wf_eq P _ _⟩
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_isE P _, wf_eq P _ _, wf_sOf P _ _, wf_ltA P _ _⟩
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_isE P _, wf_eq P _ _, wf_sOf P _ _, wf_ltA P _ _, wf_ltA P _ _⟩
    · subst h
      intro l hl
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hl
      exact wf_qA P (Nat.le_of_lt_succ (List.mem_range.mp hℓ)) 0
    · subst h; simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_isO P _, wf_qA P (Nat.zero_le _) _⟩
    · by_cases hab : a < b
      · rw [if_pos hab] at h
        cases h
        simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        exact ⟨wf_qA P (Nat.le_of_lt_succ ha) 0, wf_qA P (Nat.le_of_lt_succ hb) 0⟩
      · rw [if_neg hab] at h; cases h
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact ⟨wf_isO P _, wf_cOf P hr _ _, wf_eq P _ _⟩
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      exact wf_qA P (Nat.le_of_lt_succ hℓ) 0
  · rcases h : P[ℓ]? with _ | i
    · rw [h] at hcl; simp at hcl
    · rw [h] at hcl
      have hcnt := P.instrCnt_lt h
      have hpre := wf_pre P hℓ.le
      rcases i with ⟨r, ℓ'⟩ | ⟨r, ℓ₀, ℓ₁⟩ | u
      · simp only [Prog.instrCnt] at hcnt
        simp only [transClauses, sameClauses, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hcl
        rcases hcl with (rfl | rfl | rfl) | ⟨r', ⟨hr', -⟩, rfl⟩ <;>
        simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        · exact ⟨hpre, wf_cOf P hcnt _ _, wf_eq P _ _⟩
        · exact ⟨hpre, wf_cOf P hcnt _ _, wf_sOf P _ _, wf_cOf P hcnt _ _⟩
        · exact ⟨hpre, wf_qA P (P.norm_le _) _⟩
        · exact ⟨hpre, wf_cOf P hr' _ _, wf_cOf P hr' _ _⟩
      · simp only [Prog.instrCnt] at hcnt
        simp only [transClauses, sameClauses, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hcl
        rcases hcl with ((rfl | rfl | rfl | rfl | rfl) | ⟨r', ⟨hr', -⟩, rfl⟩) |
          ⟨r', ⟨hr', -⟩, rfl⟩ <;>
        simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        · exact ⟨hpre, wf_isO P _, wf_cOf P hcnt _ _, wf_eq P _ _, wf_cOf P hcnt _ _⟩
        · exact ⟨hpre, wf_isO P _, wf_cOf P hcnt _ _, wf_eq P _ _, wf_qA P (P.norm_le _) _⟩
        · exact ⟨hpre, wf_isO P _, wf_cOf P hcnt _ _, wf_eq P _ _, wf_cOf P hcnt _ _,
            wf_ltA P _ _⟩
        · exact ⟨hpre, wf_isO P _, wf_cOf P hcnt _ _, wf_eq P _ _, wf_cOf P hcnt _ _,
            wf_sOf P _ _, wf_eq P _ _⟩
        · exact ⟨hpre, wf_isO P _, wf_cOf P hcnt _ _, wf_eq P _ _, wf_qA P (P.norm_le _) _⟩
        · exact ⟨⟨hpre, wf_isO P _, wf_cOf P hcnt _ _, wf_eq P _ _⟩, wf_cOf P hr' _ _,
            wf_cOf P hr' _ _⟩
        · exact ⟨⟨hpre, wf_isO P _, wf_cOf P hcnt _ _, wf_eq P _ _⟩, wf_cOf P hr' _ _,
            wf_cOf P hr' _ _⟩
      · simp [transClauses] at hcl

end WF

/-- **The switch, direction (i)** (manuscript `lem:switch` (i)): if the run of `M` from zero
never halts, `θ_M` has a model of every finite size `n ≥ 1`. -/
theorem switch_i (P : Prog) (hP : ¬ P.Halts) {n : ℕ} (hn : 0 < n) : HasModelOfSize (theta P) n :=
  ⟨stdStr P n hn, theta_std_model P hn (fun j _ h => hP ⟨j, h⟩)⟩

end ClaudeUndec
