/-
Claude, 27 Sep 2026.  Undecidability, part D1: programming counter machines.

Counter machines are those of `UCounter` (increment, decrement with zero test, halt; all counters
start at `0`).  This file gives relocatable code blocks with proved behaviour:

* `ReachN P c c' t`: from configuration `c` the machine reaches `c'` in exactly `t` steps and no
  intermediate configuration is halting;
* `Emb P a code`: `code` occurs in `P` at address `a`;
* blocks `clearC`, `moveC`, `dupC`, `incC` and the counted loop `loopC`, each with a proved
  reachability lemma.

These are used in `UCompile` to compile every primitive recursive function (Mathlib's
`Nat.Primrec'`) into counter-machine code.
-/
import USwitch

set_option autoImplicit false

namespace ClaudeUndec

/-! ### Runs -/

section Runs
variable (P : Prog)

/-- Reaching `c'` from `c` in exactly `t` steps, with no halting configuration before. -/
def ReachN (c c' : ℕ × (ℕ → ℕ)) (t : ℕ) : Prop :=
  P.step^[t] c = c' ∧ ∀ j < t, ¬ P.IsHaltSt (P.step^[j] c).1

def Reach (c c' : ℕ × (ℕ → ℕ)) : Prop := ∃ t, ReachN P c c' t

variable {P}

theorem ReachN.refl (c : ℕ × (ℕ → ℕ)) : ReachN P c c 0 := ⟨rfl, fun _ h => absurd h (by omega)⟩

theorem ReachN.trans {c c' c'' : ℕ × (ℕ → ℕ)} {t t' : ℕ} (h : ReachN P c c' t)
    (h' : ReachN P c' c'' t') : ReachN P c c'' (t + t') := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [add_comm, Function.iterate_add_apply, h.1, h'.1]
  · -- careful with the order of iteration
    by_cases hjt : j < t
    · exact h.2 j hjt
    · have e : P.step^[j] c = P.step^[j - t] c' := by
        rw [← h.1, ← Function.iterate_add_apply]
        congr 1; omega
      rw [e]; exact h'.2 _ (by omega)

theorem Reach.trans {c c' c'' : ℕ × (ℕ → ℕ)} (h : Reach P c c') (h' : Reach P c' c'') :
    Reach P c c'' := by
  obtain ⟨t, ht⟩ := h; obtain ⟨t', ht'⟩ := h'; exact ⟨_, ht.trans ht'⟩

theorem Reach.refl (c : ℕ × (ℕ → ℕ)) : Reach P c c := ⟨0, ReachN.refl c⟩

/-- One step from a non-halting instruction. -/
theorem ReachN.step {c : ℕ × (ℕ → ℕ)} {i : Instr} (h : P[c.1]? = some i)
    (hi : i ≠ Sum.inr (Sum.inr ())) : ReachN P c (P.step c) 1 := by
  refine ⟨rfl, fun j hj => ?_⟩
  have : j = 0 := by omega
  subst this
  simp only [Function.iterate_zero, id] 
  rintro (hl | hl)
  · rw [List.getElem?_eq_none hl] at h; cases h
  · rw [h] at hl; exact hi (Option.some.inj hl)

theorem Reach.step {c : ℕ × (ℕ → ℕ)} {i : Instr} (h : P[c.1]? = some i)
    (hi : i ≠ Sum.inr (Sum.inr ())) : Reach P c (P.step c) := ⟨1, ReachN.step h hi⟩

/-- `ReachN` with a positive time. -/
theorem ReachN.step_trans {c c' : ℕ × (ℕ → ℕ)} {i : Instr} (h : P[c.1]? = some i)
    (hi : i ≠ Sum.inr (Sum.inr ())) {t : ℕ} (h' : ReachN P (P.step c) c' t) :
    ReachN P c c' (1 + t) := (ReachN.step h hi).trans h'

end Runs

/-! ### Embedded code -/

/-- `code` occurs in `P` at address `a`. -/
def Emb (P : Prog) (a : ℕ) (code : List Instr) : Prop :=
  ∀ i (h : i < code.length), P[a + i]? = some code[i]

theorem Emb.left {P : Prog} {a : ℕ} {c₁ c₂ : List Instr} (h : Emb P a (c₁ ++ c₂)) : Emb P a c₁ :=
  fun i hi => by
    have := h i (by simp; omega)
    rwa [List.getElem_append_left hi] at this

theorem Emb.right {P : Prog} {a : ℕ} {c₁ c₂ : List Instr} (h : Emb P a (c₁ ++ c₂)) :
    Emb P (a + c₁.length) c₂ := fun i hi => by
  have := h (c₁.length + i) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  rw [show a + c₁.length + i = a + (c₁.length + i) by omega]
  simpa using this

theorem Emb.get {P : Prog} {a : ℕ} {code : List Instr} (h : Emb P a code) {i : ℕ}
    (hi : i < code.length) : P[a + i]? = some code[i] := h i hi

/-! ### Instructions -/

abbrev incI (r ℓ : ℕ) : Instr := Sum.inl (r, ℓ)
abbrev decI (r ℓ₀ ℓ₁ : ℕ) : Instr := Sum.inr (Sum.inl (r, ℓ₀, ℓ₁))
abbrev haltI : Instr := Sum.inr (Sum.inr ())

theorem incI_ne (r ℓ : ℕ) : incI r ℓ ≠ haltI := by simp
theorem decI_ne (r ℓ₀ ℓ₁ : ℕ) : decI r ℓ₀ ℓ₁ ≠ haltI := by simp

section Blocks
variable {P : Prog}
open Function

theorem step_at_inc {a r ℓ : ℕ} (h : P[a]? = some (incI r ℓ)) (ρ : ℕ → ℕ) :
    P.step (a, ρ) = (ℓ, update ρ r (ρ r + 1)) := P.step_inc h

theorem step_at_dec_zero {a r ℓ₀ ℓ₁ : ℕ} (h : P[a]? = some (decI r ℓ₀ ℓ₁)) {ρ : ℕ → ℕ}
    (hz : ρ r = 0) : P.step (a, ρ) = (ℓ₀, ρ) := P.step_dec_zero h hz

theorem step_at_dec_pos {a r ℓ₀ ℓ₁ : ℕ} (h : P[a]? = some (decI r ℓ₀ ℓ₁)) {ρ : ℕ → ℕ}
    (hz : ρ r ≠ 0) : P.step (a, ρ) = (ℓ₁, update ρ r (ρ r - 1)) := P.step_dec_pos h hz

/-! #### Increment -/

def incC (r a : ℕ) : List Instr := [incI r (a + 1)]

theorem incC_run {a r : ℕ} (h : Emb P a (incC r a)) (ρ : ℕ → ℕ) :
    Reach P (a, ρ) (a + 1, update ρ r (ρ r + 1)) := by
  have h0 : P[a]? = some (incI r (a + 1)) := by simpa using h.get (i := 0) (by simp [incC])
  have := Reach.step (c := (a, ρ)) h0 (incI_ne _ _)
  rwa [step_at_inc h0] at this

/-! #### Clearing a register: `while r ≠ 0 do r--` -/

def clearC (r a : ℕ) : List Instr := [decI r (a + 1) a]

theorem clearC_run {a r : ℕ} (h : Emb P a (clearC r a)) :
    ∀ (v : ℕ) (ρ : ℕ → ℕ), ρ r = v → Reach P (a, ρ) (a + 1, update ρ r 0) := by
  have h0 : P[a]? = some (decI r (a + 1) a) := by simpa using h.get (i := 0) (by simp [clearC])
  intro v
  induction v with
  | zero =>
    intro ρ hρ
    have := Reach.step (c := (a, ρ)) h0 (decI_ne _ _ _)
    rw [step_at_dec_zero h0 hρ] at this
    rwa [show update ρ r 0 = ρ by rw [← hρ, update_eq_self]]
  | succ v ih =>
    intro ρ hρ
    have h1 := Reach.step (c := (a, ρ)) h0 (decI_ne _ _ _)
    rw [step_at_dec_pos h0 (by omega)] at h1
    have h2 := ih (update ρ r (ρ r - 1)) (by simp; omega)
    rw [update_idem] at h2
    exact h1.trans h2

theorem clearC_run' {a r : ℕ} (h : Emb P a (clearC r a)) (ρ : ℕ → ℕ) :
    Reach P (a, ρ) (a + 1, update ρ r 0) := clearC_run h _ ρ rfl

/-! #### Moving a register: `while s ≠ 0 do (s--, d++)` -/

def moveC (s d a : ℕ) : List Instr := [decI s (a + 2) (a + 1), incI d a]

theorem moveC_run {a s d : ℕ} (hsd : s ≠ d) (h : Emb P a (moveC s d a)) :
    ∀ (v : ℕ) (ρ : ℕ → ℕ), ρ s = v →
      Reach P (a, ρ) (a + 2, update (update ρ d (ρ d + ρ s)) s 0) := by
  have h0 : P[a]? = some (decI s (a + 2) (a + 1)) := by
    simpa using h.get (i := 0) (by simp [moveC])
  have h1 : P[a + 1]? = some (incI d a) := by simpa using h.get (i := 1) (by simp [moveC])
  intro v
  induction v with
  | zero =>
    intro ρ hρ
    have := Reach.step (c := (a, ρ)) h0 (decI_ne _ _ _)
    rw [step_at_dec_zero h0 hρ] at this
    convert this using 2
    funext x
    simp only [update_apply]
    split_ifs with h1 h2 <;> subst_vars <;> omega
  | succ v ih =>
    intro ρ hρ
    have r1 := Reach.step (c := (a, ρ)) h0 (decI_ne _ _ _)
    rw [step_at_dec_pos h0 (by omega)] at r1
    have r2 := Reach.step (c := (a + 1, update ρ s (ρ s - 1))) h1 (incI_ne _ _)
    rw [step_at_inc h1] at r2
    have r3 := ih (update (update ρ s (ρ s - 1)) d (update ρ s (ρ s - 1) d + 1))
      (by simp [hsd, Ne.symm hsd]; omega)
    refine (r1.trans (r2.trans r3)).trans ?_
    convert Reach.refl _ using 2
    funext x
    simp only [update_apply]
    split_ifs <;> subst_vars <;> omega

theorem moveC_run' {a s d : ℕ} (hsd : s ≠ d) (h : Emb P a (moveC s d a)) (ρ : ℕ → ℕ) :
    Reach P (a, ρ) (a + 2, update (update ρ d (ρ d + ρ s)) s 0) := moveC_run hsd h _ ρ rfl

/-! #### Duplicating a register: `while s ≠ 0 do (s--, d++, t++)` -/

def dupC (s d t a : ℕ) : List Instr := [decI s (a + 3) (a + 1), incI d (a + 2), incI t a]

theorem dupC_run {a s d t : ℕ} (hsd : s ≠ d) (hst : s ≠ t) (hdt : d ≠ t)
    (h : Emb P a (dupC s d t a)) :
    ∀ (v : ℕ) (ρ : ℕ → ℕ), ρ s = v →
      Reach P (a, ρ) (a + 3, update (update (update ρ d (ρ d + ρ s)) t (ρ t + ρ s)) s 0) := by
  have h0 : P[a]? = some (decI s (a + 3) (a + 1)) := by
    simpa using h.get (i := 0) (by simp [dupC])
  have h1 : P[a + 1]? = some (incI d (a + 2)) := by simpa using h.get (i := 1) (by simp [dupC])
  have h2 : P[a + 2]? = some (incI t a) := by simpa using h.get (i := 2) (by simp [dupC])
  intro v
  induction v with
  | zero =>
    intro ρ hρ
    have := Reach.step (c := (a, ρ)) h0 (decI_ne _ _ _)
    rw [step_at_dec_zero h0 hρ] at this
    convert this using 2
    funext x
    simp only [update_apply]
    split_ifs <;> subst_vars <;> omega
  | succ v ih =>
    intro ρ hρ
    have r1 := Reach.step (c := (a, ρ)) h0 (decI_ne _ _ _)
    rw [step_at_dec_pos h0 (by omega)] at r1
    have r2 := Reach.step (c := (a + 1, update ρ s (ρ s - 1))) h1 (incI_ne _ _)
    rw [step_at_inc h1] at r2
    have r3 := Reach.step (c := (a + 2, update (update ρ s (ρ s - 1)) d
      (update ρ s (ρ s - 1) d + 1))) h2 (incI_ne _ _)
    rw [step_at_inc h2] at r3
    have r4 := ih (update (update (update ρ s (ρ s - 1)) d (update ρ s (ρ s - 1) d + 1)) t
      (update (update ρ s (ρ s - 1)) d (update ρ s (ρ s - 1) d + 1) t + 1))
      (by simp [update_apply, hsd, hst, Ne.symm hsd, Ne.symm hst]; omega)
    refine (r1.trans (r2.trans (r3.trans r4))).trans ?_
    convert Reach.refl _ using 2
    funext x
    simp only [update_apply]
    split_ifs <;> subst_vars <;> omega

/-! #### Counted loops: `while K ≠ 0 do (K--, body)` -/

/-- The loop around a body of length `lb` placed at `a + 1`. -/
def loopC (K : ℕ) (body : ℕ → List Instr) (lb a : ℕ) : List Instr :=
  [decI K (a + 2 + lb) (a + 1)] ++ body (a + 1) ++ [decI K (a + 2 + lb) (a + 1)]

theorem loopC_length (K : ℕ) (body : ℕ → List Instr) (lb a : ℕ) (hb : (body (a + 1)).length = lb) :
    (loopC K body lb a).length = lb + 2 := by
  simp [loopC, hb]

/-- **Loop lemma** with an invariant indexed by the number of completed iterations. -/
theorem loopC_run {K lb a : ℕ} {body : ℕ → List Instr} (hb : (body (a + 1)).length = lb)
    (h : Emb P a (loopC K body lb a)) (I : ℕ → (ℕ → ℕ) → Prop)
    (hbody : ∀ i ρ, I i ρ → ρ K ≠ 0 → ∃ ρ', Reach P (a + 1, update ρ K (ρ K - 1)) (a + 1 + lb, ρ') ∧
      I (i + 1) ρ' ∧ ρ' K = ρ K - 1) :
    ∀ ρ, I 0 ρ → ∃ ρ', Reach P (a, ρ) (a + 2 + lb, ρ') ∧ I (ρ K) ρ' ∧ ρ' K = 0 := by
  have h0 : P[a]? = some (decI K (a + 2 + lb) (a + 1)) := by
    simpa [loopC] using h.get (i := 0) (by simp [loopC])
  have hend : P[a + 1 + lb]? = some (decI K (a + 2 + lb) (a + 1)) := by
    have := h.get (i := 1 + lb) (by rw [loopC_length K body lb a hb]; omega)
    rw [show a + (1 + lb) = a + 1 + lb by omega] at this
    rw [this]
    simp only [loopC, List.append_assoc, Option.some.injEq]
    rw [List.getElem_append_right (by simp), List.getElem_append_right (by simp [hb])]
    simp [hb]
  have hstart : ∀ s, (s = a ∨ s = a + 1 + lb) → P[s]? = some (decI K (a + 2 + lb) (a + 1)) := by
    rintro s (rfl | rfl)
    · exact h0
    · exact hend
  have key : ∀ (v i : ℕ) (ρ : ℕ → ℕ) (s : ℕ), ρ K = v → I i ρ → (s = a ∨ s = a + 1 + lb) →
      ∃ ρ', Reach P (s, ρ) (a + 2 + lb, ρ') ∧ I (i + v) ρ' ∧ ρ' K = 0 := by
    intro v
    induction v with
    | zero =>
      intro i ρ s hv hI hs
      have := Reach.step (c := (s, ρ)) (hstart s hs) (decI_ne _ _ _)
      rw [step_at_dec_zero (hstart s hs) hv] at this
      exact ⟨ρ, this, by simpa using hI, hv⟩
    | succ v ih =>
      intro i ρ s hv hI hs
      have r1 := Reach.step (c := (s, ρ)) (hstart s hs) (decI_ne _ _ _)
      rw [step_at_dec_pos (hstart s hs) (by omega)] at r1
      obtain ⟨ρ', r2, hI', hK'⟩ := hbody i ρ hI (by omega)
      obtain ⟨ρ'', r3, hI'', hK''⟩ := ih (i + 1) ρ' (a + 1 + lb) (by omega) hI' (Or.inr rfl)
      exact ⟨ρ'', r1.trans (r2.trans r3), by rwa [show i + (v + 1) = i + 1 + v by omega], hK''⟩
  intro ρ hI
  obtain ⟨ρ', hr, hI', hK⟩ := key (ρ K) 0 ρ a rfl hI (Or.inl rfl)
  exact ⟨ρ', hr, by simpa using hI', hK⟩

end Blocks

end ClaudeUndec
