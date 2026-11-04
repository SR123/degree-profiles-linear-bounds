/-
Claude, 27 Sep 2026.  Undecidability, part B1: counter machines and the sentence `θ_M`
(manuscript `lem:switch`).

Machines have finitely many counters, all starting at `0`, and instructions

    inc(r, ℓ')          increment counter r, go to ℓ',
    dec(r, ℓ₀, ℓ₊)      if counter r is 0 go to ℓ₀, else decrement it and go to ℓ₊,
    halt.

States are `0, …, |P|`; a jump target `≥ |P|` is replaced by the halting state `|P|`
(`norm`).  The run from the zero configuration is `cfg P j`.  The manuscript uses two counters;
here any number `K = ncnt P` is allowed (the proof does not depend on it).

`θ_M` (`theta P`) is the manuscript's sentence over a strict order `<`, constants `o, e`, unary
functions `S, C_0, …, C_{K-1}` and unary relations `Q_0, …, Q_{|P|}`, given directly in
normalized, flattened clausal form.  Indices: relation `0` is `<`, relation `1 + ℓ` is `Q_ℓ`;
function `0` is `o`, `1` is `e`, `2` is `S`, `3 + r` is `C_r`.  Clause variables:
`t = 0, u = 1, v = 2, c = 3, w = 4, p = 5, d = 6, z = 7`.
-/
import UConj

set_option autoImplicit false

namespace ClaudeUndec

/-! ### Machines and runs -/

/-- `inl (r, ℓ')`: increment; `inr (inl (r, ℓ₀, ℓ₊))`: decrement; `inr (inr ())`: halt. -/
abbrev Instr := (ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ) ⊕ Unit
abbrev Prog := List Instr

namespace Prog
variable (P : Prog)

/-- The counters used are `0, …, ncnt P - 1`. -/
def instrCnt : Instr → ℕ
  | Sum.inl (r, _) => r
  | Sum.inr (Sum.inl (r, _, _)) => r
  | Sum.inr (Sum.inr _) => 0

def ncnt : ℕ := (P.map instrCnt).foldr max 0 + 1

/-- Normalized state: jump targets beyond the program become the halting state `|P|`. -/
def norm (ℓ : ℕ) : ℕ := min ℓ P.length

/-- A halting state: out of range, or a `halt` instruction. -/
def IsHaltSt (ℓ : ℕ) : Prop := P.length ≤ ℓ ∨ P[ℓ]? = some (Sum.inr (Sum.inr ()))

/-- One step; halting configurations are fixed. -/
def step (c : ℕ × (ℕ → ℕ)) : ℕ × (ℕ → ℕ) :=
  match P[c.1]? with
  | some (Sum.inl (r, ℓ')) => (ℓ', Function.update c.2 r (c.2 r + 1))
  | some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁))) =>
      if c.2 r = 0 then (ℓ₀, c.2) else (ℓ₁, Function.update c.2 r (c.2 r - 1))
  | _ => c

/-- The configuration at time `j` of the run from the zero configuration. -/
def cfg (j : ℕ) : ℕ × (ℕ → ℕ) := (step P)^[j] (0, fun _ => 0)

/-- The machine halts (from zero). -/
def Halts : Prop := ∃ j, P.IsHaltSt (P.cfg j).1

theorem cfg_succ (j : ℕ) : P.cfg (j + 1) = P.step (P.cfg j) := by
  unfold cfg; rw [Function.iterate_succ_apply']

theorem cfg_zero : P.cfg 0 = (0, fun _ => 0) := rfl

theorem step_le (c : ℕ × (ℕ → ℕ)) (r : ℕ) : (P.step c).2 r ≤ c.2 r + 1 := by
  unfold step
  split
  · simp only [Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> omega
  · split_ifs
    · show c.2 r ≤ c.2 r + 1; omega
    · simp only [Function.update_apply]; split_ifs with h <;> [subst h; skip] <;> omega
  · omega

/-- Counter values are at most the time. -/
theorem cfg_le (j r : ℕ) : (P.cfg j).2 r ≤ j := by
  induction j generalizing r with
  | zero => simp [cfg]
  | succ j ih => rw [cfg_succ]; have := P.step_le (P.cfg j) r; have := ih r; omega

instance : DecidablePred P.IsHaltSt := fun ℓ => by unfold IsHaltSt; infer_instance

end Prog

/-! ### The sentence `θ_M` -/

section Theta
variable (P : Prog)

def pos (a : Atom) : Lit := (true, a)
def neg (a : Atom) : Lit := (false, a)

/-- `i < j`. -/
def ltA (i j : ℕ) : Atom := Atom.rel 0 [i, j]
/-- `Q_ℓ(i)`. -/
def qA (ℓ i : ℕ) : Atom := Atom.rel (1 + ℓ) [i]
/-- `u = o`, `u = e`. -/
def isO (u : ℕ) : Atom := Atom.graph 0 [] u
def isE (u : ℕ) : Atom := Atom.graph 1 [] u
/-- `v = S(t)`. -/
def sOf (v t : ℕ) : Atom := Atom.graph 2 [t] v
/-- `c = C_r(t)`. -/
def cOf (r c t : ℕ) : Atom := Atom.graph (3 + r) [t] c

/-- Relation arities: `<` then `Q_0, …, Q_{|P|}`. -/
def thRels : List ℕ := 2 :: List.replicate (P.length + 1) 1
/-- Function arities: `o, e, S, C_0, …, C_{K-1}`. -/
def thFuns : List ℕ := 0 :: 0 :: 1 :: List.replicate P.ncnt 1

/-- Order, successor and state clauses. -/
def baseClauses : List Clause :=
  [ [neg (ltA 0 0)],
    [neg (ltA 0 7), neg (ltA 7 2), pos (ltA 0 2)],
    [pos (ltA 0 2), pos (Atom.eq 0 2), pos (ltA 2 0)],
    [neg (isO 1), pos (Atom.eq 0 1), pos (ltA 1 0)],
    [neg (isE 1), pos (Atom.eq 0 1), pos (ltA 0 1)],
    [neg (isE 1), neg (sOf 2 1), pos (Atom.eq 2 1)],
    [neg (isE 1), pos (Atom.eq 0 1), neg (sOf 2 0), pos (ltA 0 2)],
    [neg (isE 1), pos (Atom.eq 0 1), neg (sOf 2 0), neg (ltA 0 7), neg (ltA 7 2)],
    (List.range (P.length + 1)).map (fun ℓ => pos (qA ℓ 0)),
    [neg (isO 1), pos (qA 0 1)] ] ++
  (List.range (P.length + 1)).flatMap (fun a => (List.range (P.length + 1)).filterMap
    (fun b => if a < b then some [neg (qA a 0), neg (qA b 0)] else none)) ++
  (List.range P.ncnt).map (fun r => [neg (isO 1), neg (cOf r 3 1), pos (Atom.eq 3 1)]) ++
  ((List.range (P.length + 1)).filter (fun ℓ => decide (P.IsHaltSt ℓ))).map
    (fun ℓ => [neg (qA ℓ 0)])

/-- The common premise of a transition: `t ≠ e`, `Q_ℓ(t)`, `v = S(t)`. -/
def pre (ℓ : ℕ) : Clause := [neg (isE 1), pos (Atom.eq 0 1), neg (qA ℓ 0), neg (sOf 2 0)]

/-- Other counters are unchanged. -/
def sameClauses (ℓ r : ℕ) (extra : Clause) : List Clause :=
  ((List.range P.ncnt).filter (fun r' => r' ≠ r)).map
    (fun r' => pre ℓ ++ extra ++ [neg (cOf r' 6 0), pos (cOf r' 6 2)])

/-- The transition clauses of the instruction at state `ℓ`. -/
def transClauses (ℓ : ℕ) : Instr → List Clause
  | Sum.inl (r, ℓ') =>
      [ pre ℓ ++ [neg (cOf r 3 0), neg (Atom.eq 3 1)],
        pre ℓ ++ [neg (cOf r 3 0), neg (sOf 4 3), pos (cOf r 4 2)],
        pre ℓ ++ [pos (qA (P.norm ℓ') 2)] ] ++ sameClauses P ℓ r []
  | Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)) =>
      [ pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5), pos (cOf r 3 2)],
        pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5), pos (qA (P.norm ℓ₀) 2)],
        pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5), neg (cOf r 6 2), pos (ltA 6 3)],
        pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5), neg (cOf r 6 2), neg (sOf 4 6),
          pos (Atom.eq 4 3)],
        pre ℓ ++ [neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5), pos (qA (P.norm ℓ₁) 2)] ] ++
      sameClauses P ℓ r [neg (isO 5), neg (cOf r 3 0), neg (Atom.eq 3 5)] ++
      sameClauses P ℓ r [neg (isO 5), neg (cOf r 3 0), pos (Atom.eq 3 5)]
  | Sum.inr (Sum.inr _) => []

/-- **The sentence `θ_M`.** -/
def theta : Sentence :=
  ((thRels P, thFuns P),
    baseClauses P ++ (List.range P.length).flatMap
      (fun ℓ => match P[ℓ]? with | some i => transClauses P ℓ i | none => []))

/-! ### Evaluating the atoms of `θ_M` -/

theorem thRels_length : (thRels P).length = P.length + 2 := by simp [thRels]
theorem thFuns_length : (thFuns P).length = P.ncnt + 3 := by simp [thFuns]

theorem thRels_getD_zero : (thRels P).getD 0 0 = 2 := rfl
theorem thRels_getD_q {ℓ : ℕ} (h : ℓ ≤ P.length) : (thRels P).getD (1 + ℓ) 0 = 1 := by
  simp only [thRels, show 1 + ℓ = ℓ + 1 by omega, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
theorem thFuns_getD_o : (thFuns P).getD 0 0 = 0 := rfl
theorem thFuns_getD_e : (thFuns P).getD 1 0 = 0 := rfl
theorem thFuns_getD_S : (thFuns P).getD 2 0 = 1 := rfl
theorem thFuns_getD_C {r : ℕ} (h : r < P.ncnt) : (thFuns P).getD (3 + r) 0 = 1 := by
  simp only [thFuns, show 3 + r = r + 1 + 1 + 1 by omega, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp

variable {α : Type} (M : Str α) (σ : ℕ → α)

theorem holds_ltA (i j : ℕ) : atomHolds (theta P) M σ (ltA i j) ↔ M.rel 0 [σ i, σ j] := by
  simp only [ltA, atomHolds, Sentence.rels, theta, thRels_getD_zero, thRels_length]
  simp

theorem holds_qA {ℓ : ℕ} (h : ℓ ≤ P.length) (i : ℕ) :
    atomHolds (theta P) M σ (qA ℓ i) ↔ M.rel (1 + ℓ) [σ i] := by
  simp only [qA, atomHolds, Sentence.rels, theta, thRels_getD_q P h, thRels_length]
  simp only [List.length_singleton, List.map_cons, List.map_nil, true_and]
  constructor
  · exact fun h => h.2
  · exact fun h' => ⟨by omega, h'⟩

theorem holds_isO (u : ℕ) : atomHolds (theta P) M σ (isO u) ↔ σ u = M.fn 0 [] := by
  simp only [isO, atomHolds, Sentence.funs, theta, thFuns_getD_o, thFuns_length]
  simp

theorem holds_isE (u : ℕ) : atomHolds (theta P) M σ (isE u) ↔ σ u = M.fn 1 [] := by
  simp only [isE, atomHolds, Sentence.funs, theta, thFuns_getD_e, thFuns_length]
  simp

theorem holds_sOf (v t : ℕ) : atomHolds (theta P) M σ (sOf v t) ↔ σ v = M.fn 2 [σ t] := by
  simp only [sOf, atomHolds, Sentence.funs, theta, thFuns_getD_S, thFuns_length]
  simp

theorem holds_cOf {r : ℕ} (hr : r < P.ncnt) (c t : ℕ) :
    atomHolds (theta P) M σ (cOf r c t) ↔ σ c = M.fn (3 + r) [σ t] := by
  simp only [cOf, atomHolds, Sentence.funs, theta, thFuns_getD_C P hr, thFuns_length]
  simp only [List.length_singleton, List.map_cons, List.map_nil, true_and]
  constructor
  · exact fun h => h.2
  · exact fun h' => ⟨by omega, h'⟩

theorem holds_eq (i j : ℕ) : atomHolds (theta P) M σ (Atom.eq i j) ↔ σ i = σ j := Iff.rfl

theorem litHolds_pos (a : Atom) : litHolds (theta P) M σ (pos a) ↔ atomHolds (theta P) M σ a := by
  simp [litHolds, pos]
theorem litHolds_neg (a : Atom) : litHolds (theta P) M σ (neg a) ↔ ¬ atomHolds (theta P) M σ a := by
  simp [litHolds, neg]

theorem clauseHolds_cons (l : Lit) (c : Clause) :
    clauseHolds (theta P) M σ (l :: c) ↔ litHolds (theta P) M σ l ∨ clauseHolds (theta P) M σ c := by
  simp [clauseHolds]
theorem clauseHolds_nil : ¬ clauseHolds (theta P) M σ [] := by simp [clauseHolds]
theorem clauseHolds_append (c c' : Clause) :
    clauseHolds (theta P) M σ (c ++ c') ↔ clauseHolds (theta P) M σ c ∨ clauseHolds (theta P) M σ c' := by
  simp [clauseHolds, or_and_right, exists_or]

end Theta

end ClaudeUndec
