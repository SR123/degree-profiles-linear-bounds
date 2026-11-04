/-
Claude, 27 Sep 2026.  Undecidability, part E1: the witnesses `ψ₁` (type T1) and `η` (type T2).

* `psi1 = ∀x (R(x) ∧ ¬R(x))`: two clause groundings sum to `1`, so the NS degree is at most `1` at
  every `n ≥ 1`; no nonempty model.
* `eta`: a unary function `g` is injective and a constant `c` lies outside its image.  Its
  graph-and-sum translation is mapped, by an injective renaming of variables (labels `i ↦ i+1`),
  onto the project's system `G_n` (`SelfContainedCycle072.IsGAxiom`): totality sums go to row sums
  and the constant sum, collisions to collisions, Booleans to Booleans, injectivity groundings to
  column collisions (or `0` for repeated labels) and the guard groundings to `x_{ij} c_j`.  An NS
  refutation of degree `d` therefore gives one of `G_n`, and `G_both_linear` (an unconditional
  project theorem) gives `n < 3 p d` for `n ≥ 3`.  No nonempty model (a total injection of `[n]`
  into `[n] \ {c}` does not exist).
-/
import UWitCommon
import UCounter
import PigeonholeRestriction

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open MvPolynomial DegreeProfilesReview.NS DegreeProfilesReview.Uniform

/-! ### `ψ₁` -/

/-- `ψ₁ = ∀x (R(x) ∧ ¬R(x))`. -/
def psi1 : Sentence := (([1], []), [[pos (Atom.rel 0 [0])], [neg (Atom.rel 0 [0])]])

theorem psi1_WF : WF psi1 := by
  intro c hc l hl
  simp only [psi1, Sentence.clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
  · simp only [List.mem_singleton] at hl
    subst hl
    exact ⟨by decide, rfl⟩

theorem psi1_nsRefutes (K : Type) [Field K] {n : ℕ} (hn : 0 < n) :
    NSRefutes ((template psi1 K).inst n) 1 := by
  rw [nsRefutes_iff_one_mem_NSspan]
  let ν : ℕ → Fin n := fun _ => ⟨0, hn⟩
  have h1 := clause_mem psi1 K (c := [pos (Atom.rel 0 [0])]) (by simp [psi1, Sentence.clauses]) ν
  have h2 := clause_mem psi1 K (c := [neg (Atom.rel 0 [0])]) (by simp [psi1, Sentence.clauses]) ν
  have hv := atomVal_rel psi1 K hn ν (R := 0) (args := [0]) (by decide) rfl
  simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    litFactor, pos, neg, if_true, Bool.false_eq_true, if_false, hv] at h1 h2
  have e : (1 : MvPolynomial ((VarSys psi1).Rk n) K) =
      (1 - X (rvN psi1 n ⟨0, by decide⟩ (tupL hn ([0].map ν)))) +
        X (rvN psi1 n ⟨0, by decide⟩ (tupL hn ([0].map ν))) := by ring
  rw [e]
  refine add_mem (NSspan_mono' ?_ (mem_NSspan_of_mem h1)) (NSspan_mono' ?_ (mem_NSspan_of_mem h2))
  · exact le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_X_le' _))
  · exact totalDegree_X_le' _

theorem psi1_no_model {n : ℕ} (hn : 0 < n) : ¬ HasModelOfSize psi1 n := by
  rintro ⟨M, hM⟩
  have h1 := hM [pos (Atom.rel 0 [0])] (by simp [psi1, Sentence.clauses]) (fun _ => ⟨0, hn⟩)
  have h2 := hM [neg (Atom.rel 0 [0])] (by simp [psi1, Sentence.clauses]) (fun _ => ⟨0, hn⟩)
  simp only [clauseHolds, List.mem_singleton, exists_eq_left, litHolds, pos, neg, if_true,
    Bool.false_eq_true, if_false, atomHolds] at h1 h2
  exact h2 h1

/-! ### `η` -/

/-- `η`: `g` (function `0`, unary) injective, `c` (function `1`, a constant) outside its image. -/
def eta : Sentence := (([], [1, 0]),
  [[neg (Atom.graph 0 [0] 2), neg (Atom.graph 0 [1] 2), pos (Atom.eq 0 1)],
   [neg (Atom.graph 0 [0] 1), neg (Atom.graph 1 [] 1)]])

theorem eta_WF : WF eta := by
  intro c hc l hl
  simp only [eta, Sentence.clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩
    · trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, rfl⟩

theorem eta_no_model {n : ℕ} (_hn : 0 < n) : ¬ HasModelOfSize eta n := by
  rintro ⟨M, hM⟩
  have hinj : ∀ x y : Fin n, M.fn 0 [x] = M.fn 0 [y] → x = y := by
    intro x y hxy
    have h := hM [neg (Atom.graph 0 [0] 2), neg (Atom.graph 0 [1] 2), pos (Atom.eq 0 1)]
      (by simp [eta, Sentence.clauses])
      (fun v => if v = 0 then x else if v = 1 then y else M.fn 0 [x])
    simp only [clauseHolds, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litHolds, neg, pos, if_true, Bool.false_eq_true, if_false, atomHolds,
      eta, Sentence.funs] at h
    simp at h
    tauto
  have hc : ∀ x : Fin n, M.fn 0 [x] ≠ M.fn 1 [] := by
    intro x hx
    have h := hM [neg (Atom.graph 0 [0] 1), neg (Atom.graph 1 [] 1)]
      (by simp [eta, Sentence.clauses]) (fun v => if v = 0 then x else M.fn 0 [x])
    simp only [clauseHolds, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litHolds, neg, pos, Bool.false_eq_true, if_false, atomHolds,
      eta, Sentence.funs] at h
    simp at h
    exact h hx
  -- a total injection into the complement of `c`
  let g : Fin n → Fin n := fun x => M.fn 0 [x]
  have hg : Function.Injective g := fun x y h => hinj x y h
  have hsurj := (Finite.injective_iff_surjective.mp hg) (M.fn 1 [])
  obtain ⟨x, hx⟩ := hsurj
  exact hc x hx

section EtaMap
open SelfContainedCycle054 SelfContainedCycle072
variable {n : ℕ}

/-- Labels `0, …, n-1` as the project's labels `1, …, n`. -/
def lab (i : Fin n) : Label n := ⟨i.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem lab_injective : Function.Injective (lab (n := n)) := by
  intro i j h
  apply Fin.ext
  have := congrArg Subtype.val h
  simp only [lab] at this
  omega

/-- `lab` is a bijection. -/
noncomputable def labEquiv : Fin n ≃ Label n :=
  Equiv.ofBijective lab ⟨lab_injective, fun j => by
    obtain ⟨v, hv⟩ := j
    have := Finset.mem_Icc.mp hv
    exact ⟨⟨v - 1, by omega⟩, Subtype.ext (by simp [lab]; omega)⟩⟩

theorem sum_lab {M : Type} [AddCommMonoid M] (F : Label n → M) :
    ∑ j : Fin n, F (lab j) = ∑ j : Label n, F j :=
  Fintype.sum_equiv labEquiv _ _ (fun _ => rfl)

/-- The renaming of the variables of `η` into `G_n`. -/
def etaVar : (VarSys eta).Rk n → GVar n
  | ⟨Sum.inl R, _⟩ => R.elim0
  | ⟨Sum.inr f, t⟩ =>
      let t' : Fin (eta.funs.get f + 1) → Fin n := t
      if f.val = 0 then Sum.inl (lab (t' 0), lab (t' (Fin.last _))) else Sum.inr (lab (t' (Fin.last _)))

theorem etaVar_g (t : Fin (eta.funs.get ⟨0, by decide⟩) → Fin n) (j : Fin n) :
    etaVar (gvN eta n ⟨0, by decide⟩ t j) = Sum.inl (lab (t ⟨0, by decide⟩), lab j) := by
  simp only [etaVar, gvN, if_true]
  rfl

theorem etaVar_c (t : Fin (eta.funs.get ⟨1, by decide⟩) → Fin n) (j : Fin n) :
    etaVar (gvN eta n ⟨1, by decide⟩ t j) = Sum.inr (lab j) := by
  simp only [etaVar, gvN]
  rfl

variable (K : Type) [Field K]

theorem etaMap_gX0 (hn : 0 < n) (a b : Fin n) :
    rename etaVar (gX eta K hn 0 [a] b) = X (Sum.inl (lab a, lab b)) := by
  simp only [gX, dif_pos (show 0 < eta.funs.length by decide), rename_X]
  rw [etaVar_g]
  rfl

theorem etaMap_gX1 (hn : 0 < n) (b : Fin n) :
    rename etaVar (gX eta K hn 1 [] b) = X (Sum.inr (lab b)) := by
  simp only [gX, dif_pos (show 1 < eta.funs.length by decide), rename_X]
  rw [etaVar_c]

theorem bool_G (w : GVar n) : IsGAxiom (F := K) n (X w ^ 2 - X w) := by
  rcases w with w | j
  · have := IsGAxiom.base (F := K) (n := n) _ (IsHAxiom.boolean w)
    simpa [boolAxiom] using this
  · exact IsGAxiom.constBoolean j

/-- Every axiom of the translation of `η` is renamed to an axiom of `G_n` or to `0`. -/
theorem eta_hom_mem (hn : 0 < n) {g : MvPolynomial ((VarSys eta).Rk n) K}
    (hg : g ∈ (template eta K).inst n) :
    rename etaVar g ∈ {f | IsGAxiom (F := K) n f} ∨ rename etaVar g = 0 := by
  classical
  rcases inst_cases eta K hg with ⟨f, t, rfl⟩ | ⟨f, t, j, j', hjj, rfl⟩ | ⟨v, rfl⟩ |
    ⟨c, hc, ν, rfl⟩
  · -- totality
    left
    match f, t with
    | ⟨0, h⟩, t =>
      have e : rename etaVar ((∑ j : Fin n, X (gvN eta n ⟨0, h⟩ t j)) - 1 :
          MvPolynomial ((VarSys eta).Rk n) K) =
          rename Sum.inl (rowAxiom (F := K) (m := n) (lab (t ⟨0, Nat.one_pos⟩))) := by
        simp only [map_sub, map_sum, rename_X, map_one, rowAxiom, etaVar_g]
        rw [sum_lab (fun j => (X (Sum.inl (lab (t ⟨0, Nat.one_pos⟩), j)) :
          MvPolynomial (GVar n) K))]
      rw [e]; exact IsGAxiom.base _ (IsHAxiom.row _)
    | ⟨1, h⟩, t =>
      have e : rename etaVar ((∑ j : Fin n, X (gvN eta n ⟨1, h⟩ t j)) - 1 :
          MvPolynomial ((VarSys eta).Rk n) K) =
          (∑ j : Label n, X (Sum.inr j)) - 1 := by
        simp only [map_sub, map_sum, rename_X, map_one, etaVar_c]
        rw [sum_lab (fun j => (X (Sum.inr j) : MvPolynomial (GVar n) K))]
      rw [e]; exact IsGAxiom.constTotal
  · -- collisions
    left
    match f, t with
    | ⟨0, h⟩, t =>
      have e : rename etaVar (X (gvN eta n ⟨0, h⟩ t j) * X (gvN eta n ⟨0, h⟩ t j') :
          MvPolynomial ((VarSys eta).Rk n) K) =
          rename Sum.inl (X (lab (t ⟨0, Nat.one_pos⟩), lab j) * X (lab (t ⟨0, Nat.one_pos⟩), lab j') :
            MvPolynomial (Var n n) K) := by
        simp only [map_mul, rename_X, etaVar_g]
      rw [e]
      exact IsGAxiom.base _ (IsHAxiom.rowCollision _ _ _ (fun h' => hjj (lab_injective h')))
    | ⟨1, h⟩, t =>
      have e : rename etaVar (X (gvN eta n ⟨1, h⟩ t j) * X (gvN eta n ⟨1, h⟩ t j') :
          MvPolynomial ((VarSys eta).Rk n) K) = X (Sum.inr (lab j)) * X (Sum.inr (lab j')) := by
        simp only [map_mul, rename_X, etaVar_c]
      rw [e]
      exact IsGAxiom.constCollision _ _ (fun h' => hjj (lab_injective h'))
  · -- Booleans
    left
    simp only [map_sub, map_pow, rename_X]
    exact bool_G K _
  · -- clause groundings
    simp only [eta, Sentence.clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have h0 := atomVal_graph eta K hn ν (f := 0) (args := [0]) 2 (by decide) rfl
      have h1 := atomVal_graph eta K hn ν (f := 0) (args := [1]) 2 (by decide) rfl
      simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        litFactor, neg, pos, Bool.false_eq_true, if_false, if_true, h0, h1, List.map_cons,
        List.map_nil]
      by_cases he : ν 0 = ν 1
      · right
        simp [atomVal, he]
      · left
        have e : rename etaVar (gX eta K hn 0 [ν 0] (ν 2) * (gX eta K hn 0 [ν 1] (ν 2) *
            (1 - atomVal (K := K) eta (rvN eta n) (gvN eta n) ν (Atom.eq 0 1)))) =
            rename Sum.inl (X (lab (ν 0), lab (ν 2)) * X (lab (ν 1), lab (ν 2)) :
              MvPolynomial (Var n n) K) := by
          simp only [atomVal, if_neg he, sub_zero, mul_one, map_mul, etaMap_gX0, rename_X]
        rw [e]
        exact IsGAxiom.base _ (IsHAxiom.colCollision _ _ _ (fun h' => he (lab_injective h')))
    · have h0 := atomVal_graph eta K hn ν (f := 0) (args := [0]) 1 (by decide) rfl
      have h1 := atomVal_graph eta K hn ν (f := 1) (args := []) 1 (by decide) rfl
      left
      simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        litFactor, neg, Bool.false_eq_true, if_false, h0, h1, map_mul, etaMap_gX0, etaMap_gX1]
      exact IsGAxiom.guard _ _

/-- An NS refutation of `η` gives one of `G_n` of the same degree. -/
theorem eta_nsRefutes_G (hn : 0 < n) {d : ℕ} (h : NSRefutes ((template eta K).inst n) d) :
    NSRefutes {f : MvPolynomial (GVar n) K | IsGAxiom n f} d :=
  nsRefutes_of_hom (rename etaVar) (fun _ => totalDegree_rename_X_le K _ _)
    (fun _ hf => mem_NSspan_of_image (eta_hom_mem K hn hf) (totalDegree_rename_le _ _)) h

/-- **The linear lower bound for `η`** (from the project's `G_both_linear`). -/
theorem eta_lower {p : ℕ} (hp : p.Prime) [CharP K p] (hn : 3 ≤ n) {d : ℕ}
    (h : NSRefutes ((template eta K).inst n) d) : n < 3 * p * d :=
  G_both_linear hp hn (Or.inl (eta_nsRefutes_G K (by omega) h))

end EtaMap

end ClaudeUndec
