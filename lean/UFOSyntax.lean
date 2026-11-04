/-
Claude, 27 Sep 2026.  Undecidability, part A1: normalized first-order sentences and their
semantics.

A *normalized sentence* is the output of the manuscript's fixed normalization (Skolemize, put
the universal matrix in CNF, flatten terms): a signature (arities of relation symbols and of
function symbols; constants are functions of arity `0`) and a finite list of clauses.  A clause
is a finite list of literals; a literal is a sign and an atom of one of the three forms

    R(v_1,…,v_a),        v_{a+1} = f(v_1,…,v_a),        v_i = v_j,

where the `v`'s are clause-local variables `0, 1, 2, …`.  Each clause is universally closed; its
variables are `0, …, nvars c - 1` with `nvars c` one more than the largest variable index
occurring (so every clause is well formed by construction).

All data are built from `ℕ`, `List`, `Bool`, products and sums, so the type of sentences is
`Primcodable` with Mathlib's standard coding; this is used for the computability statements.

Semantics: a structure on a type `α` interprets relation symbols as predicates on lists and
function symbols as functions on lists.  An atom whose symbol is out of range, or whose argument
list has the wrong length, is false.  Equality is actual equality.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD

set_option autoImplicit false

namespace ClaudeUndec

/-- Atoms: `inl (R, args)` is `R(args)`; `inr (inl ((f, args), out))` is `out = f(args)`;
`inr (inr (i, j))` is `i = j`. -/
abbrev Atom := (ℕ × List ℕ) ⊕ ((ℕ × List ℕ) × ℕ) ⊕ (ℕ × ℕ)

/-- A literal: the sign (`true` = positive) and the atom. -/
abbrev Lit := Bool × Atom

abbrev Clause := List Lit

/-- A normalized sentence: `((relation arities, function arities), clauses)`. -/
abbrev Sentence := (List ℕ × List ℕ) × List Clause

namespace Atom
abbrev rel (R : ℕ) (args : List ℕ) : Atom := Sum.inl (R, args)
abbrev graph (f : ℕ) (args : List ℕ) (out : ℕ) : Atom := Sum.inr (Sum.inl ((f, args), out))
abbrev eq (i j : ℕ) : Atom := Sum.inr (Sum.inr (i, j))

/-- The variables of an atom. -/
def vars : Atom → List ℕ
  | Sum.inl (_, args) => args
  | Sum.inr (Sum.inl ((_, args), out)) => out :: args
  | Sum.inr (Sum.inr (i, j)) => [i, j]
end Atom

namespace Sentence
variable (φ : Sentence)
abbrev rels : List ℕ := φ.1.1
abbrev funs : List ℕ := φ.1.2
abbrev clauses : List Clause := φ.2
end Sentence

/-- Number of variables of a clause: one more than the largest variable index. -/
def nvars (c : Clause) : ℕ := ((c.flatMap fun l => l.2.vars).foldr max 0) + 1

theorem le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem var_lt_nvars {c : Clause} {l : Lit} (hl : l ∈ c) {x : ℕ} (hx : x ∈ l.2.vars) :
    x < nvars c := by
  unfold nvars
  have : x ∈ c.flatMap fun l => l.2.vars := List.mem_flatMap.mpr ⟨l, hl, hx⟩
  have := le_foldr_max _ x this
  omega

/-! ### Structures and satisfaction -/

/-- A structure for a sentence's signature on a type `α`. -/
structure Str (α : Type) where
  rel : ℕ → List α → Prop
  fn : ℕ → List α → α

variable {α : Type}

/-- Truth of an atom under a variable assignment `σ`.  Ill-formed atoms are false. -/
def atomHolds (φ : Sentence) (M : Str α) (σ : ℕ → α) : Atom → Prop
  | Sum.inl (R, args) =>
      R < φ.rels.length ∧ args.length = φ.rels.getD R 0 ∧ M.rel R (args.map σ)
  | Sum.inr (Sum.inl ((f, args), out)) =>
      f < φ.funs.length ∧ args.length = φ.funs.getD f 0 ∧ σ out = M.fn f (args.map σ)
  | Sum.inr (Sum.inr (i, j)) => σ i = σ j

def litHolds (φ : Sentence) (M : Str α) (σ : ℕ → α) (l : Lit) : Prop :=
  if l.1 then atomHolds φ M σ l.2 else ¬ atomHolds φ M σ l.2

def clauseHolds (φ : Sentence) (M : Str α) (σ : ℕ → α) (c : Clause) : Prop :=
  ∃ l ∈ c, litHolds φ M σ l

/-- `M` is a model of the (universally closed) normalized sentence `φ`. -/
def IsModel (φ : Sentence) (M : Str α) : Prop :=
  ∀ c ∈ φ.clauses, ∀ σ : ℕ → α, clauseHolds φ M σ c

/-- `φ` has a model of size exactly `n`, i.e. on `Fin n`. -/
def HasModelOfSize (φ : Sentence) (n : ℕ) : Prop := ∃ M : Str (Fin n), IsModel φ M

end ClaudeUndec
