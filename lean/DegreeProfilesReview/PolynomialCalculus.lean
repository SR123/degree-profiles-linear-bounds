/-
Prompt 04 (a), part 1: ordinary Polynomial Calculus derivations.

* Ordinary commutative polynomial ring `MvPolynomial σ K` over a field `K`.
* A derivation is a finite *sequence* of lines (a `List`, most recent line first).
  Each line is an input axiom, a `K`-linear combination of earlier lines (membership of
  the `K`-span of the earlier lines; the empty combination gives `0`), or `X i` times
  an earlier line.
* The degree of a derivation is the maximum ordinary total degree of its lines
  (`MvPolynomial.totalDegree`, with `totalDegree 0 = 0`).  There is no multilinearisation,
  no Boolean quotient and no truncation: an axiom of degree `> d` can never be a line
  of a degree-`≤ d` derivation, so "use a high-degree input and cancel" is not allowed.

No external hypothesis is used in this file.
-/
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.ENat.Basic

open MvPolynomial

namespace DegreeProfilesReview.PC

variable {σ : Type*} {K : Type*} [Field K]

/-- `IsProof Γ l`: the list `l` (most recent line first) is an ordinary PC derivation
from the axiom set `Γ`. -/
inductive IsProof (Γ : Set (MvPolynomial σ K)) : List (MvPolynomial σ K) → Prop
  | nil : IsProof Γ []
  | ax {l : List (MvPolynomial σ K)} {f : MvPolynomial σ K} :
      IsProof Γ l → f ∈ Γ → IsProof Γ (f :: l)
  | lin {l : List (MvPolynomial σ K)} {f : MvPolynomial σ K} :
      IsProof Γ l → f ∈ Submodule.span K {g | g ∈ l} → IsProof Γ (f :: l)
  | mulX {l : List (MvPolynomial σ K)} {g : MvPolynomial σ K} (i : σ) :
      IsProof Γ l → g ∈ l → IsProof Γ (X i * g :: l)

/-- All lines have total degree at most `d`. -/
def DegBounded (d : ℕ) (l : List (MvPolynomial σ K)) : Prop :=
  ∀ g ∈ l, g.totalDegree ≤ d

/-- `f` is a line of some PC derivation from `Γ` all of whose lines have degree `≤ d`. -/
def Derives (Γ : Set (MvPolynomial σ K)) (d : ℕ) (f : MvPolynomial σ K) : Prop :=
  ∃ l, IsProof Γ l ∧ DegBounded d l ∧ f ∈ l

/-- A degree-`≤ d` PC refutation: a degree-`≤ d` derivation of the constant `1`. -/
def Refutes (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Prop := Derives Γ d 1

theorem IsProof.append {Γ : Set (MvPolynomial σ K)} {l₁ l₂ : List (MvPolynomial σ K)}
    (h₁ : IsProof Γ l₁) (h₂ : IsProof Γ l₂) : IsProof Γ (l₁ ++ l₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hf ih => exact IsProof.ax ih hf
  | lin _ hf ih =>
    refine IsProof.lin ih (Submodule.span_mono ?_ hf)
    intro g hg
    exact List.mem_append_left _ hg
  | mulX i _ hg ih => exact IsProof.mulX i ih (List.mem_append_left _ hg)

theorem DegBounded.append {d : ℕ} {l₁ l₂ : List (MvPolynomial σ K)}
    (h₁ : DegBounded d l₁) (h₂ : DegBounded d l₂) : DegBounded d (l₁ ++ l₂) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h₁ g h
  · exact h₂ g h

theorem DegBounded.cons {d : ℕ} {l : List (MvPolynomial σ K)} {f : MvPolynomial σ K}
    (hf : f.totalDegree ≤ d) (h : DegBounded d l) : DegBounded d (f :: l) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | h'
  · exact hf
  · exact h g h'

theorem Derives.mono {Γ : Set (MvPolynomial σ K)} {d d' : ℕ} (hdd : d ≤ d')
    {f : MvPolynomial σ K} (h : Derives Γ d f) : Derives Γ d' f := by
  obtain ⟨l, hp, hb, hm⟩ := h
  exact ⟨l, hp, fun g hg => le_trans (hb g hg) hdd, hm⟩

/-- The degree-`≤ d` consequences form a `K`-subspace. -/
def derivable (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Submodule K (MvPolynomial σ K) where
  carrier := {f | Derives Γ d f}
  zero_mem' := by
    refine ⟨[0], IsProof.lin IsProof.nil (Submodule.zero_mem _), ?_, by simp⟩
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    simp
  add_mem' := by
    rintro a b ⟨l₁, p₁, b₁, m₁⟩ ⟨l₂, p₂, b₂, m₂⟩
    refine ⟨(a + b) :: (l₁ ++ l₂), IsProof.lin (p₁.append p₂) ?_, ?_, by simp⟩
    · exact Submodule.add_mem _
        (Submodule.subset_span (List.mem_append_left _ m₁))
        (Submodule.subset_span (List.mem_append_right _ m₂))
    · exact DegBounded.cons
        (le_trans (totalDegree_add a b) (max_le (b₁ a m₁) (b₂ b m₂))) (b₁.append b₂)
  smul_mem' := by
    rintro c a ⟨l, p, hb, m⟩
    refine ⟨(c • a) :: l, IsProof.lin p (Submodule.smul_mem _ c (Submodule.subset_span m)),
      ?_, by simp⟩
    exact DegBounded.cons (le_trans (totalDegree_smul_le c a) (hb a m)) hb

theorem mem_derivable {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K} :
    f ∈ derivable Γ d ↔ Derives Γ d f := Iff.rfl

/-- Deriving `1` is equivalent to deriving any nonzero constant. -/
theorem refutes_iff_const {Γ : Set (MvPolynomial σ K)} {d : ℕ} {c : K} (hc : c ≠ 0) :
    Refutes Γ d ↔ Derives Γ d (C c) := by
  unfold Refutes
  rw [← mem_derivable, ← mem_derivable]
  constructor
  · intro h
    have := (derivable Γ d).smul_mem c h
    rwa [smul_eq_C_mul, mul_one] at this
  · intro h
    have := (derivable Γ d).smul_mem c⁻¹ h
    rwa [smul_eq_C_mul, ← C_mul, inv_mul_cancel₀ hc, C_1] at this

/-! ### The degree of `X i * g` -/

/-- For `g ≠ 0` over a field, `deg (X i * g) ≥ deg g + 1`: multiplication by a variable
cannot lower the degree of a nonzero polynomial. -/
theorem totalDegree_succ_le_X_mul (i : σ) {g : MvPolynomial σ K} (hg : g ≠ 0) :
    g.totalDegree + 1 ≤ (X i * g).totalDegree := by
  classical
  have hne : g.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hg (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup g.support hne (fun s => s.sum fun _ e => e)
  have hm' : Finsupp.single i 1 + m ∈ (X i * g).support := by
    rw [MvPolynomial.mem_support_iff, coeff_X_mul]
    exact MvPolynomial.mem_support_iff.mp hm
  have hle := le_totalDegree hm'
  have hsum : (Finsupp.single i 1 + m).sum (fun _ e => e) = 1 + m.sum (fun _ e => e) := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl]
  rw [hsum] at hle
  have : g.totalDegree = m.sum (fun _ e => e) := hsup
  omega

end DegreeProfilesReview.PC
