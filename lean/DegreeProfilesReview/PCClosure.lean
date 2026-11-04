/-
Prompt 04 (a), part 2: the degree-bounded PC consequence closure, *including the
intersection with lower-degree polynomials*, and its equivalence with actual derivations.

For fixed `d`:
  `W = P_{≤ d}`, `L = P_{≤ d-1}` (and `L = 0` when `d = 0`),
  `V 0   = span of the axioms of degree ≤ d`,
  `V (j+1) = V j ⊔ span { X i * f | f ∈ V j ⊓ L }`.
The intersection `V j ⊓ L` is the honest one: a low-degree element of `V j` may be a
linear combination of high-degree generators (a degree drop by cancellation).

Proved here, with no external hypothesis:
* every element of every `V j` has an ordinary degree-`≤ d` derivation;
* every line of every ordinary degree-`≤ d` derivation lies in `⨆ j, V j`;
* the chain is increasing, one repeated stage freezes it, and for finitely many
  variables it stabilises (finite dimension of `P_{≤ d}`);
* `1 ∈` stabilised space `↔` there is an actual degree-`≤ d` refutation;
* the minimum refutation degree as an element of `ℕ∞`.
-/
import DegreeProfilesReview.PolynomialCalculus
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.MvPolynomial.CommRing

open MvPolynomial

namespace DegreeProfilesReview.PC

variable {σ : Type*} {K : Type*} [Field K]

noncomputable section

/-- `L = P_{≤ d-1}`, with `P_{≤ -1} = 0`. -/
def lowDeg (σ : Type*) (K : Type*) [Field K] (d : ℕ) : Submodule K (MvPolynomial σ K) :=
  if d = 0 then ⊥ else restrictTotalDegree σ K (d - 1)

/-- The image of multiplication `X ⊗ S → K[x]`, as a span: `span {X i * f | f ∈ S}`. -/
def mulStep (S : Submodule K (MvPolynomial σ K)) : Submodule K (MvPolynomial σ K) :=
  Submodule.span K {h | ∃ i : σ, ∃ f ∈ S, h = X i * f}

/-- One closure step. -/
def step (d : ℕ) (V : Submodule K (MvPolynomial σ K)) : Submodule K (MvPolynomial σ K) :=
  V ⊔ mulStep (V ⊓ lowDeg σ K d)

/-- `V 0`: the span of the input equations of degree at most `d`. -/
def V0 (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Submodule K (MvPolynomial σ K) :=
  Submodule.span K {f | f ∈ Γ ∧ f.totalDegree ≤ d}

/-- The closure chain. -/
def V (Γ : Set (MvPolynomial σ K)) (d : ℕ) : ℕ → Submodule K (MvPolynomial σ K)
  | 0 => V0 Γ d
  | j + 1 => step d (V Γ d j)

/-- The eventual closure. -/
def Vinf (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Submodule K (MvPolynomial σ K) :=
  ⨆ j, V Γ d j

theorem mulStep_mono {S T : Submodule K (MvPolynomial σ K)} (h : S ≤ T) :
    mulStep S ≤ mulStep T := by
  apply Submodule.span_mono
  rintro _ ⟨i, f, hf, rfl⟩
  exact ⟨i, f, h hf, rfl⟩

theorem step_mono (d : ℕ) {S T : Submodule K (MvPolynomial σ K)} (h : S ≤ T) :
    step d S ≤ step d T :=
  sup_le_sup h (mulStep_mono (inf_le_inf_right _ h))

theorem V_le_succ (Γ : Set (MvPolynomial σ K)) (d j : ℕ) : V Γ d j ≤ V Γ d (j + 1) :=
  le_sup_left

/-- Prompt 04, item 3 (first part): the chain is increasing. -/
theorem V_mono (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Monotone (V Γ d) :=
  monotone_nat_of_le_succ (V_le_succ Γ d)

/-- A variable times an element of `L` has degree at most `d`.  (`d = 0`: `L = 0`.) -/
theorem totalDegree_X_mul_lowDeg {d : ℕ} (i : σ) {f : MvPolynomial σ K}
    (hf : f ∈ lowDeg σ K d) : (X i * f).totalDegree ≤ d := by
  unfold lowDeg at hf
  split at hf
  · rw [Submodule.mem_bot] at hf
    subst hf
    simp
  · rw [mem_restrictTotalDegree] at hf
    have h1 := totalDegree_mul (X i : MvPolynomial σ K) f
    have h2 : (X i : MvPolynomial σ K).totalDegree = 1 := totalDegree_X i
    omega

/-- Converse (the degree-drop bookkeeping of Prompt 04, item 2): if `X i * g` is a
nonzero-`g` line of degree `≤ d`, then `g ∈ L`.  The case `g = 0` is treated by callers. -/
theorem mem_lowDeg_of_X_mul {d : ℕ} (i : σ) {g : MvPolynomial σ K} (hg : g ≠ 0)
    (h : (X i * g).totalDegree ≤ d) : g ∈ lowDeg σ K d := by
  have h1 := totalDegree_succ_le_X_mul i hg
  unfold lowDeg
  rw [if_neg (by omega), mem_restrictTotalDegree]
  omega

/-- Every stage lies in `W = P_{≤ d}`. -/
theorem V_le_W (Γ : Set (MvPolynomial σ K)) (d j : ℕ) :
    V Γ d j ≤ restrictTotalDegree σ K d := by
  induction j with
  | zero =>
    apply Submodule.span_le.mpr
    rintro f ⟨_, hf⟩
    exact (mem_restrictTotalDegree σ d f).mpr hf
  | succ j ih =>
    apply sup_le ih
    apply Submodule.span_le.mpr
    rintro _ ⟨i, f, hf, rfl⟩
    exact (mem_restrictTotalDegree σ d _).mpr (totalDegree_X_mul_lowDeg i hf.2)

/-- Prompt 04, item 1: every element of every stage has an actual finite ordinary
derivation of degree `≤ d`. -/
theorem V_le_derivable (Γ : Set (MvPolynomial σ K)) (d j : ℕ) : V Γ d j ≤ derivable Γ d := by
  induction j with
  | zero =>
    apply Submodule.span_le.mpr
    rintro f ⟨hfΓ, hfd⟩
    refine ⟨[f], IsProof.ax IsProof.nil hfΓ, ?_, by simp⟩
    intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact hfd
  | succ j ih =>
    apply sup_le ih
    apply Submodule.span_le.mpr
    rintro _ ⟨i, f, hf, rfl⟩
    obtain ⟨l, hp, hb, hm⟩ := ih hf.1
    exact ⟨X i * f :: l, IsProof.mulX i hp hm,
      DegBounded.cons (totalDegree_X_mul_lowDeg i hf.2) hb, by simp⟩

theorem Vinf_le_derivable (Γ : Set (MvPolynomial σ K)) (d : ℕ) : Vinf Γ d ≤ derivable Γ d :=
  iSup_le (V_le_derivable Γ d)

theorem mem_Vinf_iff {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K} :
    f ∈ Vinf Γ d ↔ ∃ j, f ∈ V Γ d j :=
  Submodule.mem_iSup_of_chain ⟨V Γ d, V_mono Γ d⟩ f

/-- Prompt 04, item 2: every line of every ordinary degree-`≤ d` derivation lies in the
eventual closure. -/
theorem IsProof.mem_Vinf {Γ : Set (MvPolynomial σ K)} {d : ℕ} {l : List (MvPolynomial σ K)}
    (hp : IsProof Γ l) (hb : DegBounded d l) : ∀ g ∈ l, g ∈ Vinf Γ d := by
  induction hp with
  | nil => intro g hg; cases hg
  | @ax l f _ hf ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · apply (le_iSup (V Γ d) 0 : V Γ d 0 ≤ Vinf Γ d)
      exact Submodule.subset_span ⟨hf, hb _ (by simp)⟩
    · exact ih (fun g hg => hb g (List.mem_cons_of_mem _ hg)) g hg'
  | @lin l f _ hf ih =>
    have ih' := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact (Submodule.span_le.mpr (fun g hg => ih' g hg)) hf
    · exact ih' g hg'
  | @mulX l g₀ i _ hg₀ ih =>
    have ih' := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · by_cases hz : g₀ = 0
      · subst hz
        simp
      · obtain ⟨j, hj⟩ := mem_Vinf_iff.mp (ih' g₀ hg₀)
        have hdeg : (X i * g₀).totalDegree ≤ d := hb _ (by simp)
        have hlow := mem_lowDeg_of_X_mul i hz hdeg
        apply (le_iSup (V Γ d) (j + 1) : V Γ d (j + 1) ≤ Vinf Γ d)
        apply (le_sup_right : mulStep (V Γ d j ⊓ lowDeg σ K d) ≤ step d (V Γ d j))
        exact Submodule.subset_span ⟨i, g₀, ⟨hj, hlow⟩, rfl⟩
    · exact ih' g hg'

/-- **Closure = consequences.**  `f` has an ordinary degree-`≤ d` PC derivation from `Γ`
iff `f` lies in the eventual closure. -/
theorem derives_iff_mem_Vinf {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K} :
    Derives Γ d f ↔ f ∈ Vinf Γ d := by
  constructor
  · rintro ⟨l, hp, hb, hm⟩
    exact hp.mem_Vinf hb f hm
  · intro h
    exact Vinf_le_derivable Γ d h

theorem derivable_eq_Vinf (Γ : Set (MvPolynomial σ K)) (d : ℕ) : derivable Γ d = Vinf Γ d := by
  ext f
  exact derives_iff_mem_Vinf

/-- Prompt 04, item 4: `1 ∈ V∞` iff there is an actual degree-`≤ d` PC refutation. -/
theorem refutes_iff_one_mem_Vinf {Γ : Set (MvPolynomial σ K)} {d : ℕ} :
    Refutes Γ d ↔ (1 : MvPolynomial σ K) ∈ Vinf Γ d :=
  derives_iff_mem_Vinf

/-! ### Stabilisation -/

/-- Prompt 04, item 3 (second part): once a stage repeats, the chain is frozen. -/
theorem V_frozen {Γ : Set (MvPolynomial σ K)} {d j : ℕ} (h : V Γ d (j + 1) = V Γ d j) :
    ∀ k, V Γ d (j + k) = V Γ d j := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have : V Γ d (j + (k + 1)) = step d (V Γ d (j + k)) := rfl
    rw [this, ih]
    exact h

theorem Vinf_eq_of_frozen {Γ : Set (MvPolynomial σ K)} {d j : ℕ}
    (h : V Γ d (j + 1) = V Γ d j) : Vinf Γ d = V Γ d j := by
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hk : k ≤ j
    · exact V_mono Γ d hk
    · obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
      rw [V_frozen h m]
  · exact le_iSup (V Γ d) j

/-- Prompt 04, item 3 (third part): for finitely many variables the chain stabilises,
because every stage lies in the finite-dimensional space `P_{≤ d}`. -/
theorem exists_stable [Finite σ] (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    ∃ j, V Γ d (j + 1) = V Γ d j ∧ Vinf Γ d = V Γ d j := by
  set W := restrictTotalDegree σ K d with hW
  have hfin : Module.Finite K W := inferInstance
  have hNoeth : IsNoetherian K W := (IsNoetherian.iff_fg (K := K) (V := W)).mpr hfin
  let f : ℕ →o Submodule K W :=
    ⟨fun j => (V Γ d j).comap W.subtype, fun a b hab => Submodule.comap_mono (V_mono Γ d hab)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr hNoeth f
  have hback : ∀ j, V Γ d j = ((V Γ d j).comap W.subtype).map W.subtype := by
    intro j
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (V_le_W Γ d j)]
  have hstep : V Γ d (n + 1) = V Γ d n := by
    rw [hback (n + 1), hback n]
    exact congrArg _ (hn (n + 1) (by omega)).symm
  exact ⟨n, hstep, Vinf_eq_of_frozen hstep⟩

/-- A stage beyond the stabilisation index of two different chains (e.g. two ranks):
the two chains need not stabilise at the same index, but a common later index exists. -/
theorem exists_common_stable {σ' : Type*} [Finite σ] [Finite σ']
    (Γ : Set (MvPolynomial σ K)) (Γ' : Set (MvPolynomial σ' K)) (d : ℕ) :
    ∃ j, Vinf Γ d = V Γ d j ∧ Vinf Γ' d = V Γ' d j := by
  obtain ⟨j₁, h₁, _⟩ := exists_stable Γ d
  obtain ⟨j₂, h₂, _⟩ := exists_stable Γ' d
  refine ⟨max j₁ j₂, ?_, ?_⟩
  · obtain ⟨m, hm⟩ : ∃ m, max j₁ j₂ = j₁ + m := ⟨max j₁ j₂ - j₁, by omega⟩
    rw [hm, V_frozen h₁ m, Vinf_eq_of_frozen h₁]
  · obtain ⟨m, hm⟩ : ∃ m, max j₁ j₂ = j₂ + m := ⟨max j₁ j₂ - j₂, by omega⟩
    rw [hm, V_frozen h₂ m, Vinf_eq_of_frozen h₂]

/-- With finitely many variables: a refutation exists iff `1` lies in a stabilised stage. -/
theorem refutes_iff_one_mem_stage [Finite σ] (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    ∃ j, V Γ d (j + 1) = V Γ d j ∧ (Refutes Γ d ↔ (1 : MvPolynomial σ K) ∈ V Γ d j) := by
  obtain ⟨j, hj, hinf⟩ := exists_stable Γ d
  exact ⟨j, hj, by rw [refutes_iff_one_mem_Vinf, hinf]⟩

/-! ### Degree zero -/

/-- At `d = 0` nothing can be multiplied: the closure is just the span of the constant
axioms (and `0`). -/
theorem Vinf_zero (Γ : Set (MvPolynomial σ K)) : Vinf Γ 0 = V0 Γ 0 := by
  have h : V Γ 0 (0 + 1) = V Γ 0 0 := by
    show step 0 (V0 Γ 0) = V0 Γ 0
    unfold step mulStep lowDeg
    rw [if_pos rfl, inf_bot_eq]
    apply le_antisymm
    · apply sup_le (le_refl _)
      apply Submodule.span_le.mpr
      rintro _ ⟨i, f, hf, rfl⟩
      rw [Submodule.mem_bot] at hf
      subst hf
      simp
    · exact le_sup_left
  exact Vinf_eq_of_frozen h

/-! ### Minimum refutation degree -/

open Classical in
/-- The minimum PC refutation degree, `⊤` when there is no refutation of any degree. -/
def pcDegree (Γ : Set (MvPolynomial σ K)) : ℕ∞ :=
  if h : ∃ d, Refutes Γ d then ((Nat.find h : ℕ) : ℕ∞) else ⊤

theorem pcDegree_le_iff (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    pcDegree Γ ≤ (d : ℕ∞) ↔ Refutes Γ d := by
  classical
  unfold pcDegree
  split
  · rename_i h
    rw [Nat.cast_le]
    constructor
    · intro hle
      exact Derives.mono hle (Nat.find_spec h)
    · intro hd
      exact Nat.find_min' h hd
  · rename_i h
    simp only [top_le_iff, ENat.coe_ne_top, false_iff]
    intro hd
    exact h ⟨d, hd⟩

end

end DegreeProfilesReview.PC
