/-
Claude, 27 Sep 2026.  Undecidability, part E0: tools for the concrete witnesses and the types.

* `atomVal_congr`, `clause_mem`: every grounding of a clause (any `ν : ℕ → Fin n`) is an axiom.
* `inst_cases`: every axiom of the translation is a totality sum, a collision, a Boolean axiom or a
  clause grounding.
* `conj_WF`: conjunction preserves well-formedness.
* `NSType T τ`, `PCType T τ` (`τ = 1, 2, 3, 4`): the four types of the actual NS and ordinary-PC
  profiles, relative to the linear onset `onset T.k T.s T.n0` of `LinearFinal` (for which every
  template's profiles are periodic in every prime characteristic).
* `nsType_iff_intrinsic`: for these periodic profiles the types are intrinsic: T2–T4 are read off
  from the set `Rec h` of values taken at arbitrarily large sizes.  Hence profiles that agree at
  every `n ≥ 1` have the same type (`nsType_congr`).
* `pcType_iff_nsType`: the ordinary-PC and NS types coincide (the comparison of `CompLinear`).
-/
import UHerbrand
import CompLinear

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open MvPolynomial DegreeProfilesReview.NS DegreeProfilesReview.Uniform
open DegreeProfilesReview.Profiles

/-! ### Groundings are axioms -/

section Congr
variable (φ : Sentence) (K : Type) [Field K] {n : ℕ}

theorem atomVal_congr {ν ν' : ℕ → Fin n} (a : Atom) (h : ∀ v ∈ a.vars, ν v = ν' v) :
    atomVal (K := K) φ (rvN φ n) (gvN φ n) ν a = atomVal φ (rvN φ n) (gvN φ n) ν' a := by
  classical
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · simp only [atomVal]
    split_ifs with hc
    · have ha : φ.rels.get ⟨R, hc.1⟩ = args.length := by
        have h2 := hc.2
        rw [List.getD_eq_getElem _ _ hc.1] at h2
        rw [List.get_eq_getElem]; exact h2.symm
      congr 2
      funext k
      have hk : k.val < args.length := by have := k.2; omega
      simp only [tupleOf]
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk)]
      simp only [List.getElem_map]
      exact h _ (List.getElem_mem hk)
    · rfl
  · simp only [atomVal]
    split_ifs with hc
    · have ha : φ.funs.get ⟨f, hc.1⟩ = args.length := by
        have h2 := hc.2
        rw [List.getD_eq_getElem _ _ hc.1] at h2
        rw [List.get_eq_getElem]; exact h2.symm
      have ho : ν out = ν' out := h out List.mem_cons_self
      rw [ho]
      congr 2
      funext k
      have hk : k.val < args.length := by have := k.2; omega
      simp only [tupleOf]
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk)]
      simp only [List.getElem_map]
      exact h _ (List.mem_cons_of_mem _ (List.getElem_mem hk))
    · rfl
  · have ei : ν i = ν' i := h i (by simp [Atom.vars])
    have ej : ν j = ν' j := h j (by simp [Atom.vars])
    simp only [atomVal]
    by_cases hh : ν i = ν j
    · rw [if_pos hh, if_pos (by rw [← ei, ← ej]; exact hh)]
    · rw [if_neg hh, if_neg (by rw [← ei, ← ej]; exact hh)]

theorem clausePoly_congr_vars {ν ν' : ℕ → Fin n} (c : Clause)
    (h : ∀ l ∈ c, ∀ v ∈ l.2.vars, ν v = ν' v) :
    clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c = clausePoly φ (rvN φ n) (gvN φ n) ν' c := by
  unfold clausePoly
  congr 1
  apply List.map_congr_left
  intro l hl
  unfold litFactor
  rw [atomVal_congr φ K l.2 (h l hl)]

/-- Every grounding of every clause is an axiom of the translation. -/
theorem clause_mem {c : Clause} (hc : c ∈ φ.clauses) (ν : ℕ → Fin n) :
    clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c ∈ (template φ K).inst n := by
  obtain ⟨ci, rfl⟩ := List.get_of_mem hc
  let σ' : Fin (nvars (φ.clauses.get ci)) → Fin n := fun v => ν v.val
  rw [← clausePoly_congr_vars φ K (ν := νOf (nvars_pos _) σ') _ (fun l hl v hv => by
    simp only [νOf, dif_pos (var_lt_nvars hl hv), σ'])]
  exact ⟨_, poly_clause φ K n ci σ'⟩

/-- The four kinds of axioms. -/
theorem inst_cases {g : MvPolynomial ((VarSys φ).Rk n) K} (hg : g ∈ (template φ K).inst n) :
    (∃ (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n),
      g = (∑ j : Fin n, X (gvN φ n f t j)) - 1) ∨
    (∃ (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j j' : Fin n), j ≠ j' ∧
      g = X (gvN φ n f t j) * X (gvN φ n f t j')) ∨
    (∃ v, g = X v ^ 2 - X v) ∨
    (∃ c ∈ φ.clauses, ∃ ν : ℕ → Fin n, g = clausePoly φ (rvN φ n) (gvN φ n) ν c) := by
  obtain ⟨⟨i, u⟩, rfl⟩ := hg
  rcases i with f | f | _ | ci
  · exact Or.inl ⟨f, u, poly_tot φ K n f u⟩
  · refine Or.inr (Or.inl ⟨f, collIn u.1, collOut1 u.1, collOut2 u.1, ?_, poly_coll φ K n f u⟩)
    intro h
    apply u.2
    simp only [collOut1, collOut2] at h
    show (u.1 _).val = (u.1 _).val
    rw [h]
  · exact Or.inr (Or.inr (Or.inl ⟨u, poly_bool φ K n u⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, List.get_mem _ _, _, poly_clause φ K n ci u⟩))

end Congr

/-! ### Conjunction preserves well-formedness -/

theorem conj_WF {φ ψ : Sentence} (hφ : WF φ) (hψ : WF ψ) : WF (conj φ ψ) := by
  intro c hc l hl
  rw [conj_clauses, List.mem_append] at hc
  rcases hc with hc | hc
  · have h := hφ c hc l hl
    obtain ⟨s, a⟩ := l
    rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
    · obtain ⟨h1, h2⟩ := h
      exact ⟨by rw [conj_rels_length]; omega, by rw [getD_conj_rels_left φ ψ h1]; exact h2⟩
    · obtain ⟨h1, h2⟩ := h
      exact ⟨by rw [conj_funs_length]; omega, by rw [getD_conj_funs_left φ ψ h1]; exact h2⟩
    · trivial
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    have h := hψ c' hc' l' hl'
    obtain ⟨s, a⟩ := l'
    rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
    · obtain ⟨h1, h2⟩ := h
      show AtomWF (conj φ ψ) (Sum.inl (φ.rels.length + R, args))
      exact ⟨by rw [conj_rels_length]; omega, by rw [getD_conj_rels_right φ ψ R]; exact h2⟩
    · obtain ⟨h1, h2⟩ := h
      show AtomWF (conj φ ψ) (Sum.inr (Sum.inl ((φ.funs.length + f, args), out)))
      exact ⟨by rw [conj_funs_length]; omega, by rw [getD_conj_funs_right φ ψ f]; exact h2⟩
    · trivial

/-! ### The four types -/

section Types
variable {K : Type} [Field K]

/-- The values taken at arbitrarily large sizes. -/
def Rec (h : ℕ → ℕ∞) : Set ℕ := {d | ∀ M, ∃ n, M ≤ n ∧ h n = (d : ℕ∞)}

/-- The intrinsic form of the four types. -/
def IType (h : ℕ → ℕ∞) : ℕ → Prop
  | 1 => EventuallyBounded h
  | 2 => Rec h = ∅
  | 3 => (Rec h).Finite ∧ (Rec h).Nonempty ∧ ¬ EventuallyBounded h
  | 4 => (Rec h).Infinite
  | _ => False

/-- The type of the actual NS profile of a template, relative to its linear onset. -/
def NSType (T : Template K) : ℕ → Prop
  | 1 => IsT1 T.nsProfile
  | 2 => IsT2 T.nsProfile (onset T.k T.s T.n0)
  | 3 => IsT3 T.nsProfile (onset T.k T.s T.n0)
  | 4 => IsT4 T.nsProfile (onset T.k T.s T.n0)
  | _ => False

/-- The type of the actual ordinary-PC profile of a template, relative to its linear onset. -/
def PCType (T : Template K) : ℕ → Prop
  | 1 => IsT1 T.pcProfile
  | 2 => IsT2 T.pcProfile (onset T.k T.s T.n0)
  | 3 => IsT3 T.pcProfile (onset T.k T.s T.n0)
  | 4 => IsT4 T.pcProfile (onset T.k T.s T.n0)
  | _ => False

theorem E_eq_Rec {h : ℕ → ℕ∞} {N Q : ℕ → ℕ} (P : PeriodicProfile h N Q) : E h N = Rec h :=
  Set.ext fun d => P.mem_E_iff d

theorem type_iff_intrinsic {h : ℕ → ℕ∞} {N Q : ℕ → ℕ} (P : PeriodicProfile h N Q) (τ : ℕ) :
    (match τ with
      | 1 => IsT1 h | 2 => IsT2 h N | 3 => IsT3 h N | 4 => IsT4 h N | _ => False) ↔
      IType h τ := by
  rcases τ with _ | _ | _ | _ | _ | τ
  · exact Iff.rfl
  · exact Iff.rfl
  · show E h N = ∅ ↔ Rec h = ∅; rw [E_eq_Rec P]
  · show (E h N).Finite ∧ (E h N).Nonempty ∧ _ ↔ _; rw [E_eq_Rec P]; rfl
  · show (E h N).Infinite ↔ (Rec h).Infinite; rw [E_eq_Rec P]
  · exact Iff.rfl

variable (p : ℕ) [Fact p.Prime] [CharP K p]
include p

theorem nsType_iff_intrinsic (T : Template K) (τ : ℕ) : NSType T τ ↔ IType T.nsProfile τ := by
  have := type_iff_intrinsic (ClaudeComparison.periodic_linear_ns p T) τ
  rcases τ with _ | _ | _ | _ | _ | τ <;> exact this

theorem pcType_iff_intrinsic (T : Template K) (τ : ℕ) : PCType T τ ↔ IType T.pcProfile τ := by
  have := type_iff_intrinsic (ClaudeComparison.periodic_linear_pc p T) τ
  rcases τ with _ | _ | _ | _ | _ | τ <;> exact this

/-- **The ordinary-PC and NS types agree** (`CompLinear.types_agree_linear`). -/
theorem pcType_iff_nsType (T : Template K) (τ : ℕ) : PCType T τ ↔ NSType T τ := by
  obtain ⟨e1, e2, e3, e4⟩ := ClaudeComparison.types_agree_linear p T
  rcases τ with _ | _ | _ | _ | _ | τ
  · exact Iff.rfl
  · exact e1
  · exact e2
  · exact e3
  · exact e4
  · exact Iff.rfl

/-- Exactly one of the four types holds. -/
theorem nsType_unique (T : Template K) {τ τ' : ℕ} (h : NSType T τ) (h' : NSType T τ') : τ = τ' := by
  have hx := (ClaudeComparison.periodic_linear_ns p T).exactly_one
  rcases τ with _ | _ | _ | _ | _ | τ <;> rcases τ' with _ | _ | _ | _ | _ | τ' <;>
    first | rfl | exact h.elim | exact h'.elim | (simp only [NSType] at h h'; tauto)

theorem nsType_exists (T : Template K) : ∃ τ ∈ ({1, 2, 3, 4} : Set ℕ), NSType T τ := by
  rcases (ClaudeComparison.periodic_linear_ns p T).exactly_one with h | h | h | h
  · exact ⟨1, by simp, h.1⟩
  · exact ⟨2, by simp, h.2.1⟩
  · exact ⟨3, by simp, h.2.2.1⟩
  · exact ⟨4, by simp, h.2.2.2⟩

end Types

/-- Intrinsic types depend only on the profile at sizes `n ≥ 1`. -/
theorem iType_congr {h h' : ℕ → ℕ∞} (e : ∀ n, 1 ≤ n → h n = h' n) (τ : ℕ) :
    IType h τ ↔ IType h' τ := by
  have hrec : Rec h = Rec h' := by
    ext d
    constructor
    · intro hd M
      obtain ⟨n, hn, hv⟩ := hd (M + 1)
      exact ⟨n, by omega, by rw [← e n (by omega)]; exact hv⟩
    · intro hd M
      obtain ⟨n, hn, hv⟩ := hd (M + 1)
      exact ⟨n, by omega, by rw [e n (by omega)]; exact hv⟩
  have hb : EventuallyBounded h ↔ EventuallyBounded h' := by
    constructor
    · rintro ⟨B, M, hB⟩
      exact ⟨B, M + 1, fun n hn => by rw [← e n (by omega)]; exact hB n (by omega)⟩
    · rintro ⟨B, M, hB⟩
      exact ⟨B, M + 1, fun n hn => by rw [e n (by omega)]; exact hB n (by omega)⟩
  rcases τ with _ | _ | _ | _ | _ | τ
  · exact Iff.rfl
  · exact hb
  · show Rec h = ∅ ↔ Rec h' = ∅; rw [hrec]
  · show (Rec h).Finite ∧ (Rec h).Nonempty ∧ ¬ EventuallyBounded h ↔ _
    rw [hrec, hb]; rfl
  · show (Rec h).Infinite ↔ (Rec h').Infinite; rw [hrec]
  · exact Iff.rfl

end ClaudeUndec
