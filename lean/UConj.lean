/-
Claude, 27 Sep 2026.  Undecidability, part C1: conjunction in disjoint signatures, and the
satisfiable-block lemma (manuscript `lem:disjoint`).

`conj φ ψ` concatenates the signatures and the clause lists, shifting the symbols of `ψ`
(blockwise normalization with disjoint symbols).  For well-formed `φ, ψ` and every `n`:

* `conj_inst_left/right`: the axioms of `φ` and of `ψ` at size `n`, renamed injectively, are
  axioms of `conj φ ψ`; conversely every axiom of `conj φ ψ` arises in this way;
* `nsDegree_conj_le_left/right`: the conjunction is at least as easy as each block;
* `nsDegree_conj_eq_left`: if the translation of `ψ` at size `n` has a common root, the NS
  degree of the conjunction equals that of `φ` (substitute the root, `UNSTools`);
* `conj_root_right`: a common root of the conjunction restricts to one of `ψ`.
-/
import UFORoots
import UNSTools

set_option autoImplicit false
open MvPolynomial DegreeProfilesReview.Uniform DegreeProfilesReview.NS

namespace ClaudeUndec

/-! ### Well-formedness, shifting, conjunction -/

/-- A well-formed atom: symbol in range and argument list of the right length. -/
def AtomWF (φ : Sentence) : Atom → Prop
  | Sum.inl (R, args) => R < φ.rels.length ∧ args.length = φ.rels.getD R 0
  | Sum.inr (Sum.inl ((f, args), _)) => f < φ.funs.length ∧ args.length = φ.funs.getD f 0
  | Sum.inr (Sum.inr _) => True

def WF (φ : Sentence) : Prop := ∀ c ∈ φ.clauses, ∀ l ∈ c, AtomWF φ l.2

def Atom.shift (dR dF : ℕ) : Atom → Atom
  | Sum.inl (R, args) => Sum.inl (dR + R, args)
  | Sum.inr (Sum.inl ((f, args), out)) => Sum.inr (Sum.inl ((dF + f, args), out))
  | Sum.inr (Sum.inr p) => Sum.inr (Sum.inr p)

def Clause.shift (dR dF : ℕ) (c : Clause) : Clause := c.map fun l => (l.1, l.2.shift dR dF)

/-- Conjunction in disjoint signatures (the symbols of `ψ` are shifted). -/
def conj (φ ψ : Sentence) : Sentence :=
  ((φ.rels ++ ψ.rels, φ.funs ++ ψ.funs),
    φ.clauses ++ ψ.clauses.map (Clause.shift φ.rels.length φ.funs.length))

theorem nvars_shift (dR dF : ℕ) (c : Clause) : nvars (Clause.shift dR dF c) = nvars c := by
  unfold nvars Clause.shift
  congr 2
  rw [List.flatMap_map]
  congr 1
  funext l
  rcases l with ⟨b, ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩⟩ <;> rfl

/-! ### Symbol and variable maps -/

section Maps
variable (φ ψ : Sentence)

theorem conj_rels : (conj φ ψ).rels = φ.rels ++ ψ.rels := rfl
theorem conj_funs : (conj φ ψ).funs = φ.funs ++ ψ.funs := rfl
theorem conj_clauses : (conj φ ψ).clauses =
    φ.clauses ++ ψ.clauses.map (Clause.shift φ.rels.length φ.funs.length) := rfl

theorem conj_rels_length : (conj φ ψ).rels.length = φ.rels.length + ψ.rels.length := by
  rw [conj_rels, List.length_append]
theorem conj_funs_length : (conj φ ψ).funs.length = φ.funs.length + ψ.funs.length := by
  rw [conj_funs, List.length_append]

def cR (R : Fin φ.rels.length) : Fin (conj φ ψ).rels.length :=
  ⟨R.1, by rw [conj_rels_length]; omega⟩
def dR (R : Fin ψ.rels.length) : Fin (conj φ ψ).rels.length :=
  ⟨φ.rels.length + R.1, by rw [conj_rels_length]; omega⟩
def cF (f : Fin φ.funs.length) : Fin (conj φ ψ).funs.length :=
  ⟨f.1, by rw [conj_funs_length]; omega⟩
def dF (f : Fin ψ.funs.length) : Fin (conj φ ψ).funs.length :=
  ⟨φ.funs.length + f.1, by rw [conj_funs_length]; omega⟩

theorem ar_cR (R : Fin φ.rels.length) : (conj φ ψ).rels.get (cR φ ψ R) = φ.rels.get R := by
  simp only [List.get_eq_getElem, cR, conj_rels, List.getElem_append_left R.2]
theorem ar_dR (R : Fin ψ.rels.length) : (conj φ ψ).rels.get (dR φ ψ R) = ψ.rels.get R := by
  simp only [List.get_eq_getElem, dR, conj_rels]
  rw [List.getElem_append_right (by omega)]
  congr 1; omega
theorem ar_cF (f : Fin φ.funs.length) : (conj φ ψ).funs.get (cF φ ψ f) = φ.funs.get f := by
  simp only [List.get_eq_getElem, cF, conj_funs, List.getElem_append_left f.2]
theorem ar_dF (f : Fin ψ.funs.length) : (conj φ ψ).funs.get (dF φ ψ f) = ψ.funs.get f := by
  simp only [List.get_eq_getElem, dF, conj_funs]
  rw [List.getElem_append_right (by omega)]
  congr 1; omega

variable (n : ℕ)

/-- The variables of `φ` inside the conjunction. -/
def ιL : (VarSys φ).Rk n → (VarSys (conj φ ψ)).Rk n
  | ⟨Sum.inl R, t⟩ => ⟨Sum.inl (cR φ ψ R), fun i => t (Fin.cast (ar_cR φ ψ R) i)⟩
  | ⟨Sum.inr f, t⟩ => ⟨Sum.inr (cF φ ψ f), fun i =>
      t (Fin.cast (show (conj φ ψ).funs.get (cF φ ψ f) + 1 = φ.funs.get f + 1 by rw [ar_cF]) i)⟩

/-- The variables of `ψ` inside the conjunction. -/
def ιR : (VarSys ψ).Rk n → (VarSys (conj φ ψ)).Rk n
  | ⟨Sum.inl R, t⟩ => ⟨Sum.inl (dR φ ψ R), fun i => t (Fin.cast (ar_dR φ ψ R) i)⟩
  | ⟨Sum.inr f, t⟩ => ⟨Sum.inr (dF φ ψ f), fun i =>
      t (Fin.cast (show (conj φ ψ).funs.get (dF φ ψ f) + 1 = ψ.funs.get f + 1 by rw [ar_dF]) i)⟩

theorem snoc_cast {m m' : ℕ} (h : m' = m) (t : Fin m → Fin n) (j : Fin n) (i : Fin (m' + 1)) :
    Fin.snoc (α := fun _ => Fin n) t j (Fin.cast (by rw [h]) i) =
      Fin.snoc (α := fun _ => Fin n) (fun k => t (Fin.cast h k)) j i := by
  subst h
  rfl

theorem ιL_rvN (R : Fin φ.rels.length) (t : Fin (φ.rels.get R) → Fin n) :
    ιL φ ψ n (rvN φ n R t) = rvN (conj φ ψ) n (cR φ ψ R) (fun i => t (Fin.cast (ar_cR φ ψ R) i)) :=
  rfl

theorem ιR_rvN (R : Fin ψ.rels.length) (t : Fin (ψ.rels.get R) → Fin n) :
    ιR φ ψ n (rvN ψ n R t) = rvN (conj φ ψ) n (dR φ ψ R) (fun i => t (Fin.cast (ar_dR φ ψ R) i)) :=
  rfl

theorem ιL_gvN (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j : Fin n) :
    ιL φ ψ n (gvN φ n f t j) =
      gvN (conj φ ψ) n (cF φ ψ f) (fun i => t (Fin.cast (ar_cF φ ψ f) i)) j := by
  show (⟨Sum.inr (cF φ ψ f), _⟩ : (VarSys (conj φ ψ)).Rk n) = ⟨Sum.inr (cF φ ψ f), _⟩
  congr 1
  funext i
  exact snoc_cast n (ar_cF φ ψ f) t j i

theorem ιR_gvN (f : Fin ψ.funs.length) (t : Fin (ψ.funs.get f) → Fin n) (j : Fin n) :
    ιR φ ψ n (gvN ψ n f t j) =
      gvN (conj φ ψ) n (dF φ ψ f) (fun i => t (Fin.cast (ar_dF φ ψ f) i)) j := by
  show (⟨Sum.inr (dF φ ψ f), _⟩ : (VarSys (conj φ ψ)).Rk n) = ⟨Sum.inr (dF φ ψ f), _⟩
  congr 1
  funext i
  exact snoc_cast n (ar_dF φ ψ f) t j i

/-! ### Clause polynomials of the two blocks -/

section Clauses
variable {K : Type} [Field K]

theorem getD_conj_rels_left {R : ℕ} (h : R < φ.rels.length) :
    (conj φ ψ).rels.getD R 0 = φ.rels.getD R 0 := by
  rw [conj_rels, List.getD_append _ _ _ _ h]

theorem getD_conj_rels_right (R : ℕ) :
    (conj φ ψ).rels.getD (φ.rels.length + R) 0 = ψ.rels.getD R 0 := by
  rw [conj_rels, List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

theorem getD_conj_funs_left {f : ℕ} (h : f < φ.funs.length) :
    (conj φ ψ).funs.getD f 0 = φ.funs.getD f 0 := by
  rw [conj_funs, List.getD_append _ _ _ _ h]

theorem getD_conj_funs_right (f : ℕ) :
    (conj φ ψ).funs.getD (φ.funs.length + f) 0 = ψ.funs.getD f 0 := by
  rw [conj_funs, List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

theorem atomVal_left (ν : ℕ → Fin n) (a : Atom) (ha : AtomWF φ a) :
    rename (ιL φ ψ n) (atomVal φ (rvN φ n) (gvN φ n) ν a : MvPolynomial _ K) =
      atomVal (conj φ ψ) (rvN (conj φ ψ) n) (gvN (conj φ ψ) n) ν a := by
  classical
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · obtain ⟨hR, hl⟩ := ha
    have hR' : R < (conj φ ψ).rels.length := by rw [conj_rels_length]; omega
    have hl' : args.length = (conj φ ψ).rels.getD R 0 := by rw [getD_conj_rels_left φ ψ hR]; exact hl
    simp only [atomVal, dif_pos (And.intro hR hl), dif_pos (And.intro hR' hl'), rename_X]
    rfl
  · obtain ⟨hf, hl⟩ := ha
    have hf' : f < (conj φ ψ).funs.length := by rw [conj_funs_length]; omega
    have hl' : args.length = (conj φ ψ).funs.getD f 0 := by rw [getD_conj_funs_left φ ψ hf]; exact hl
    simp only [atomVal, dif_pos (And.intro hf hl), dif_pos (And.intro hf' hl'), rename_X]
    rw [ιL_gvN]
    rfl
  · simp only [atomVal]
    split_ifs <;> simp

theorem atomVal_right (ν : ℕ → Fin n) (a : Atom) (ha : AtomWF ψ a) :
    rename (ιR φ ψ n) (atomVal ψ (rvN ψ n) (gvN ψ n) ν a : MvPolynomial _ K) =
      atomVal (conj φ ψ) (rvN (conj φ ψ) n) (gvN (conj φ ψ) n) ν
        (a.shift φ.rels.length φ.funs.length) := by
  classical
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · obtain ⟨hR, hl⟩ := ha
    have hR' : φ.rels.length + R < (conj φ ψ).rels.length := by rw [conj_rels_length]; omega
    have hl' : args.length = (conj φ ψ).rels.getD (φ.rels.length + R) 0 := by
      rw [getD_conj_rels_right]; exact hl
    simp only [Atom.shift, atomVal, dif_pos (And.intro hR hl), dif_pos (And.intro hR' hl'),
      rename_X]
    rfl
  · obtain ⟨hf, hl⟩ := ha
    have hf' : φ.funs.length + f < (conj φ ψ).funs.length := by rw [conj_funs_length]; omega
    have hl' : args.length = (conj φ ψ).funs.getD (φ.funs.length + f) 0 := by
      rw [getD_conj_funs_right]; exact hl
    simp only [Atom.shift, atomVal, dif_pos (And.intro hf hl), dif_pos (And.intro hf' hl'),
      rename_X]
    rw [ιR_gvN]
    rfl
  · simp only [Atom.shift, atomVal]
    split_ifs <;> simp

theorem clausePoly_left (ν : ℕ → Fin n) (c : Clause) (hc : ∀ l ∈ c, AtomWF φ l.2) :
    rename (ιL φ ψ n) (clausePoly φ (rvN φ n) (gvN φ n) ν c : MvPolynomial _ K) =
      clausePoly (conj φ ψ) (rvN (conj φ ψ) n) (gvN (conj φ ψ) n) ν c := by
  unfold clausePoly
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply, litFactor]
  split_ifs
  · rw [map_sub, map_one, atomVal_left φ ψ n ν l.2 (hc l hl)]
  · rw [atomVal_left φ ψ n ν l.2 (hc l hl)]

theorem clausePoly_right (ν : ℕ → Fin n) (c : Clause) (hc : ∀ l ∈ c, AtomWF ψ l.2) :
    rename (ιR φ ψ n) (clausePoly ψ (rvN ψ n) (gvN ψ n) ν c : MvPolynomial _ K) =
      clausePoly (conj φ ψ) (rvN (conj φ ψ) n) (gvN (conj φ ψ) n) ν
        (Clause.shift φ.rels.length φ.funs.length c) := by
  unfold clausePoly Clause.shift
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply, litFactor]
  split_ifs
  · rw [map_sub, map_one, atomVal_right φ ψ n ν l.2 (hc l hl)]
  · rw [atomVal_right φ ψ n ν l.2 (hc l hl)]

theorem clausePoly_congr {φ' : Sentence} {L V : Type}
    (rv : (R : Fin φ'.rels.length) → (Fin (φ'.rels.get R) → L) → V)
    (gv : (f : Fin φ'.funs.length) → (Fin (φ'.funs.get f) → L) → L → V)
    {c c' : Clause} (h : c' = c) (σ : Fin (nvars c) → L) :
    (clausePoly φ' rv gv (νOf (nvars_pos c') (fun k => σ (Fin.cast (by rw [h]) k))) c' :
      MvPolynomial V K) = clausePoly φ' rv gv (νOf (nvars_pos c) σ) c := by
  subst h; rfl

/-! ### The axioms of the conjunction -/

theorem conj_clauses_length :
    (conj φ ψ).clauses.length = φ.clauses.length + ψ.clauses.length := by
  rw [conj_clauses, List.length_append, List.length_map]

def cC (ci : Fin φ.clauses.length) : Fin (conj φ ψ).clauses.length :=
  ⟨ci.1, by rw [conj_clauses_length]; omega⟩
def dC (ci : Fin ψ.clauses.length) : Fin (conj φ ψ).clauses.length :=
  ⟨φ.clauses.length + ci.1, by rw [conj_clauses_length]; omega⟩

theorem conj_clause_left (ci : Fin φ.clauses.length) :
    (conj φ ψ).clauses.get (cC φ ψ ci) = φ.clauses.get ci := by
  simp only [List.get_eq_getElem, cC, conj_clauses, List.getElem_append_left ci.2]

theorem conj_clause_right (ci : Fin ψ.clauses.length) :
    (conj φ ψ).clauses.get (dC φ ψ ci) =
      Clause.shift φ.rels.length φ.funs.length (ψ.clauses.get ci) := by
  simp only [dC]
  simp only [List.get_eq_getElem, conj_clauses]
  rw [List.getElem_append_right (by omega)]
  simp only [List.getElem_map]
  congr 2; omega

theorem coll_index_eq {a a' : ℕ} (h : a' = a) :
    (Fin.cast (by rw [h]) (⟨a', by omega⟩ : Fin (a' + 2)) : Fin (a + 2)) = ⟨a, by omega⟩ ∧
    (Fin.cast (by rw [h]) (⟨a' + 1, by omega⟩ : Fin (a' + 2)) : Fin (a + 2)) = ⟨a + 1, by omega⟩ := by
  subst h; exact ⟨rfl, rfl⟩

/-- Axioms of `φ`, renamed, are axioms of the conjunction. -/
theorem inst_left (hφ : WF φ) {f : MvPolynomial ((VarSys φ).Rk n) K}
    (hf : f ∈ (template φ K).inst n) : rename (ιL φ ψ n) f ∈ (template (conj φ ψ) K).inst n := by
  obtain ⟨⟨i, u⟩, rfl⟩ := hf
  rcases i with g | g | ⟨⟩ | ci
  · refine ⟨⟨Sum.inl (cF φ ψ g), fun k => u (Fin.cast (ar_cF φ ψ g) k)⟩, ?_⟩
    rw [poly_tot, poly_tot, map_sub, map_sum, map_one]
    simp only [rename_X, ιL_gvN]
  · have ha := ar_cF φ ψ g
    obtain ⟨e1, e2⟩ := coll_index_eq ha
    let b : Fin ((conj φ ψ).funs.get (cF φ ψ g) + 2) → Fin n := fun k => u.1 (Fin.cast (by rw [ha]) k)
    have hb : (b ⟨(conj φ ψ).funs.get (cF φ ψ g), by omega⟩).val ≠
        (b ⟨(conj φ ψ).funs.get (cF φ ψ g) + 1, by omega⟩).val := by
      simp only [b, e1, e2]; exact u.2
    refine ⟨⟨Sum.inr (Sum.inl (cF φ ψ g)), ⟨b, hb⟩⟩, ?_⟩
    rw [poly_coll, poly_coll, map_mul, rename_X, rename_X, ιL_gvN, ιL_gvN]
    simp only [collOut1, collOut2, b, e1, e2]
    rfl
  · refine ⟨⟨Sum.inr (Sum.inr (Sum.inl ())), ιL φ ψ n u⟩, ?_⟩
    rw [poly_bool, poly_bool, map_sub, map_pow, rename_X]
  · have hcl := conj_clause_left φ ψ ci
    refine ⟨⟨Sum.inr (Sum.inr (Sum.inr (cC φ ψ ci))), fun k => u (Fin.cast (by rw [hcl]) k)⟩, ?_⟩
    rw [poly_clause, poly_clause, clausePoly_left φ ψ n _ _ (hφ _ (List.get_mem _ ci))]
    exact clausePoly_congr _ _ hcl u

/-- Axioms of `ψ`, renamed, are axioms of the conjunction. -/
theorem inst_right (hψ : WF ψ) {f : MvPolynomial ((VarSys ψ).Rk n) K}
    (hf : f ∈ (template ψ K).inst n) : rename (ιR φ ψ n) f ∈ (template (conj φ ψ) K).inst n := by
  obtain ⟨⟨i, u⟩, rfl⟩ := hf
  rcases i with g | g | ⟨⟩ | ci
  · refine ⟨⟨Sum.inl (dF φ ψ g), fun k => u (Fin.cast (ar_dF φ ψ g) k)⟩, ?_⟩
    rw [poly_tot, poly_tot, map_sub, map_sum, map_one]
    simp only [rename_X, ιR_gvN]
  · have ha := ar_dF φ ψ g
    obtain ⟨e1, e2⟩ := coll_index_eq ha
    let b : Fin ((conj φ ψ).funs.get (dF φ ψ g) + 2) → Fin n := fun k => u.1 (Fin.cast (by rw [ha]) k)
    have hb : (b ⟨(conj φ ψ).funs.get (dF φ ψ g), by omega⟩).val ≠
        (b ⟨(conj φ ψ).funs.get (dF φ ψ g) + 1, by omega⟩).val := by
      simp only [b, e1, e2]; exact u.2
    refine ⟨⟨Sum.inr (Sum.inl (dF φ ψ g)), ⟨b, hb⟩⟩, ?_⟩
    rw [poly_coll, poly_coll, map_mul, rename_X, rename_X, ιR_gvN, ιR_gvN]
    simp only [collOut1, collOut2, b, e1, e2]
    rfl
  · refine ⟨⟨Sum.inr (Sum.inr (Sum.inl ())), ιR φ ψ n u⟩, ?_⟩
    rw [poly_bool, poly_bool, map_sub, map_pow, rename_X]
  · have hcl := conj_clause_right φ ψ ci
    have hnv : nvars (Clause.shift φ.rels.length φ.funs.length (ψ.clauses.get ci)) =
        nvars (ψ.clauses.get ci) := nvars_shift _ _ _
    refine ⟨⟨Sum.inr (Sum.inr (Sum.inr (dC φ ψ ci))),
      fun k => u (Fin.cast (by rw [hcl, hnv]) k)⟩, ?_⟩
    rw [poly_clause, poly_clause, clausePoly_right φ ψ n _ _ (hψ _ (List.get_mem _ ci))]
    have e := clausePoly_congr (K := K) (rvN (conj φ ψ) n) (gvN (conj φ ψ) n) hcl
      (fun k => u (Fin.cast hnv k))
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · congr 1
      funext x
      simp only [νOf]
      by_cases hx : x < nvars (ψ.clauses.get ci)
      · rw [dif_pos (by rw [hnv]; exact hx), dif_pos hx]; rfl
      · rw [dif_neg (by rw [hnv]; exact hx), dif_neg hx]; rfl

/-- Every axiom of the conjunction comes from one of the blocks. -/
theorem inst_conj (hφ : WF φ) (hψ : WF ψ) (i : (AxSys (conj φ ψ)).Rk n) :
    (∃ f ∈ (template φ K).inst n, (template (conj φ ψ) K).poly n i = rename (ιL φ ψ n) f) ∨
    (∃ g ∈ (template ψ K).inst n, (template (conj φ ψ) K).poly n i = rename (ιR φ ψ n) g) := by
  obtain ⟨i, u⟩ := i
  rcases i with g | g | ⟨⟩ | ci
  · by_cases hg : g.1 < φ.funs.length
    · obtain ⟨g, rfl⟩ : ∃ g', g = cF φ ψ g' := ⟨⟨g.1, hg⟩, rfl⟩
      refine Or.inl ⟨_, ⟨⟨Sum.inl g, fun k => u (Fin.cast (ar_cF φ ψ g).symm k)⟩, rfl⟩, ?_⟩
      rw [poly_tot, poly_tot, map_sub, map_sum, map_one]
      simp only [rename_X, ιL_gvN]
      rfl
    · obtain ⟨g, rfl⟩ : ∃ g', g = dF φ ψ g' :=
        ⟨⟨g.1 - φ.funs.length, by have := g.2; have := conj_funs_length φ ψ; omega⟩,
          Fin.ext (by simp only [dF]; omega)⟩
      refine Or.inr ⟨_, ⟨⟨Sum.inl g, fun k => u (Fin.cast (ar_dF φ ψ g).symm k)⟩, rfl⟩, ?_⟩
      rw [poly_tot, poly_tot, map_sub, map_sum, map_one]
      simp only [rename_X, ιR_gvN]
      rfl
  · by_cases hg : g.1 < φ.funs.length
    · obtain ⟨g, rfl⟩ : ∃ g', g = cF φ ψ g' := ⟨⟨g.1, hg⟩, rfl⟩
      have ha := ar_cF φ ψ g
      obtain ⟨e1, e2⟩ := coll_index_eq ha.symm
      let b : Fin (φ.funs.get g + 2) → Fin n := fun k => u.1 (Fin.cast (by rw [ha]) k)
      have hb : (b ⟨φ.funs.get g, by omega⟩).val ≠ (b ⟨φ.funs.get g + 1, by omega⟩).val := by
        simp only [b, e1, e2]; exact u.2
      refine Or.inl ⟨_, ⟨⟨Sum.inr (Sum.inl g), ⟨b, hb⟩⟩, rfl⟩, ?_⟩
      rw [poly_coll, poly_coll, map_mul, rename_X, rename_X, ιL_gvN, ιL_gvN]
      simp only [collOut1, collOut2, b, e1, e2]
      rfl
    · obtain ⟨g, rfl⟩ : ∃ g', g = dF φ ψ g' :=
        ⟨⟨g.1 - φ.funs.length, by have := g.2; have := conj_funs_length φ ψ; omega⟩,
          Fin.ext (by simp only [dF]; omega)⟩
      have ha := ar_dF φ ψ g
      obtain ⟨e1, e2⟩ := coll_index_eq ha.symm
      let b : Fin (ψ.funs.get g + 2) → Fin n := fun k => u.1 (Fin.cast (by rw [ha]) k)
      have hb : (b ⟨ψ.funs.get g, by omega⟩).val ≠ (b ⟨ψ.funs.get g + 1, by omega⟩).val := by
        simp only [b, e1, e2]; exact u.2
      refine Or.inr ⟨_, ⟨⟨Sum.inr (Sum.inl g), ⟨b, hb⟩⟩, rfl⟩, ?_⟩
      rw [poly_coll, poly_coll, map_mul, rename_X, rename_X, ιR_gvN, ιR_gvN]
      simp only [collOut1, collOut2, b, e1, e2]
      rfl
  · obtain ⟨j, t⟩ := u
    rcases j with R | g
    · by_cases hR : R.1 < φ.rels.length
      · obtain ⟨R, rfl⟩ : ∃ R', R = cR φ ψ R' := ⟨⟨R.1, hR⟩, rfl⟩
        refine Or.inl ⟨_, ⟨⟨Sum.inr (Sum.inr (Sum.inl ())),
          ⟨Sum.inl R, fun k => t (Fin.cast (ar_cR φ ψ R).symm k)⟩⟩, rfl⟩, ?_⟩
        rw [poly_bool, poly_bool, map_sub, map_pow, rename_X]
        rfl
      · obtain ⟨R, rfl⟩ : ∃ R', R = dR φ ψ R' :=
          ⟨⟨R.1 - φ.rels.length, by have := R.2; have := conj_rels_length φ ψ; omega⟩,
            Fin.ext (by simp only [dR]; omega)⟩
        refine Or.inr ⟨_, ⟨⟨Sum.inr (Sum.inr (Sum.inl ())),
          ⟨Sum.inl R, fun k => t (Fin.cast (ar_dR φ ψ R).symm k)⟩⟩, rfl⟩, ?_⟩
        rw [poly_bool, poly_bool, map_sub, map_pow, rename_X]
        rfl
    · by_cases hg : g.1 < φ.funs.length
      · obtain ⟨g, rfl⟩ : ∃ g', g = cF φ ψ g' := ⟨⟨g.1, hg⟩, rfl⟩
        refine Or.inl ⟨_, ⟨⟨Sum.inr (Sum.inr (Sum.inl ())),
          ⟨Sum.inr g, fun k => t (Fin.cast
            (show φ.funs.get g + 1 = (conj φ ψ).funs.get (cF φ ψ g) + 1 by rw [ar_cF]) k)⟩⟩,
          rfl⟩, ?_⟩
        rw [poly_bool, poly_bool, map_sub, map_pow, rename_X]
        rfl
      · obtain ⟨g, rfl⟩ : ∃ g', g = dF φ ψ g' :=
          ⟨⟨g.1 - φ.funs.length, by have := g.2; have := conj_funs_length φ ψ; omega⟩,
            Fin.ext (by simp only [dF]; omega)⟩
        refine Or.inr ⟨_, ⟨⟨Sum.inr (Sum.inr (Sum.inl ())),
          ⟨Sum.inr g, fun k => t (Fin.cast
            (show ψ.funs.get g + 1 = (conj φ ψ).funs.get (dF φ ψ g) + 1 by rw [ar_dF]) k)⟩⟩,
          rfl⟩, ?_⟩
        rw [poly_bool, poly_bool, map_sub, map_pow, rename_X]
        rfl
  · by_cases hc : ci.1 < φ.clauses.length
    · obtain ⟨ci, hci⟩ : ∃ c' : Fin φ.clauses.length, ci = cC φ ψ c' := ⟨⟨ci.1, hc⟩, rfl⟩
      clear hc
      subst hci
      have hcl := conj_clause_left φ ψ ci
      refine Or.inl ⟨_, ⟨⟨Sum.inr (Sum.inr (Sum.inr ci)), fun k => u (Fin.cast (by rw [hcl]) k)⟩,
        rfl⟩, ?_⟩
      rw [poly_clause, poly_clause, clausePoly_left φ ψ n _ _ (hφ _ (List.get_mem _ ci))]
      have e := clausePoly_congr (K := K) (rvN (conj φ ψ) n) (gvN (conj φ ψ) n) hcl
        (fun k => u (Fin.cast (by rw [hcl]) k))
      refine Eq.trans ?_ e
      rfl
    · have hlen : ci.1 - φ.clauses.length < ψ.clauses.length := by
        have h1 := ci.2
        have h2 : (conj φ ψ).clauses.length = φ.clauses.length + ψ.clauses.length := by
          rw [conj_clauses, List.length_append, List.length_map]
        omega
      obtain ⟨ci, hci⟩ : ∃ c' : Fin ψ.clauses.length, ci = dC φ ψ c' :=
        ⟨⟨ci.1 - φ.clauses.length, hlen⟩, Fin.ext (by simp only [dC]; omega)⟩
      clear hc hlen
      subst hci
      have hcl := conj_clause_right φ ψ ci
      have hnv : nvars (Clause.shift φ.rels.length φ.funs.length (ψ.clauses.get ci)) =
          nvars (ψ.clauses.get ci) := nvars_shift _ _ _
      refine Or.inr ⟨_, ⟨⟨Sum.inr (Sum.inr (Sum.inr ci)),
        fun k => u (Fin.cast (by rw [hcl, hnv]) k)⟩, rfl⟩, ?_⟩
      rw [poly_clause, poly_clause, clausePoly_right φ ψ n _ _ (hψ _ (List.get_mem _ ci))]
      have e := clausePoly_congr (K := K) (rvN (conj φ ψ) n) (gvN (conj φ ψ) n) hcl
        (fun k => u (Fin.cast (by rw [hcl]) k))
      refine Eq.trans e ?_
      congr 1
      funext x
      simp only [νOf]
      by_cases hx : x < nvars (ψ.clauses.get ci)
      · rw [dif_pos (by rw [hnv]; exact hx), dif_pos hx]; rfl
      · rw [dif_neg (by rw [hnv]; exact hx), dif_neg hx]; rfl

/-! ### Injectivity and disjointness of the two embeddings -/

theorem ιL_injective : Function.Injective (ιL φ ψ n) := by
  rintro ⟨i, t⟩ ⟨i', t'⟩ h
  rcases i with R | g <;> rcases i' with R' | g' <;> simp only [ιL] at h
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hR : R = R' := Fin.ext (by simpa [cR] using congrArg Fin.val (Sum.inl.inj h1))
    subst hR
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast (ar_cR φ ψ R).symm k)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hg : g = g' := Fin.ext (by simpa [cF] using congrArg Fin.val (Sum.inr.inj h1))
    subst hg
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast
      (show φ.funs.get g + 1 = (conj φ ψ).funs.get (cF φ ψ g) + 1 by rw [ar_cF]) k)

theorem ιR_injective : Function.Injective (ιR φ ψ n) := by
  rintro ⟨i, t⟩ ⟨i', t'⟩ h
  rcases i with R | g <;> rcases i' with R' | g' <;> simp only [ιR] at h
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hR : R = R' := Fin.ext (by
      have := congrArg Fin.val (Sum.inl.inj h1); simp only [dR] at this; omega)
    subst hR
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast (ar_dR φ ψ R).symm k)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hg : g = g' := Fin.ext (by
      have := congrArg Fin.val (Sum.inr.inj h1); simp only [dF] at this; omega)
    subst hg
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast
      (show ψ.funs.get g + 1 = (conj φ ψ).funs.get (dF φ ψ g) + 1 by rw [ar_dF]) k)

theorem ιL_ne_ιR (u : (VarSys φ).Rk n) (w : (VarSys ψ).Rk n) : ιL φ ψ n u ≠ ιR φ ψ n w := by
  obtain ⟨i, t⟩ := u
  obtain ⟨i', t'⟩ := w
  intro h
  rcases i with R | g <;> rcases i' with R' | g' <;> simp only [ιL, ιR] at h
  · have := congrArg Fin.val (Sum.inl.inj (Sigma.mk.inj_iff.mp h).1)
    simp only [cR, dR] at this; have := R.2; omega
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · have := congrArg Fin.val (Sum.inr.inj (Sigma.mk.inj_iff.mp h).1)
    simp only [cF, dF] at this; have := g.2; omega

end Clauses

/-! ### Degrees of a conjunction -/

section Degrees
variable (K : Type) [Field K]

theorem totalDegree_rename_X_le {σ τ : Type} (e : σ → τ) (i : σ) :
    (rename e (X i : MvPolynomial σ K)).totalDegree ≤ 1 := by
  rw [rename_X]; exact totalDegree_X_le' _

/-- The conjunction is at least as easy as its first block. -/
theorem nsDegree_conj_le_left (hφ : WF φ) :
    nsDegree ((template (conj φ ψ) K).inst n) ≤ nsDegree ((template φ K).inst n) :=
  nsDegree_le_of_hom (rename (ιL φ ψ n)) (totalDegree_rename_X_le K _)
    (fun _ hf => mem_NSspan_of_image (Or.inl (inst_left φ ψ n hφ hf)) (totalDegree_rename_le _ _))

/-- The conjunction is at least as easy as its second block. -/
theorem nsDegree_conj_le_right (hψ : WF ψ) :
    nsDegree ((template (conj φ ψ) K).inst n) ≤ nsDegree ((template ψ K).inst n) :=
  nsDegree_le_of_hom (rename (ιR φ ψ n)) (totalDegree_rename_X_le K _)
    (fun _ hf => mem_NSspan_of_image (Or.inl (inst_right φ ψ n hψ hf)) (totalDegree_rename_le _ _))

open Classical in
/-- Substitute a common root `y` of the second block. -/
noncomputable def subRoot (y : (VarSys ψ).Rk n → K) :
    MvPolynomial ((VarSys (conj φ ψ)).Rk n) K →ₐ[K] MvPolynomial ((VarSys φ).Rk n) K :=
  aeval fun v => if h : ∃ u, ιL φ ψ n u = v then X (Classical.choose h)
    else if h' : ∃ w, ιR φ ψ n w = v then C (y (Classical.choose h')) else 0

theorem subRoot_X_left (y : (VarSys ψ).Rk n → K) (u : (VarSys φ).Rk n) :
    subRoot φ ψ n K y (X (ιL φ ψ n u)) = X u := by
  classical
  have h : ∃ u', ιL φ ψ n u' = ιL φ ψ n u := ⟨u, rfl⟩
  simp only [subRoot, aeval_X, dif_pos h]
  rw [ιL_injective φ ψ n (Classical.choose_spec h)]

theorem subRoot_X_right (y : (VarSys ψ).Rk n → K) (w : (VarSys ψ).Rk n) :
    subRoot φ ψ n K y (X (ιR φ ψ n w)) = C (y w) := by
  classical
  have h0 : ¬ ∃ u, ιL φ ψ n u = ιR φ ψ n w := fun ⟨u, hu⟩ => ιL_ne_ιR φ ψ n u w hu
  have h : ∃ w', ιR φ ψ n w' = ιR φ ψ n w := ⟨w, rfl⟩
  simp only [subRoot, aeval_X, dif_neg h0, dif_pos h]
  rw [ιR_injective φ ψ n (Classical.choose_spec h)]

theorem subRoot_left (y : (VarSys ψ).Rk n → K) (f : MvPolynomial ((VarSys φ).Rk n) K) :
    subRoot φ ψ n K y (rename (ιL φ ψ n) f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, subRoot_X_left]

theorem subRoot_right (y : (VarSys ψ).Rk n → K) (g : MvPolynomial ((VarSys ψ).Rk n) K) :
    subRoot φ ψ n K y (rename (ιR φ ψ n) g) = C (eval y g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, subRoot_X_right, map_mul, map_mul, eval_X]

/-- **The satisfiable-block lemma** (manuscript `lem:disjoint`): if the second block has a
common root at size `n`, the conjunction has exactly the NS degree of the first block. -/
theorem nsDegree_conj_eq_left (hφ : WF φ) (hψ : WF ψ) (y : (VarSys ψ).Rk n → K)
    (hy : ∀ g ∈ (template ψ K).inst n, eval y g = 0) :
    nsDegree ((template (conj φ ψ) K).inst n) = nsDegree ((template φ K).inst n) := by
  classical
  refine le_antisymm (nsDegree_conj_le_left φ ψ n K hφ) ?_
  apply nsDegree_le_of_hom (subRoot φ ψ n K y)
  · intro v
    simp only [subRoot, aeval_X]
    split_ifs
    · exact totalDegree_X_le' _
    · simp
    · simp
  · rintro _ ⟨i, rfl⟩
    rcases inst_conj φ ψ n hφ hψ i with ⟨f, hf, e⟩ | ⟨g, hg, e⟩
    · have hd : f.totalDegree ≤ (rename (ιL φ ψ n) f).totalDegree := by
        have := totalDegree_map_le (subRoot φ ψ n K y) (fun v => by
          simp only [subRoot, aeval_X]; split_ifs
          · exact totalDegree_X_le' _
          · simp
          · simp) (rename (ιL φ ψ n) f)
        rwa [subRoot_left] at this
      rw [e, subRoot_left]
      exact mem_NSspan_of_image (Or.inl hf) hd
    · rw [e, subRoot_right, hy g hg, map_zero]
      exact Submodule.zero_mem _

/-- A common root of the conjunction restricts to a common root of each block. -/
theorem conj_root_right (hψ : WF ψ) (x : (VarSys (conj φ ψ)).Rk n → K)
    (hx : ∀ f ∈ (template (conj φ ψ) K).inst n, eval x f = 0) :
    ∀ g ∈ (template ψ K).inst n, eval (x ∘ ιR φ ψ n) g = 0 := by
  intro g hg
  rw [← eval_rename]
  exact hx _ (inst_right φ ψ n hψ hg)

theorem conj_root_left (hφ : WF φ) (x : (VarSys (conj φ ψ)).Rk n → K)
    (hx : ∀ f ∈ (template (conj φ ψ) K).inst n, eval x f = 0) :
    ∀ f ∈ (template φ K).inst n, eval (x ∘ ιL φ ψ n) f = 0 := by
  intro f hf
  rw [← eval_rename]
  exact hx _ (inst_left φ ψ n hφ hf)

/-- A model of the conjunction gives models of both blocks (via roots, `n ≥ 1`). -/
theorem hasModel_conj (hφ : WF φ) (hψ : WF ψ) (hn : 0 < n) (h : HasModelOfSize (conj φ ψ) n) :
    HasModelOfSize φ n ∧ HasModelOfSize ψ n := by
  obtain ⟨x, hx⟩ := (hasRoot_iff (conj φ ψ) ℚ hn).mpr h
  exact ⟨(hasRoot_iff φ ℚ hn).mp ⟨_, conj_root_left φ ψ n ℚ hφ x hx⟩,
    (hasRoot_iff ψ ℚ hn).mp ⟨_, conj_root_right φ ψ n ℚ hψ x hx⟩⟩

end Degrees

end Maps

end ClaudeUndec
