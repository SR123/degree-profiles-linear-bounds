/-
Claude, 27 Sep 2026.  Undecidability, part J1: the unary-selector guarded join `A ∨_* B`
(manuscript, pair version of `thm:undecidable`).

`join A B` has the disjoint union of the signatures of `A` and `B` (the symbols of `B` shifted,
as in `conj`), followed by one fresh unary relation `Z`.  Its clauses are

* `¬Z(t) ∨ C` for every clause `C` of `A` (i.e. `∀t (Z(t) → C)`), and
* `Z(t) ∨ C'` for every clause `C` of `B`, `C'` its shift (i.e. `∀t (¬Z(t) → C')`),

where `t = nvars C` is a fresh variable.  Both blocks are normalized separately, so the
structural equations (totality, collisions, Booleanity) of both blocks are retained, and `Z`
contributes the Boolean axioms `z_t² - z_t`.

This file sets up the variables and axioms of the join:

* the embeddings `ιA`, `ιB` of the variables of the two blocks and the selector variables `zv t`
  (`z_t = Z(t)`), injective with disjoint ranges and jointly surjective (`var_cases`);
* `instA`, `instB`: every axiom `f` of `A` (resp. `B`), renamed, is an axiom of the join, or else
  `z_t · f` (resp. `(1 - z_t) · f`) is one for every `t`;
* `join_cases`: every axiom of the join is a renamed structural axiom of a block, a Boolean
  selector axiom, `z_t · f` with `f` an axiom of `A`, or `(1 - z_t) · g` with `g` an axiom of `B`.
-/
import UWitCommon

set_option autoImplicit false
set_option linter.unusedSimpArgs false
open MvPolynomial DegreeProfilesReview.Uniform DegreeProfilesReview.NS

namespace ClaudeUndec

/-! ### Syntax -/

/-- `¬Z(t) ∨ C` with `t = nvars C` fresh. -/
def guardN (z : ℕ) (c : Clause) : Clause := (false, Atom.rel z [nvars c]) :: c

/-- `Z(t) ∨ C` with `t = nvars C` fresh. -/
def guardP (z : ℕ) (c : Clause) : Clause := (true, Atom.rel z [nvars c]) :: c

/-- **The unary-selector guarded join** `A ∨_* B`. -/
def join (A B : Sentence) : Sentence :=
  (((A.rels ++ B.rels) ++ [1], A.funs ++ B.funs),
    A.clauses.map (guardN (A.rels.length + B.rels.length)) ++
      (B.clauses.map (Clause.shift A.rels.length A.funs.length)).map
        (guardP (A.rels.length + B.rels.length)))

section Maps
variable (A B : Sentence)

theorem join_rels : (join A B).rels = (A.rels ++ B.rels) ++ [1] := rfl
theorem join_funs : (join A B).funs = A.funs ++ B.funs := rfl
theorem join_clauses : (join A B).clauses =
    A.clauses.map (guardN (A.rels.length + B.rels.length)) ++
      (B.clauses.map (Clause.shift A.rels.length A.funs.length)).map
        (guardP (A.rels.length + B.rels.length)) := rfl

theorem join_rels_length : (join A B).rels.length = A.rels.length + B.rels.length + 1 := by
  rw [join_rels, List.length_append, List.length_append]; rfl
theorem join_funs_length : (join A B).funs.length = A.funs.length + B.funs.length := by
  rw [join_funs, List.length_append]

def aR (R : Fin A.rels.length) : Fin (join A B).rels.length :=
  ⟨R.1, by rw [join_rels_length]; omega⟩
def bR (R : Fin B.rels.length) : Fin (join A B).rels.length :=
  ⟨A.rels.length + R.1, by rw [join_rels_length]; omega⟩
/-- The selector symbol `Z`. -/
def zR : Fin (join A B).rels.length :=
  ⟨A.rels.length + B.rels.length, by rw [join_rels_length]; omega⟩
def aF (f : Fin A.funs.length) : Fin (join A B).funs.length :=
  ⟨f.1, by rw [join_funs_length]; omega⟩
def bF (f : Fin B.funs.length) : Fin (join A B).funs.length :=
  ⟨A.funs.length + f.1, by rw [join_funs_length]; omega⟩

theorem ar_aR (R : Fin A.rels.length) : (join A B).rels.get (aR A B R) = A.rels.get R := by
  simp only [List.get_eq_getElem, aR, join_rels]
  rw [List.getElem_append_left (by rw [List.length_append]; omega),
    List.getElem_append_left R.2]
theorem ar_bR (R : Fin B.rels.length) : (join A B).rels.get (bR A B R) = B.rels.get R := by
  simp only [List.get_eq_getElem, bR, join_rels]
  rw [List.getElem_append_left (by rw [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  congr 1; omega
theorem ar_zR : (join A B).rels.get (zR A B) = 1 := by
  simp only [List.get_eq_getElem, zR, join_rels]
  rw [List.getElem_append_right (by rw [List.length_append])]
  simp
theorem ar_aF (f : Fin A.funs.length) : (join A B).funs.get (aF A B f) = A.funs.get f := by
  simp only [List.get_eq_getElem, aF, join_funs, List.getElem_append_left f.2]
theorem ar_bF (f : Fin B.funs.length) : (join A B).funs.get (bF A B f) = B.funs.get f := by
  simp only [List.get_eq_getElem, bF, join_funs]
  rw [List.getElem_append_right (by omega)]
  congr 1; omega

variable (n : ℕ)

/-- The variables of `A` inside the join. -/
def ιA : (VarSys A).Rk n → (VarSys (join A B)).Rk n
  | ⟨Sum.inl R, t⟩ => ⟨Sum.inl (aR A B R), fun i => t (Fin.cast (ar_aR A B R) i)⟩
  | ⟨Sum.inr f, t⟩ => ⟨Sum.inr (aF A B f), fun i =>
      t (Fin.cast (show (join A B).funs.get (aF A B f) + 1 = A.funs.get f + 1 by rw [ar_aF]) i)⟩

/-- The variables of `B` inside the join. -/
def ιB : (VarSys B).Rk n → (VarSys (join A B)).Rk n
  | ⟨Sum.inl R, t⟩ => ⟨Sum.inl (bR A B R), fun i => t (Fin.cast (ar_bR A B R) i)⟩
  | ⟨Sum.inr f, t⟩ => ⟨Sum.inr (bF A B f), fun i =>
      t (Fin.cast (show (join A B).funs.get (bF A B f) + 1 = B.funs.get f + 1 by rw [ar_bF]) i)⟩

/-- The selector variable `z_t = Z(t)`. -/
def zv (t : Fin n) : (VarSys (join A B)).Rk n := rvN (join A B) n (zR A B) (fun _ => t)

theorem ιA_gvN (f : Fin A.funs.length) (t : Fin (A.funs.get f) → Fin n) (j : Fin n) :
    ιA A B n (gvN A n f t j) =
      gvN (join A B) n (aF A B f) (fun i => t (Fin.cast (ar_aF A B f) i)) j := by
  show (⟨Sum.inr (aF A B f), _⟩ : (VarSys (join A B)).Rk n) = ⟨Sum.inr (aF A B f), _⟩
  congr 1
  funext i
  exact snoc_cast n (ar_aF A B f) t j i

theorem ιB_gvN (f : Fin B.funs.length) (t : Fin (B.funs.get f) → Fin n) (j : Fin n) :
    ιB A B n (gvN B n f t j) =
      gvN (join A B) n (bF A B f) (fun i => t (Fin.cast (ar_bF A B f) i)) j := by
  show (⟨Sum.inr (bF A B f), _⟩ : (VarSys (join A B)).Rk n) = ⟨Sum.inr (bF A B f), _⟩
  congr 1
  funext i
  exact snoc_cast n (ar_bF A B f) t j i

/-! ### Injectivity, disjointness, surjectivity -/

theorem ιA_injective : Function.Injective (ιA A B n) := by
  rintro ⟨i, t⟩ ⟨i', t'⟩ h
  rcases i with R | g <;> rcases i' with R' | g' <;> simp only [ιA] at h
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hR : R = R' := Fin.ext (by simpa [aR] using congrArg Fin.val (Sum.inl.inj h1))
    subst hR
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast (ar_aR A B R).symm k)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hg : g = g' := Fin.ext (by simpa [aF] using congrArg Fin.val (Sum.inr.inj h1))
    subst hg
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast
      (show A.funs.get g + 1 = (join A B).funs.get (aF A B g) + 1 by rw [ar_aF]) k)

theorem ιB_injective : Function.Injective (ιB A B n) := by
  rintro ⟨i, t⟩ ⟨i', t'⟩ h
  rcases i with R | g <;> rcases i' with R' | g' <;> simp only [ιB] at h
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hR : R = R' := Fin.ext (by
      have := congrArg Fin.val (Sum.inl.inj h1); simp only [bR] at this; omega)
    subst hR
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast (ar_bR A B R).symm k)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    have hg : g = g' := Fin.ext (by
      have := congrArg Fin.val (Sum.inr.inj h1); simp only [bF] at this; omega)
    subst hg
    have h3 := eq_of_heq h2
    congr 1
    funext k
    simpa using congrFun h3 (Fin.cast
      (show B.funs.get g + 1 = (join A B).funs.get (bF A B g) + 1 by rw [ar_bF]) k)

theorem zv_injective : Function.Injective (zv A B n) := by
  intro t t' h
  have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have := congrFun h2 (Fin.cast (ar_zR A B).symm ⟨0, Nat.one_pos⟩)
  exact this

theorem ιA_ne_ιB (u : (VarSys A).Rk n) (w : (VarSys B).Rk n) : ιA A B n u ≠ ιB A B n w := by
  obtain ⟨i, t⟩ := u
  obtain ⟨i', t'⟩ := w
  intro h
  rcases i with R | g <;> rcases i' with R' | g' <;> simp only [ιA, ιB] at h
  · have := congrArg Fin.val (Sum.inl.inj (Sigma.mk.inj_iff.mp h).1)
    simp only [aR, bR] at this; have := R.2; omega
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)
  · have := congrArg Fin.val (Sum.inr.inj (Sigma.mk.inj_iff.mp h).1)
    simp only [aF, bF] at this; have := g.2; omega

theorem ιA_ne_zv (u : (VarSys A).Rk n) (t : Fin n) : ιA A B n u ≠ zv A B n t := by
  obtain ⟨i, s⟩ := u
  intro h
  rcases i with R | g <;> simp only [ιA, zv, rvN] at h
  · have := congrArg Fin.val (Sum.inl.inj (Sigma.mk.inj_iff.mp h).1)
    simp only [aR, zR] at this; have := R.2; omega
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)

theorem ιB_ne_zv (w : (VarSys B).Rk n) (t : Fin n) : ιB A B n w ≠ zv A B n t := by
  obtain ⟨i, s⟩ := w
  intro h
  rcases i with R | g <;> simp only [ιB, zv, rvN] at h
  · have := congrArg Fin.val (Sum.inl.inj (Sigma.mk.inj_iff.mp h).1)
    simp only [bR, zR] at this; have := R.2; omega
  · exact absurd (Sigma.mk.inj_iff.mp h).1 (by simp)

/-- Every variable of the join is a variable of `A`, of `B`, or a selector. -/
theorem var_cases (v : (VarSys (join A B)).Rk n) :
    (∃ u, v = ιA A B n u) ∨ (∃ w, v = ιB A B n w) ∨ (∃ t, v = zv A B n t) := by
  obtain ⟨i, t⟩ := v
  rcases i with R | g
  · by_cases hR : R.1 < A.rels.length
    · obtain ⟨R, rfl⟩ : ∃ R', R = aR A B R' := ⟨⟨R.1, hR⟩, rfl⟩
      exact Or.inl ⟨⟨Sum.inl R, fun k => t (Fin.cast (ar_aR A B R).symm k)⟩, rfl⟩
    · by_cases hR' : R.1 < A.rels.length + B.rels.length
      · obtain ⟨R, rfl⟩ : ∃ R', R = bR A B R' :=
          ⟨⟨R.1 - A.rels.length, by omega⟩, Fin.ext (by simp only [bR]; omega)⟩
        exact Or.inr (Or.inl ⟨⟨Sum.inl R, fun k => t (Fin.cast (ar_bR A B R).symm k)⟩, rfl⟩)
      · have hz : R = zR A B := Fin.ext (by
          have := R.2; have := join_rels_length A B; simp only [zR]; omega)
        subst hz
        refine Or.inr (Or.inr ⟨t (Fin.cast (ar_zR A B).symm ⟨0, Nat.one_pos⟩), ?_⟩)
        show (⟨Sum.inl (zR A B), t⟩ : (VarSys (join A B)).Rk n) = ⟨Sum.inl (zR A B), _⟩
        congr 1
        funext k
        congr 1
        apply Fin.ext
        have := k.2
        change k.val < (join A B).rels.get (zR A B) at this
        rw [ar_zR] at this
        simp only [Fin.val_cast]
        omega
  · by_cases hg : g.1 < A.funs.length
    · obtain ⟨g, rfl⟩ : ∃ g', g = aF A B g' := ⟨⟨g.1, hg⟩, rfl⟩
      exact Or.inl ⟨⟨Sum.inr g, fun k => t (Fin.cast
        (show A.funs.get g + 1 = (join A B).funs.get (aF A B g) + 1 by rw [ar_aF]) k)⟩, rfl⟩
    · obtain ⟨g, rfl⟩ : ∃ g', g = bF A B g' :=
        ⟨⟨g.1 - A.funs.length, by have := g.2; have := join_funs_length A B; omega⟩,
          Fin.ext (by simp only [bF]; omega)⟩
      exact Or.inr (Or.inl ⟨⟨Sum.inr g, fun k => t (Fin.cast
        (show B.funs.get g + 1 = (join A B).funs.get (bF A B g) + 1 by rw [ar_bF]) k)⟩, rfl⟩)

/-! ### Atoms and clauses of the two blocks -/

section Clauses
variable {K : Type} [Field K]

theorem getD_join_rels_left {R : ℕ} (h : R < A.rels.length) :
    (join A B).rels.getD R 0 = A.rels.getD R 0 := by
  rw [join_rels, List.getD_append _ _ _ _ (by rw [List.length_append]; omega),
    List.getD_append _ _ _ _ h]

theorem getD_join_rels_right {R : ℕ} (h : R < B.rels.length) :
    (join A B).rels.getD (A.rels.length + R) 0 = B.rels.getD R 0 := by
  rw [join_rels, List.getD_append _ _ _ _ (by rw [List.length_append]; omega),
    List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

theorem getD_join_rels_z : (join A B).rels.getD (A.rels.length + B.rels.length) 0 = 1 := by
  rw [join_rels, List.getD_append_right _ _ _ _ (by rw [List.length_append])]
  simp

theorem getD_join_funs_left {f : ℕ} (h : f < A.funs.length) :
    (join A B).funs.getD f 0 = A.funs.getD f 0 := by
  rw [join_funs, List.getD_append _ _ _ _ h]

theorem getD_join_funs_right (f : ℕ) :
    (join A B).funs.getD (A.funs.length + f) 0 = B.funs.getD f 0 := by
  rw [join_funs, List.getD_append_right _ _ _ _ (by omega)]
  congr 1; omega

theorem atomVal_A (ν : ℕ → Fin n) (a : Atom) (ha : AtomWF A a) :
    rename (ιA A B n) (atomVal A (rvN A n) (gvN A n) ν a : MvPolynomial _ K) =
      atomVal (join A B) (rvN (join A B) n) (gvN (join A B) n) ν a := by
  classical
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · obtain ⟨hR, hl⟩ := ha
    have hR' : R < (join A B).rels.length := by rw [join_rels_length]; omega
    have hl' : args.length = (join A B).rels.getD R 0 := by
      rw [getD_join_rels_left A B hR]; exact hl
    simp only [atomVal, dif_pos (And.intro hR hl), dif_pos (And.intro hR' hl'), rename_X]
    rfl
  · obtain ⟨hf, hl⟩ := ha
    have hf' : f < (join A B).funs.length := by rw [join_funs_length]; omega
    have hl' : args.length = (join A B).funs.getD f 0 := by
      rw [getD_join_funs_left A B hf]; exact hl
    simp only [atomVal, dif_pos (And.intro hf hl), dif_pos (And.intro hf' hl'), rename_X]
    rw [ιA_gvN]
    rfl
  · simp only [atomVal]
    split_ifs <;> simp

theorem atomVal_B (ν : ℕ → Fin n) (a : Atom) (ha : AtomWF B a) :
    rename (ιB A B n) (atomVal B (rvN B n) (gvN B n) ν a : MvPolynomial _ K) =
      atomVal (join A B) (rvN (join A B) n) (gvN (join A B) n) ν
        (a.shift A.rels.length A.funs.length) := by
  classical
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · obtain ⟨hR, hl⟩ := ha
    have hR' : A.rels.length + R < (join A B).rels.length := by rw [join_rels_length]; omega
    have hl' : args.length = (join A B).rels.getD (A.rels.length + R) 0 := by
      rw [getD_join_rels_right A B hR]; exact hl
    simp only [Atom.shift, atomVal, dif_pos (And.intro hR hl), dif_pos (And.intro hR' hl'),
      rename_X]
    rfl
  · obtain ⟨hf, hl⟩ := ha
    have hf' : A.funs.length + f < (join A B).funs.length := by rw [join_funs_length]; omega
    have hl' : args.length = (join A B).funs.getD (A.funs.length + f) 0 := by
      rw [getD_join_funs_right]; exact hl
    simp only [Atom.shift, atomVal, dif_pos (And.intro hf hl), dif_pos (And.intro hf' hl'),
      rename_X]
    rw [ιB_gvN]
    rfl
  · simp only [Atom.shift, atomVal]
    split_ifs <;> simp

theorem atomVal_Z (ν : ℕ → Fin n) (x : ℕ) :
    (atomVal (join A B) (rvN (join A B) n) (gvN (join A B) n) ν
      (Atom.rel (A.rels.length + B.rels.length) [x]) : MvPolynomial _ K) = X (zv A B n (ν x)) := by
  classical
  have hR' : A.rels.length + B.rels.length < (join A B).rels.length := by
    rw [join_rels_length]; omega
  have hl' : [x].length = (join A B).rels.getD (A.rels.length + B.rels.length) 0 := by
    rw [getD_join_rels_z]; rfl
  simp only [atomVal, dif_pos (And.intro hR' hl')]
  congr 1
  show (⟨Sum.inl (zR A B), _⟩ : (VarSys (join A B)).Rk n) = ⟨Sum.inl (zR A B), _⟩
  congr 1
  funext k
  have hk := k.2
  change k.val < (join A B).rels.get (zR A B) at hk
  rw [ar_zR] at hk
  simp only [tupleOf]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [show k.val = 0 by omega]

theorem clausePoly_A (ν : ℕ → Fin n) (c : Clause) (hc : ∀ l ∈ c, AtomWF A l.2) :
    rename (ιA A B n) (clausePoly A (rvN A n) (gvN A n) ν c : MvPolynomial _ K) =
      clausePoly (join A B) (rvN (join A B) n) (gvN (join A B) n) ν c := by
  unfold clausePoly
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply, litFactor]
  split_ifs
  · rw [map_sub, map_one, atomVal_A A B n ν l.2 (hc l hl)]
  · rw [atomVal_A A B n ν l.2 (hc l hl)]

theorem clausePoly_B (ν : ℕ → Fin n) (c : Clause) (hc : ∀ l ∈ c, AtomWF B l.2) :
    rename (ιB A B n) (clausePoly B (rvN B n) (gvN B n) ν c : MvPolynomial _ K) =
      clausePoly (join A B) (rvN (join A B) n) (gvN (join A B) n) ν
        (Clause.shift A.rels.length A.funs.length c) := by
  unfold clausePoly Clause.shift
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply, litFactor]
  split_ifs
  · rw [map_sub, map_one, atomVal_B A B n ν l.2 (hc l hl)]
  · rw [atomVal_B A B n ν l.2 (hc l hl)]

theorem clausePoly_guardN (ν : ℕ → Fin n) (c : Clause) :
    (clausePoly (join A B) (rvN (join A B) n) (gvN (join A B) n) ν
      (guardN (A.rels.length + B.rels.length) c) : MvPolynomial _ K) =
      X (zv A B n (ν (nvars c))) *
        clausePoly (join A B) (rvN (join A B) n) (gvN (join A B) n) ν c := by
  unfold clausePoly guardN
  rw [List.map_cons, List.prod_cons]
  congr 1
  simp only [litFactor, Bool.false_eq_true, if_false]
  exact atomVal_Z A B n ν _

theorem clausePoly_guardP (ν : ℕ → Fin n) (c : Clause) :
    (clausePoly (join A B) (rvN (join A B) n) (gvN (join A B) n) ν
      (guardP (A.rels.length + B.rels.length) c) : MvPolynomial _ K) =
      (1 - X (zv A B n (ν (nvars c)))) *
        clausePoly (join A B) (rvN (join A B) n) (gvN (join A B) n) ν c := by
  unfold clausePoly guardP
  rw [List.map_cons, List.prod_cons]
  congr 1
  simp only [litFactor, if_true]
  rw [atomVal_Z A B n ν _]

end Clauses

end Maps

/-! ### Structural axioms -/

section Struct
variable (φ : Sentence) (K : Type) [Field K] (n : ℕ)

theorem tot_mem (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) :
    (∑ j : Fin n, X (gvN φ n f t j)) - 1 ∈ (template φ K).inst n :=
  ⟨⟨Sum.inl f, t⟩, poly_tot φ K n f t⟩

theorem coll_mem (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j j' : Fin n)
    (h : j ≠ j') : X (gvN φ n f t j) * X (gvN φ n f t j') ∈ (template φ K).inst n := by
  have hP : (collIdx t j j' ⟨φ.funs.get f, by omega⟩).val ≠
      (collIdx t j j' ⟨φ.funs.get f + 1, by omega⟩).val := by
    have e1 : collIdx t j j' ⟨φ.funs.get f, by omega⟩ = j := collOut1_collIdx t j j'
    have e2 : collIdx t j j' ⟨φ.funs.get f + 1, by omega⟩ = j' := collOut2_collIdx t j j'
    rw [e1, e2]
    exact fun h' => h (Fin.ext h')
  refine ⟨⟨Sum.inr (Sum.inl f), ⟨collIdx t j j', hP⟩⟩, ?_⟩
  rw [poly_coll]
  simp only [collIn_collIdx, collOut1_collIdx, collOut2_collIdx]

/-- Structural axioms: totality, collisions and Booleanity. -/
def IsStruct (g : MvPolynomial ((VarSys φ).Rk n) K) : Prop :=
  (∃ (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n),
      g = (∑ j : Fin n, X (gvN φ n f t j)) - 1) ∨
    (∃ (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j j' : Fin n), j ≠ j' ∧
      g = X (gvN φ n f t j) * X (gvN φ n f t j')) ∨
    (∃ v, g = X v ^ 2 - X v)

theorem struct_mem {g : MvPolynomial ((VarSys φ).Rk n) K} (h : IsStruct φ K n g) :
    g ∈ (template φ K).inst n := by
  rcases h with ⟨f, t, rfl⟩ | ⟨f, t, j, j', hj, rfl⟩ | ⟨v, rfl⟩
  · exact tot_mem φ K n f t
  · exact coll_mem φ K n f t j j' hj
  · exact bool_mem φ K v

/-- The structural point: all relations false, every function constantly the label `0`. -/
def spt : (VarSys φ).Rk n → K
  | ⟨Sum.inl _, _⟩ => 0
  | ⟨Sum.inr _, t⟩ => if (t (Fin.last _)).val = 0 then 1 else 0

theorem spt_gvN (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j : Fin n) :
    spt φ K n (gvN φ n f t j) = if j.val = 0 then 1 else 0 := by
  show (if ((Fin.snoc (α := fun _ => Fin n) t j) (Fin.last _)).val = 0 then (1 : K) else 0) = _
  rw [Fin.snoc_last]

theorem spt_01 (v : (VarSys φ).Rk n) : spt φ K n v = 0 ∨ spt φ K n v = 1 := by
  obtain ⟨i, t⟩ := v
  rcases i with R | f
  · exact Or.inl rfl
  · show (if _ then (1 : K) else 0) = 0 ∨ (if _ then (1 : K) else 0) = 1
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The structural axioms vanish at the structural point (`n ≥ 1`). -/
theorem struct_spt (hn : 0 < n) {g : MvPolynomial ((VarSys φ).Rk n) K}
    (h : IsStruct φ K n g) : eval (spt φ K n) g = 0 := by
  classical
  rcases h with ⟨f, t, rfl⟩ | ⟨f, t, j, j', hj, rfl⟩ | ⟨v, rfl⟩
  · simp only [map_sub, map_sum, eval_X, map_one, spt_gvN]
    rw [sub_eq_zero]
    have : ∀ j : Fin n, (if j.val = 0 then (1 : K) else 0) =
        if j = ⟨0, hn⟩ then 1 else 0 := fun j => by
      congr 1; exact propext ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [map_mul, eval_X, spt_gvN]
    split_ifs with h1 h2
    · exact absurd (Fin.ext (h1.trans h2.symm)) hj
    · simp
    · simp
    · simp
  · simp only [map_sub, map_pow, eval_X]
    rcases spt_01 φ K n v with h | h <;> rw [h] <;> ring

end Struct

/-! ### The axioms of the join -/

section JoinAxioms
variable (A B : Sentence) (K : Type) [Field K] (n : ℕ)

theorem guardN_mem {c : Clause} (hc : c ∈ A.clauses) :
    guardN (A.rels.length + B.rels.length) c ∈ (join A B).clauses := by
  rw [join_clauses]; exact List.mem_append_left _ (List.mem_map_of_mem hc)

theorem guardP_mem {c : Clause} (hc : c ∈ B.clauses) :
    guardP (A.rels.length + B.rels.length) (Clause.shift A.rels.length A.funs.length c) ∈
      (join A B).clauses := by
  rw [join_clauses]
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_map_of_mem hc))

/-- Axioms of `A` in the join: renamed, or guarded by `z_t` for every `t`. -/
theorem instA (hA : WF A) {g : MvPolynomial ((VarSys A).Rk n) K} (hg : g ∈ (template A K).inst n) :
    rename (ιA A B n) g ∈ (template (join A B) K).inst n ∨
      ∀ t, X (zv A B n t) * rename (ιA A B n) g ∈ (template (join A B) K).inst n := by
  rcases inst_cases A K hg with ⟨f, t, rfl⟩ | ⟨f, t, j, j', hj, rfl⟩ | ⟨v, rfl⟩ | ⟨c, hc, ν, rfl⟩
  · left
    rw [map_sub, map_sum, map_one]
    simp only [rename_X, ιA_gvN]
    exact tot_mem _ K n _ _
  · left
    rw [map_mul, rename_X, rename_X, ιA_gvN, ιA_gvN]
    exact coll_mem _ K n _ _ _ _ hj
  · left
    rw [map_sub, map_pow, rename_X]
    exact bool_mem _ K _
  · right
    intro t
    have hm := clause_mem (join A B) K (guardN_mem A B hc) (Function.update ν (nvars c) t)
    rw [clausePoly_guardN, Function.update_self] at hm
    rw [clausePoly_A A B n ν c (hA c hc)]
    convert hm using 2
    apply clausePoly_congr_vars
    intro l hl v hv
    rw [Function.update_of_ne (Nat.ne_of_lt (var_lt_nvars hl hv))]

/-- Axioms of `B` in the join: renamed, or guarded by `1 - z_t` for every `t`. -/
theorem instB (hB : WF B) {g : MvPolynomial ((VarSys B).Rk n) K} (hg : g ∈ (template B K).inst n) :
    rename (ιB A B n) g ∈ (template (join A B) K).inst n ∨
      ∀ t, (1 - X (zv A B n t)) * rename (ιB A B n) g ∈ (template (join A B) K).inst n := by
  rcases inst_cases B K hg with ⟨f, t, rfl⟩ | ⟨f, t, j, j', hj, rfl⟩ | ⟨v, rfl⟩ | ⟨c, hc, ν, rfl⟩
  · left
    rw [map_sub, map_sum, map_one]
    simp only [rename_X, ιB_gvN]
    exact tot_mem _ K n _ _
  · left
    rw [map_mul, rename_X, rename_X, ιB_gvN, ιB_gvN]
    exact coll_mem _ K n _ _ _ _ hj
  · left
    rw [map_sub, map_pow, rename_X]
    exact bool_mem _ K _
  · right
    intro t
    have hm := clause_mem (join A B) K (guardP_mem A B hc) (Function.update ν (nvars c) t)
    rw [clausePoly_guardP, nvars_shift, Function.update_self] at hm
    rw [clausePoly_B A B n ν c (hB c hc)]
    convert hm using 2
    apply clausePoly_congr_vars
    intro l hl v hv
    have := var_lt_nvars hl hv
    rw [nvars_shift] at this
    rw [Function.update_of_ne (Nat.ne_of_lt this)]

/-- **Every axiom of the join** is a renamed structural axiom of `A` or of `B`, a Boolean
selector axiom, `z_t · f` with `f` an axiom of `A`, or `(1 - z_t) · g` with `g` an axiom of
`B`. -/
theorem join_cases (hA : WF A) (hB : WF B) {g : MvPolynomial ((VarSys (join A B)).Rk n) K}
    (hg : g ∈ (template (join A B) K).inst n) :
    (∃ f, IsStruct A K n f ∧ g = rename (ιA A B n) f) ∨
    (∃ f, IsStruct B K n f ∧ g = rename (ιB A B n) f) ∨
    (∃ t, g = X (zv A B n t) ^ 2 - X (zv A B n t)) ∨
    (∃ f ∈ (template A K).inst n, ∃ t, g = X (zv A B n t) * rename (ιA A B n) f) ∨
    (∃ f ∈ (template B K).inst n, ∃ t, g = (1 - X (zv A B n t)) * rename (ιB A B n) f) := by
  rcases inst_cases (join A B) K hg with ⟨f, t, rfl⟩ | ⟨f, t, j, j', hj, rfl⟩ | ⟨v, rfl⟩ |
    ⟨c, hc, ν, rfl⟩
  · by_cases hf : f.1 < A.funs.length
    · obtain ⟨f, rfl⟩ : ∃ f', f = aF A B f' := ⟨⟨f.1, hf⟩, rfl⟩
      refine Or.inl ⟨_, Or.inl ⟨f, fun k => t (Fin.cast (ar_aF A B f).symm k), rfl⟩, ?_⟩
      rw [map_sub, map_sum, map_one]
      simp only [rename_X, ιA_gvN]
      rfl
    · obtain ⟨f, rfl⟩ : ∃ f', f = bF A B f' :=
        ⟨⟨f.1 - A.funs.length, by have := f.2; have := join_funs_length A B; omega⟩,
          Fin.ext (by simp only [bF]; omega)⟩
      refine Or.inr (Or.inl ⟨_, Or.inl ⟨f, fun k => t (Fin.cast (ar_bF A B f).symm k), rfl⟩, ?_⟩)
      rw [map_sub, map_sum, map_one]
      simp only [rename_X, ιB_gvN]
      rfl
  · by_cases hf : f.1 < A.funs.length
    · obtain ⟨f, rfl⟩ : ∃ f', f = aF A B f' := ⟨⟨f.1, hf⟩, rfl⟩
      refine Or.inl ⟨_, Or.inr (Or.inl ⟨f, fun k => t (Fin.cast (ar_aF A B f).symm k), j, j', hj,
        rfl⟩), ?_⟩
      rw [map_mul, rename_X, rename_X, ιA_gvN, ιA_gvN]
      rfl
    · obtain ⟨f, rfl⟩ : ∃ f', f = bF A B f' :=
        ⟨⟨f.1 - A.funs.length, by have := f.2; have := join_funs_length A B; omega⟩,
          Fin.ext (by simp only [bF]; omega)⟩
      refine Or.inr (Or.inl ⟨_, Or.inr (Or.inl ⟨f, fun k => t (Fin.cast (ar_bF A B f).symm k), j,
        j', hj, rfl⟩), ?_⟩)
      rw [map_mul, rename_X, rename_X, ιB_gvN, ιB_gvN]
      rfl
  · rcases var_cases A B n v with ⟨u, rfl⟩ | ⟨w, rfl⟩ | ⟨t, rfl⟩
    · exact Or.inl ⟨_, Or.inr (Or.inr ⟨u, rfl⟩), by rw [map_sub, map_pow, rename_X]⟩
    · exact Or.inr (Or.inl ⟨_, Or.inr (Or.inr ⟨w, rfl⟩), by rw [map_sub, map_pow, rename_X]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨t, rfl⟩))
  · rw [join_clauses, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨_, clause_mem A K hc0 ν, ν (nvars c0), ?_⟩)))
      rw [clausePoly_guardN, clausePoly_A A B n ν c0 (hA c0 hc0)]
    · obtain ⟨c1, hc1, rfl⟩ := List.mem_map.mp hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc1
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨_, clause_mem B K hc0 ν,
        ν (nvars (Clause.shift A.rels.length A.funs.length c0)), ?_⟩)))
      rw [clausePoly_guardP, clausePoly_B A B n ν c0 (hB c0 hc0)]

end JoinAxioms

end ClaudeUndec
