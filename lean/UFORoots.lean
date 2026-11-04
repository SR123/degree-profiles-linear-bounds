/-
Claude, 27 Sep 2026.  Undecidability, part A3: the axioms of the translation at size `n`, and
models versus common roots (manuscript `lem:models`).

* `poly_tot`, `poly_coll`, `poly_bool`, `poly_clause`: the actual polynomials of
  `(template φ K).inst n`, identified coefficient by coefficient.
* `model_root`: a model on `Fin n` gives a common `0/1` root.
* `root_model`: for `n ≥ 1`, a common root in `K` gives a model on `Fin n`.  The Boolean
  equations force `0/1` values; for each function symbol and input tuple the collisions allow at
  most one output with value `1` and the totality equation (in any characteristic) forces exactly
  one; so the graph variables define total functions.  A clause product vanishes exactly when a
  literal is true.
* `hasRoot_iff`: for `n ≥ 1`, common root ⟺ model of size `n`.
-/
import UFOCompile

set_option autoImplicit false
open MvPolynomial DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem

namespace ClaudeUndec

variable (φ : Sentence) (K : Type) [Field K] (n : ℕ)

/-! ### The axioms at rank `n` -/

theorem poly_of_coeff {i : (AxSys φ).Rk n} (Q : MvPolynomial ((VarSys φ).Rk n) K)
    (h : ∀ m, Q.coeff m = axCoeff φ K ((AxSys φ).up n i) ((VarSys φ).monUp n m)) :
    (template φ K).poly n i = Q := by
  ext m
  rw [Template.coeff_poly]
  exact (h m).symm

theorem coeff_rename_up (P : MvPolynomial ((VarSys φ).Rk n) K) (m : (VarSys φ).Rk n →₀ ℕ) :
    (rename ((VarSys φ).up n) P).coeff ((VarSys φ).monUp n m) = P.coeff m :=
  coeff_rename_mapDomain _ ((VarSys φ).up_inj n) P m

theorem mem_supp_gvO_last (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → ℕ) (j : ℕ) :
    j ∈ (VarSys φ).supp (gvO φ f t j) := by
  show j ∈ Finset.univ.image (Fin.snoc (α := fun _ => ℕ) t j)
  exact Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, by simp⟩

/-- An object of the form `up w` that is a graph variable with inputs in `[n]` is `gvN`. -/
theorem exists_gvN (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j : ℕ)
    (w : (VarSys φ).Rk n) (hw : (VarSys φ).up n w = gvO φ f (Fin.val ∘ t) j) :
    ∃ j' : Fin n, w = gvN φ n f t j' ∧ j'.val = j := by
  have hj : j < n := by
    have h1 := (VarSys φ).supp_up n w
    rw [hw] at h1
    exact Finset.mem_range.mp (h1 (mem_supp_gvO_last φ f _ j))
  refine ⟨⟨j, hj⟩, (VarSys φ).up_inj n ?_, rfl⟩
  rw [hw, up_gvN]

theorem gvN_inj_out {f : Fin φ.funs.length} {t : Fin (φ.funs.get f) → Fin n} {j j' : Fin n}
    (h : gvN φ n f t j = gvN φ n f t j') : j = j' := by
  have h2 := congrArg ((VarSys φ).up n) h
  rw [up_gvN, up_gvN] at h2
  exact Fin.ext (gvO_injective φ h2).2

theorem poly_tot (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) :
    (template φ K).poly n ⟨Sum.inl f, t⟩ = (∑ j : Fin n, X (gvN φ n f t j)) - 1 := by
  classical
  apply poly_of_coeff
  intro m
  show _ = totCoeff φ K f (Fin.val ∘ t) ((VarSys φ).monUp n m)
  have hup0 : (VarSys φ).monUp n m = 0 ↔ m = 0 := by
    constructor
    · intro h; apply (VarSys φ).monUp_injective n; rw [h]; exact Finsupp.mapDomain_zero.symm
    · rintro rfl; exact Finsupp.mapDomain_zero
  have hsingle : ∀ j : Fin n, (VarSys φ).monUp n (Finsupp.single (gvN φ n f t j) 1) =
      Finsupp.single (gvO φ f (Fin.val ∘ t) j.val) 1 := by
    intro j
    rw [BasisSystem.monUp, Finsupp.mapDomain_single, up_gvN]
  rw [coeff_sub, coeff_sum, coeff_one]
  simp only [coeff_X']
  unfold totCoeff
  by_cases h0 : m = 0
  · subst h0
    rw [if_pos ((hup0).mpr rfl), if_pos rfl]
    simp
  · rw [if_neg (mt hup0.mp h0), if_neg (Ne.symm h0), sub_zero]
    by_cases hex : ∃ j : Fin n, m = Finsupp.single (gvN φ n f t j) 1
    · obtain ⟨j0, rfl⟩ := hex
      rw [if_pos ⟨j0.val, hsingle j0⟩]
      rw [Finset.sum_eq_single j0]
      · simp
      · intro j _ hj
        rw [if_neg]
        intro he
        exact hj (gvN_inj_out φ n (Finsupp.single_left_injective one_ne_zero he))
      · simp
    · rw [if_neg]
      · apply Finset.sum_eq_zero
        intro j _
        rw [if_neg]
        intro he
        exact hex ⟨j, he.symm⟩
      · rintro ⟨j', hj'⟩
        have hsupp : gvO φ f (Fin.val ∘ t) j' ∈ ((VarSys φ).monUp n m).support := by
          rw [hj']; simp
        obtain ⟨w, _, hw⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hsupp)
        obtain ⟨j'', rfl, hj''⟩ := exists_gvN φ n f t j' w hw
        apply hex
        refine ⟨j'', (VarSys φ).monUp_injective n ?_⟩
        rw [hj', hsingle, hj'']

theorem poly_coll (f : Fin φ.funs.length) (b : (collSys (φ.funs.get f)).Rk n) :
    (template φ K).poly n ⟨Sum.inr (Sum.inl f), b⟩ =
      X (gvN φ n f (collIn b.1) (collOut1 b.1)) * X (gvN φ n f (collIn b.1) (collOut2 b.1)) := by
  apply poly_of_coeff
  intro m
  show _ = (collPoly φ K f (Fin.val ∘ b.1)).coeff _
  have e : collPoly φ K f (Fin.val ∘ b.1) = rename ((VarSys φ).up n)
      (X (gvN φ n f (collIn b.1) (collOut1 b.1)) * X (gvN φ n f (collIn b.1) (collOut2 b.1))) := by
    simp only [collPoly, map_mul, rename_X, up_gvN]
    rfl
  rw [e, coeff_rename_up]

theorem poly_bool (v : (VarSys φ).Rk n) :
    (template φ K).poly n ⟨Sum.inr (Sum.inr (Sum.inl ())), v⟩ = X v ^ 2 - X v := by
  apply poly_of_coeff
  intro m
  have key : axCoeff φ K ((AxSys φ).up n ⟨Sum.inr (Sum.inr (Sum.inl ())), v⟩)
      ((VarSys φ).monUp n m) = (X ((VarSys φ).up n v) ^ 2 - X ((VarSys φ).up n v) :
        MvPolynomial (VarSys φ).Obj K).coeff ((VarSys φ).monUp n m) := rfl
  rw [key]
  have e : (X ((VarSys φ).up n v) ^ 2 - X ((VarSys φ).up n v) : MvPolynomial (VarSys φ).Obj K) =
      rename ((VarSys φ).up n) (X v ^ 2 - X v) := by
    simp only [map_sub, map_pow, rename_X]
  rw [e, coeff_rename_up]

theorem poly_clause (c : Fin φ.clauses.length) (σ : Fin (nvars (φ.clauses.get c)) → Fin n) :
    (template φ K).poly n ⟨Sum.inr (Sum.inr (Sum.inr c)), σ⟩ =
      clausePoly φ (rvN φ n) (gvN φ n) (νOf (nvars_pos _) σ) (φ.clauses.get c) := by
  apply poly_of_coeff
  intro m
  show _ = (clauseO φ K c (Fin.val ∘ σ)).coeff _
  have e : clauseO φ K c (Fin.val ∘ σ) = rename ((VarSys φ).up n)
      (clausePoly φ (rvN φ n) (gvN φ n) (νOf (nvars_pos _) σ) (φ.clauses.get c)) := by
    unfold clauseO
    rw [rename_clausePoly φ (rvN φ n) (gvN φ n) (rvO φ) (gvO φ) Fin.val Fin.val_injective
      ((VarSys φ).up n) (fun R t => up_rvN φ n R t) (fun f t j => up_gvN φ n f t j), νOf_comp]
  rw [e, coeff_rename_up]

/-! ### Points of structures -/

section Points
variable {φ K n}
open Classical

theorem ofFn_tupleOf' {β : Type} (ν : ℕ → β) (args : List ℕ) (a : ℕ) (h : a = args.length) :
    List.ofFn (tupleOf ν args a) = args.map ν := by
  subst h; exact ofFn_tupleOf ν args

/-- The `0/1` point of a structure on `Fin n`. -/
noncomputable def ptOf (M : Str (Fin n)) : (VarSys φ).Rk n → K
  | ⟨Sum.inl R, t⟩ => if M.rel R.1 (List.ofFn t) then 1 else 0
  | ⟨Sum.inr f, t⟩ =>
      let t' : Fin (φ.funs.get f + 1) → Fin n := t
      if t' (Fin.last _) = M.fn f.1 (List.ofFn (Fin.init t')) then 1 else 0

theorem ptOf_rvN (M : Str (Fin n)) (R : Fin φ.rels.length) (t : Fin (φ.rels.get R) → Fin n) :
    ptOf (K := K) M (rvN φ n R t) = if M.rel R.1 (List.ofFn t) then 1 else 0 := rfl

theorem ptOf_gvN (M : Str (Fin n)) (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n)
    (j : Fin n) : ptOf (K := K) M (gvN φ n f t j) = if j = M.fn f.1 (List.ofFn t) then 1 else 0 := by
  show (if (Fin.snoc (α := fun _ => Fin n) t j) (Fin.last _) =
      M.fn f.1 (List.ofFn (Fin.init (Fin.snoc (α := fun _ => Fin n) t j))) then 1 else 0) = _
  rw [Fin.snoc_last, Fin.init_snoc]

theorem eval_atomVal (M : Str (Fin n)) (ν : ℕ → Fin n) (a : Atom) :
    eval (ptOf M) (atomVal φ (rvN φ n) (gvN φ n) ν a : MvPolynomial _ K) =
      if atomHolds φ M ν a then 1 else 0 := by
  classical
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · simp only [atomVal, atomHolds]
    by_cases h : R < φ.rels.length ∧ args.length = φ.rels.getD R 0
    · rw [dif_pos h, eval_X, ptOf_rvN]
      have hl : φ.rels.get ⟨R, h.1⟩ = args.length := by
        rw [List.get_eq_getElem, ← List.getD_eq_getElem _ 0 h.1]; exact h.2.symm
      rw [ofFn_tupleOf' ν args _ hl]
      simp only [h.1, h.2, true_and]
    · rw [dif_neg h, map_zero, if_neg]
      rintro ⟨h1, h2, -⟩; exact h ⟨h1, h2⟩
  · simp only [atomVal, atomHolds]
    by_cases h : f < φ.funs.length ∧ args.length = φ.funs.getD f 0
    · rw [dif_pos h, eval_X, ptOf_gvN]
      have hl : φ.funs.get ⟨f, h.1⟩ = args.length := by
        rw [List.get_eq_getElem, ← List.getD_eq_getElem _ 0 h.1]; exact h.2.symm
      rw [ofFn_tupleOf' ν args _ hl]
      simp only [h.1, h.2, true_and]
    · rw [dif_neg h, map_zero, if_neg]
      rintro ⟨h1, h2, -⟩; exact h ⟨h1, h2⟩
  · simp only [atomVal, atomHolds]
    split_ifs <;> simp

theorem eval_litFactor (M : Str (Fin n)) (ν : ℕ → Fin n) (l : Lit) :
    eval (ptOf M) (litFactor φ (rvN φ n) (gvN φ n) ν l : MvPolynomial _ K) =
      if litHolds φ M ν l then 0 else 1 := by
  classical
  unfold litFactor litHolds
  by_cases hl : l.1 = true
  · simp only [hl, if_true, map_sub, map_one, eval_atomVal]
    split_ifs <;> simp
  · simp only [hl, Bool.false_eq_true, if_false, eval_atomVal]
    split_ifs <;> simp_all

theorem eval_clausePoly (M : Str (Fin n)) (ν : ℕ → Fin n) (c : Clause) :
    eval (ptOf M) (clausePoly φ (rvN φ n) (gvN φ n) ν c : MvPolynomial _ K) =
      if clauseHolds φ M ν c then 0 else 1 := by
  classical
  unfold clausePoly clauseHolds
  induction c with
  | nil => simp
  | cons l c ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, eval_litFactor]
    by_cases h1 : litHolds φ M ν l
    · rw [if_pos h1, zero_mul, if_pos ⟨l, List.mem_cons_self, h1⟩]
    · rw [if_neg h1, one_mul]
      by_cases h2 : ∃ l' ∈ c, litHolds φ M ν l'
      · rw [if_pos h2, if_pos]
        obtain ⟨l', hl', h⟩ := h2
        exact ⟨l', List.mem_cons_of_mem _ hl', h⟩
      · rw [if_neg h2, if_neg]
        rintro ⟨l', hl', h⟩
        rcases List.mem_cons.mp hl' with rfl | hl'
        · exact h1 h
        · exact h2 ⟨l', hl', h⟩

theorem ptOf_01 (M : Str (Fin n)) (v : (VarSys φ).Rk n) :
    ptOf (K := K) M v = 0 ∨ ptOf (K := K) M v = 1 := by
  obtain ⟨i, t⟩ := v
  cases i with
  | inl R =>
    by_cases h : M.rel R.1 (List.ofFn t)
    · right; simp [ptOf, h]
    · left; simp [ptOf, h]
  | inr f =>
    by_cases h : (t : Fin (φ.funs.get f + 1) → Fin n) (Fin.last _) =
        M.fn f.1 (List.ofFn (Fin.init (t : Fin (φ.funs.get f + 1) → Fin n)))
    · right; simp only [ptOf]; rw [if_pos h]
    · left; simp only [ptOf]; rw [if_neg h]

/-- **Model ⟹ root.** -/
theorem model_root (M : Str (Fin n)) (hM : IsModel φ M) (i : (AxSys φ).Rk n) :
    eval (ptOf M) ((template φ K).poly n i) = 0 := by
  classical
  obtain ⟨i, u⟩ := i
  rcases i with f | f | ⟨⟩ | c
  · rw [poly_tot]
    simp only [map_sub, map_sum, eval_X, map_one, ptOf_gvN, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, sub_self]
  · rw [poly_coll]
    simp only [map_mul, eval_X, ptOf_gvN]
    have hne : collOut1 u.1 ≠ collOut2 u.1 := by
      intro h
      apply u.2
      show (collOut1 u.1).val = (collOut2 u.1).val
      rw [h]
    split_ifs with h1 h2 <;> simp_all
  · rw [poly_bool]
    simp only [map_sub, map_pow, eval_X]
    rcases ptOf_01 (K := K) M u with h | h <;> rw [h] <;> ring
  · rw [poly_clause, eval_clausePoly, if_pos]
    exact hM _ (List.get_mem _ c) _

/-! ### Root ⟹ model -/

theorem atomHolds_congr (M : Str (Fin n)) {ν ν' : ℕ → Fin n} (a : Atom)
    (h : ∀ v ∈ a.vars, ν v = ν' v) : atomHolds φ M ν a ↔ atomHolds φ M ν' a := by
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · have e : args.map ν = args.map ν' := List.map_congr_left h
    simp only [atomHolds, e]
  · have e : args.map ν = args.map ν' :=
      List.map_congr_left fun v hv => h v (List.mem_cons_of_mem _ hv)
    have eo : ν out = ν' out := h out List.mem_cons_self
    simp only [atomHolds, e, eo]
  · have ei : ν i = ν' i := h i (by simp [Atom.vars])
    have ej : ν j = ν' j := h j (by simp [Atom.vars])
    simp only [atomHolds, ei, ej]

theorem clauseHolds_congr (M : Str (Fin n)) {ν ν' : ℕ → Fin n} (c : Clause)
    (h : ∀ v < nvars c, ν v = ν' v) : clauseHolds φ M ν c ↔ clauseHolds φ M ν' c := by
  have hlit : ∀ l ∈ c, litHolds φ M ν l ↔ litHolds φ M ν' l := by
    intro l hl
    have e := atomHolds_congr (φ := φ) M l.2 (fun v hv => h v (var_lt_nvars hl hv))
    unfold litHolds
    by_cases hb : l.1 = true
    · simp only [hb, if_true]; exact e
    · simp only [hb, Bool.false_eq_true, if_false]; exact not_congr e
  unfold clauseHolds
  constructor
  · rintro ⟨l, hl, hh⟩; exact ⟨l, hl, (hlit l hl).mp hh⟩
  · rintro ⟨l, hl, hh⟩; exact ⟨l, hl, (hlit l hl).mpr hh⟩

/-- A collision index with prescribed input tuple and outputs. -/
def collIdx {a : ℕ} (t : Fin a → Fin n) (j j' : Fin n) : Fin (a + 2) → Fin n :=
  fun k => if h : k.val < a then t ⟨k.val, h⟩ else if k.val = a then j else j'

theorem collIn_collIdx {a : ℕ} (t : Fin a → Fin n) (j j' : Fin n) :
    collIn (collIdx t j j') = t := by
  funext i; simp [collIn, collIdx, i.2]

theorem collOut1_collIdx {a : ℕ} (t : Fin a → Fin n) (j j' : Fin n) :
    collOut1 (collIdx t j j') = j := by
  simp [collOut1, collIdx]

theorem collOut2_collIdx {a : ℕ} (t : Fin a → Fin n) (j j' : Fin n) :
    collOut2 (collIdx t j j') = j' := by
  simp [collOut2, collIdx]

/-- A root is `0/1`-valued. -/
theorem root_bool (x : (VarSys φ).Rk n → K)
    (hx : ∀ i : (AxSys φ).Rk n, eval x ((template φ K).poly n i) = 0) (v : (VarSys φ).Rk n) :
    x v = 0 ∨ x v = 1 := by
  have h := hx ⟨Sum.inr (Sum.inr (Sum.inl ())), v⟩
  rw [poly_bool] at h
  simp only [map_sub, map_pow, eval_X] at h
  have : x v * (x v - 1) = 0 := by rw [← h]; ring
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- At a root, each function symbol and input tuple has exactly one output of value `1`. -/
theorem root_unique (x : (VarSys φ).Rk n → K)
    (hx : ∀ i : (AxSys φ).Rk n, eval x ((template φ K).poly n i) = 0)
    (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) :
    ∃! j, x (gvN φ n f t j) = 1 := by
  have hbool := root_bool x hx
  have hsum : ∑ j : Fin n, x (gvN φ n f t j) = 1 := by
    have h := hx ⟨Sum.inl f, t⟩
    rw [poly_tot] at h
    simp only [map_sub, map_sum, eval_X, map_one] at h
    exact sub_eq_zero.mp h
  have hcoll : ∀ j j', j ≠ j' → x (gvN φ n f t j) * x (gvN φ n f t j') = 0 := by
    intro j j' hjj'
    have hP : (collIdx t j j' ⟨φ.funs.get f, by omega⟩).val ≠
        (collIdx t j j' ⟨φ.funs.get f + 1, by omega⟩).val := by
      have e1 : collIdx t j j' ⟨φ.funs.get f, by omega⟩ = j := collOut1_collIdx t j j'
      have e2 : collIdx t j j' ⟨φ.funs.get f + 1, by omega⟩ = j' := collOut2_collIdx t j j'
      rw [e1, e2]
      exact fun h => hjj' (Fin.ext h)
    have h := hx ⟨Sum.inr (Sum.inl f), ⟨collIdx t j j', hP⟩⟩
    rw [poly_coll] at h
    simpa only [map_mul, eval_X, collIn_collIdx, collOut1_collIdx, collOut2_collIdx] using h
  obtain ⟨j0, hj0⟩ : ∃ j, x (gvN φ n f t j) = 1 := by
    by_contra hno
    push_neg at hno
    have : ∑ j : Fin n, x (gvN φ n f t j) = 0 :=
      Finset.sum_eq_zero fun j _ => (hbool _).resolve_right (hno j)
    rw [hsum] at this
    exact one_ne_zero this
  refine ⟨j0, hj0, fun j hj => ?_⟩
  by_contra hne
  have := hcoll j j0 hne
  rw [hj, hj0, one_mul] at this
  exact one_ne_zero this

/-- The tuple of a list of labels (default `0`). -/
def tupL (hn : 0 < n) {a : ℕ} (l : List (Fin n)) : Fin a → Fin n := fun i => l.getD i ⟨0, hn⟩

theorem tupL_ofFn (hn : 0 < n) {a : ℕ} (t : Fin a → Fin n) : tupL hn (List.ofFn t) = t := by
  funext i
  simp only [tupL]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The output chosen at a root. -/
noncomputable def rootFn (x : (VarSys φ).Rk n → K)
    (hx : ∀ i : (AxSys φ).Rk n, eval x ((template φ K).poly n i) = 0)
    (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) : Fin n :=
  Classical.choose (root_unique x hx f t).exists

/-- The structure of a root. -/
noncomputable def rootStr (hn : 0 < n) (x : (VarSys φ).Rk n → K)
    (hx : ∀ i : (AxSys φ).Rk n, eval x ((template φ K).poly n i) = 0) : Str (Fin n) where
  rel R l := if h : R < φ.rels.length then x (rvN φ n ⟨R, h⟩ (tupL hn l)) = 1 else False
  fn f l := if h : f < φ.funs.length then rootFn x hx ⟨f, h⟩ (tupL hn l) else ⟨0, hn⟩

theorem root_eq_ptOf (hn : 0 < n) (x : (VarSys φ).Rk n → K)
    (hx : ∀ i : (AxSys φ).Rk n, eval x ((template φ K).poly n i) = 0) (v : (VarSys φ).Rk n) :
    x v = ptOf (K := K) (rootStr hn x hx) v := by
  obtain ⟨i, t⟩ := v
  cases i with
  | inl R =>
    show x (rvN φ n R t) = ptOf (rootStr hn x hx) (rvN φ n R t)
    rw [ptOf_rvN]
    have hrel : (rootStr hn x hx).rel R.1 (List.ofFn t) ↔ x (rvN φ n R t) = 1 := by
      simp only [rootStr, dif_pos R.2, tupL_ofFn]
    by_cases h : x (rvN φ n R t) = 1
    · rw [if_pos (hrel.mpr h), h]
    · rw [if_neg (mt hrel.mp h)]
      exact (root_bool x hx _).resolve_right h
  | inr f =>
    let t' : Fin (φ.funs.get f + 1) → Fin n := t
    have ht : (Sigma.mk (β := fun i => (tuples (vArity φ i)).Rk n) (Sum.inr f) t :
        (VarSys φ).Rk n) = gvN φ n f (Fin.init t') (t' (Fin.last _)) := by
      show _ = Sigma.mk (β := fun i => (tuples (vArity φ i)).Rk n) (Sum.inr f)
        (Fin.snoc (α := fun _ => Fin n) (Fin.init t') (t' (Fin.last _)))
      rw [Fin.snoc_init_self]
    rw [ht, ptOf_gvN]
    have hfn : (rootStr hn x hx).fn f.1 (List.ofFn (Fin.init t')) = rootFn x hx f (Fin.init t') := by
      simp only [rootStr, dif_pos f.2, tupL_ofFn]
    rw [hfn]
    have hspec := Classical.choose_spec (root_unique x hx f (Fin.init t')).exists
    by_cases h : t' (Fin.last _) = rootFn x hx f (Fin.init t')
    · rw [if_pos h, h]; exact hspec
    · rw [if_neg h]
      refine (root_bool x hx _).resolve_right fun h1 => h ?_
      exact (root_unique x hx f (Fin.init t')).unique h1 hspec

/-- **Root ⟹ model**, for `n ≥ 1`. -/
theorem root_model (hn : 0 < n) (x : (VarSys φ).Rk n → K)
    (hx : ∀ i : (AxSys φ).Rk n, eval x ((template φ K).poly n i) = 0) :
    IsModel φ (rootStr hn x hx) := by
  intro c hc ν
  obtain ⟨ci, rfl⟩ := List.get_of_mem hc
  let σ : Fin (nvars (φ.clauses.get ci)) → Fin n := fun k => ν k.val
  have h := hx ⟨Sum.inr (Sum.inr (Sum.inr ci)), σ⟩
  rw [poly_clause] at h
  have hx' : x = ptOf (K := K) (rootStr hn x hx) := funext (root_eq_ptOf hn x hx)
  rw [hx', eval_clausePoly] at h
  have hh : clauseHolds φ (rootStr hn x hx) (νOf (nvars_pos _) σ) (φ.clauses.get ci) := by
    split_ifs at h with hc'
    · exact hc'
    · exact absurd h one_ne_zero
  refine (clauseHolds_congr _ _ fun v hv => ?_).mp hh
  show νOf _ σ v = ν v
  rw [νOf, dif_pos hv]

variable (φ K) in
/-- **Models and roots** (manuscript `lem:models`): for `n ≥ 1` the translation at size `n`
has a common root in `K` iff the sentence has a model of size `n`. -/
theorem hasRoot_iff (hn : 0 < n) :
    (∃ x : (VarSys φ).Rk n → K, ∀ f ∈ (template φ K).inst n, eval x f = 0) ↔
      HasModelOfSize φ n := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, root_model hn x fun i => hx _ ⟨i, rfl⟩⟩
  · rintro ⟨M, hM⟩
    refine ⟨ptOf M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact model_root M hM i

end Points

end ClaudeUndec
