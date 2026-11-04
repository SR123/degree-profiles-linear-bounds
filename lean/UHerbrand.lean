/-
Claude, 27 Sep 2026.  Undecidability, part C1: the finite-term certificate (manuscript
`lem:Herbrand` and `cor:large-models`), proved directly, without compactness.

Fix a well-formed normalized sentence `φ`, a field `K` and a universe size `n ≥ 1`.  A *term DAG*
is a finite list of nodes; node `k` applies the function symbol `sym k` to earlier nodes
`args k`.  A *labeling* `α` assigns a label to each node.  Its graph monomial is

    q_α = Π_k x^{sym k}_{α(args k), α(k)}.

Telescoping with the totality equations gives `Σ_α q_α - 1` in NS degree `m` (the number of
nodes).  A labeling that is not functionally consistent contains a collision.  For a consistent
labeling, the named labels together with a fixed finite set `D` of further labels carry a
*partial structure*: the relation atoms over these labels are expanded into Boolean monomials
`u_β`, and the functions are defined only where a node says so.  If no such partial structure
satisfies all clause instances whose function applications are defined (`LocSat`), each
`q_α u_β` lies in the NS span at a degree independent of `n`:

    NS degree ≤ m + Σ_R (m + |D|)^{ar R} + maxWidth φ.

The semantic hypothesis is purely local and finite; for `θ_M` it is proved in `UHalt`.
-/
import UConj

set_option autoImplicit false
open MvPolynomial DegreeProfilesReview.NS DegreeProfilesReview.Uniform

namespace ClaudeUndec

/-! ### Partial structures and local satisfaction -/

/-- A partial structure: a domain predicate, relations, and partial functions. -/
structure PStr (U : Type) where
  dom : U → Prop
  rel : ℕ → List U → Prop
  fn : ℕ → List U → Option U

section PStrDefs
variable {U : Type} (φ : Sentence) (S : PStr U) (σ : ℕ → U)

def atomHoldsP : Atom → Prop
  | Sum.inl (R, args) =>
      R < φ.rels.length ∧ args.length = φ.rels.getD R 0 ∧ S.rel R (args.map σ)
  | Sum.inr (Sum.inl ((f, args), out)) =>
      f < φ.funs.length ∧ args.length = φ.funs.getD f 0 ∧ S.fn f (args.map σ) = some (σ out)
  | Sum.inr (Sum.inr (i, j)) => σ i = σ j

def litHoldsP (l : Lit) : Prop := if l.1 then atomHoldsP φ S σ l.2 else ¬ atomHoldsP φ S σ l.2

/-- A function application is defined. -/
def Defined : Atom → Prop
  | Sum.inr (Sum.inl ((f, args), _)) => ∃ y, S.fn f (args.map σ) = some y
  | _ => True

/-- Local satisfaction: every clause instance with values in the domain and all of whose function
applications are defined has a true literal. -/
def LocSat : Prop :=
  ∀ c ∈ φ.clauses, ∀ σ : ℕ → U, (∀ v < nvars c, S.dom (σ v)) →
    (∀ l ∈ c, Defined S σ l.2) → ∃ l ∈ c, litHoldsP φ S σ l

end PStrDefs

theorem atomHoldsP_congr {U : Type} (φ : Sentence) (S : PStr U) {ν ν' : ℕ → U} (a : Atom)
    (h : ∀ v ∈ a.vars, ν v = ν' v) : atomHoldsP φ S ν a ↔ atomHoldsP φ S ν' a := by
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · have e : args.map ν = args.map ν' := List.map_congr_left h
    simp only [atomHoldsP, e]
  · have e : args.map ν = args.map ν' :=
      List.map_congr_left fun v hv => h v (List.mem_cons_of_mem _ hv)
    have eo : ν out = ν' out := h out List.mem_cons_self
    simp only [atomHoldsP, e, eo]
  · have ei : ν i = ν' i := h i (by simp [Atom.vars])
    have ej : ν j = ν' j := h j (by simp [Atom.vars])
    simp only [atomHoldsP, ei, ej]

theorem defined_congr {U : Type} (S : PStr U) {ν ν' : ℕ → U} (a : Atom)
    (h : ∀ v ∈ a.vars, ν v = ν' v) : Defined S ν a ↔ Defined S ν' a := by
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · rfl
  · have e : args.map ν = args.map ν' :=
      List.map_congr_left fun v hv => h v (List.mem_cons_of_mem _ hv)
    simp only [Defined, e]
  · rfl

/-- A total structure as a partial one. -/
def Str.toP {U : Type} (M : Str U) : PStr U :=
  ⟨fun _ => True, M.rel, fun f l => some (M.fn f l)⟩

theorem locSat_of_model {U : Type} (φ : Sentence) (M : Str U) (hM : IsModel φ M) :
    LocSat φ M.toP := by
  intro c hc σ _ _
  obtain ⟨l, hl, hh⟩ := hM c hc σ
  refine ⟨l, hl, ?_⟩
  have key : atomHoldsP φ M.toP σ l.2 ↔ atomHolds φ M σ l.2 := by
    rcases l with ⟨s, ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩⟩
    · rfl
    · simp only [atomHoldsP, atomHolds, Str.toP, Option.some.injEq]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨a, b, c.symm⟩
      · rintro ⟨a, b, c⟩; exact ⟨a, b, c.symm⟩
    · rfl
  unfold litHoldsP
  unfold litHolds at hh
  by_cases hb : l.1 = true
  · rw [if_pos hb] at hh ⊢; exact key.mpr hh
  · rw [if_neg hb] at hh ⊢; exact fun h => hh (key.mp h)

/-! ### Term DAGs and graph monomials -/

/-- A term DAG: node `k` applies the function symbol `sym k` to the nodes `args k`. -/
structure DAG where
  sym : ℕ → ℕ
  args : ℕ → List ℕ

/-- The first `m` nodes are well formed and refer only to earlier nodes. -/
def DAG.Valid (φ : Sentence) (G : DAG) (m : ℕ) : Prop :=
  ∀ k < m, G.sym k < φ.funs.length ∧ (G.args k).length = φ.funs.getD (G.sym k) 0 ∧
    ∀ a ∈ G.args k, a < k

section Cert
variable (φ : Sentence) (K : Type) [Field K] {n : ℕ} (hn : 0 < n) (G : DAG)

open Classical in
/-- The graph variable `x^f_{l,j}` (or `1` if `f` is not a function symbol). -/
noncomputable def gX (f : ℕ) (l : List (Fin n)) (j : Fin n) : MvPolynomial ((VarSys φ).Rk n) K :=
  if h : f < φ.funs.length then X (gvN φ n ⟨f, h⟩ (tupL hn l) j) else 1

/-- The label of node `a` (default `0` beyond the labeled nodes). -/
def av {m : ℕ} (α : Fin m → Fin n) (a : ℕ) : Fin n :=
  if h : a < m then α ⟨a, h⟩ else ⟨0, hn⟩

/-- The input labels of node `k`. -/
def nodeIn {m : ℕ} (α : Fin m → Fin n) (k : ℕ) : List (Fin n) := (G.args k).map (av hn α)

/-- The graph monomial of a labeling. -/
noncomputable def qP {m : ℕ} (α : Fin m → Fin n) : MvPolynomial ((VarSys φ).Rk n) K :=
  ∏ k : Fin m, gX φ K hn (G.sym k) (nodeIn hn G α k) (α k)

theorem totalDegree_gX (f : ℕ) (l : List (Fin n)) (j : Fin n) :
    (gX φ K hn f l j).totalDegree ≤ 1 := by
  unfold gX
  split_ifs
  · exact totalDegree_X_le' _
  · simp

theorem totalDegree_qP {m : ℕ} (α : Fin m → Fin n) : (qP φ K hn G α).totalDegree ≤ m := by
  unfold qP
  refine le_trans (totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum fun k _ => totalDegree_gX φ K hn _ _ _) ?_
  simp

theorem gX_tot {f : ℕ} (hf : f < φ.funs.length) (l : List (Fin n)) :
    (∑ j : Fin n, gX φ K hn f l j) - 1 ∈ (template φ K).inst n := by
  have e : (∑ j : Fin n, gX φ K hn f l j) - 1 =
      (template φ K).poly n ⟨Sum.inl ⟨f, hf⟩, tupL hn l⟩ := by
    rw [poly_tot]
    simp only [gX, dif_pos hf]
  rw [e]
  exact ⟨_, rfl⟩

theorem gX_coll {f : ℕ} (hf : f < φ.funs.length) (l : List (Fin n)) {j j' : Fin n}
    (hjj : j ≠ j') : gX φ K hn f l j * gX φ K hn f l j' ∈ (template φ K).inst n := by
  let t : Fin (φ.funs.get ⟨f, hf⟩) → Fin n := tupL hn l
  have hP : (collIdx t j j' ⟨φ.funs.get ⟨f, hf⟩, by omega⟩).val ≠
      (collIdx t j j' ⟨φ.funs.get ⟨f, hf⟩ + 1, by omega⟩).val := by
    have e1 : collIdx t j j' ⟨φ.funs.get ⟨f, hf⟩, by omega⟩ = j := collOut1_collIdx t j j'
    have e2 : collIdx t j j' ⟨φ.funs.get ⟨f, hf⟩ + 1, by omega⟩ = j' := collOut2_collIdx t j j'
    rw [e1, e2]
    exact fun h => hjj (Fin.ext h)
  have e : gX φ K hn f l j * gX φ K hn f l j' =
      (template φ K).poly n ⟨Sum.inr (Sum.inl ⟨f, hf⟩), ⟨collIdx t j j', hP⟩⟩ := by
    rw [poly_coll]
    simp only [gX, dif_pos hf, collIn_collIdx, collOut1_collIdx, collOut2_collIdx]
    rfl
  rw [e]
  exact ⟨_, rfl⟩

theorem bool_mem (v : (VarSys φ).Rk n) : (X v ^ 2 - X v : MvPolynomial _ K) ∈ (template φ K).inst n := by
  rw [← poly_bool φ K n v]
  exact ⟨_, rfl⟩

/-! #### Telescoping -/

theorem av_snoc {m : ℕ} (α : Fin m → Fin n) (j : Fin n) {a : ℕ} (ha : a < m) :
    av hn (Fin.snoc (α := fun _ => Fin n) α j) a = av hn α a := by
  unfold av
  rw [dif_pos ha, dif_pos (by omega : a < m + 1)]
  have e : (⟨a, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨a, ha⟩ := rfl
  rw [e, Fin.snoc_castSucc]

theorem nodeIn_snoc {m : ℕ} (α : Fin m → Fin n) (j : Fin n) {k : ℕ}
    (hk : ∀ a ∈ G.args k, a < m) :
    nodeIn hn G (Fin.snoc (α := fun _ => Fin n) α j) k = nodeIn hn G α k := by
  unfold nodeIn
  apply List.map_congr_left
  intro a ha
  exact av_snoc hn α j (hk a ha)

theorem qP_snoc {m : ℕ} (hG : G.Valid φ (m + 1)) (α : Fin m → Fin n) (j : Fin n) :
    qP φ K hn G (Fin.snoc (α := fun _ => Fin n) α j) =
      qP φ K hn G α * gX φ K hn (G.sym m) (nodeIn hn G α m) j := by
  unfold qP
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc]
    rw [nodeIn_snoc hn G α j (fun a ha => lt_trans ((hG k (by omega)).2.2 a ha) k.2)]
  · simp only [Fin.val_last, Fin.snoc_last]
    rw [nodeIn_snoc hn G α j (fun a ha => (hG m (by omega)).2.2 a ha)]

/-- **Telescoping**: `Σ_α q_α - 1` has NS degree at most the number of nodes. -/
theorem sum_qP_sub_one : ∀ m : ℕ, G.Valid φ m →
    (∑ α : Fin m → Fin n, qP φ K hn G α) - 1 ∈ NSspan ((template φ K).inst n) m
  | 0, _ => by
    have : (∑ α : Fin 0 → Fin n, qP φ K hn G α) = 1 := by
      rw [Fintype.sum_unique]
      simp [qP]
    rw [this, sub_self]
    exact Submodule.zero_mem _
  | m + 1, hG => by
    have hG' : G.Valid φ m := fun k hk => hG k (by omega)
    have ih := sum_qP_sub_one m hG'
    have hsym := (hG m (by omega)).1
    rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    have hs : ∀ (x : Fin n) (y : Fin m → Fin n),
        (Fin.snocEquiv (fun _ => Fin n)) (x, y) = Fin.snoc (α := fun _ => Fin n) y x :=
      fun _ _ => rfl
    simp only [hs, qP_snoc φ K hn G hG, ← Finset.mul_sum]
    have e : ∀ α' : Fin m → Fin n, qP φ K hn G α' *
        (∑ j : Fin n, gX φ K hn (G.sym m) (nodeIn hn G α' m) j) =
        qP φ K hn G α' + qP φ K hn G α' *
          ((∑ j : Fin n, gX φ K hn (G.sym m) (nodeIn hn G α' m) j) - 1) := by
      intro α'; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, add_sub_right_comm]
    refine add_mem (NSspan_mono' (by omega) ih) (Submodule.sum_mem _ fun α' _ => ?_)
    have htot := gX_tot φ K hn hsym (nodeIn hn G α' m)
    have hdeg : ((∑ j : Fin n, gX φ K hn (G.sym m) (nodeIn hn G α' m) j) - 1).totalDegree ≤ 1 := by
      refine le_trans (totalDegree_sub _ _) (max_le ?_ (by simp))
      refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun j _ => ?_)
      exact totalDegree_gX φ K hn _ _ _
    have h1 := NSspan_mono' hdeg (mem_NSspan_of_mem htot)
    have h2 := mul_mem_NSspan_of h1 (totalDegree_qP φ K hn G α')
    exact NSspan_mono' (by omega) h2

/-! #### Inconsistent labelings -/

/-- Functional consistency of a labeling. -/
def Cons {m : ℕ} (α : Fin m → Fin n) : Prop :=
  ∀ k k' : Fin m, G.sym k = G.sym k' → nodeIn hn G α k = nodeIn hn G α k' → α k = α k'

theorem qP_mem_of_not_cons {m : ℕ} (hG : G.Valid φ m) (α : Fin m → Fin n)
    (h : ¬ Cons hn G α) : qP φ K hn G α ∈ NSspan ((template φ K).inst n) m := by
  classical
  unfold Cons at h
  push_neg at h
  obtain ⟨k, k', hs, hin, hne⟩ := h
  have hkk : k ≠ k' := fun e => hne (by rw [e])
  have hf := (hG k k.2).1
  set F : Fin m → MvPolynomial ((VarSys φ).Rk n) K :=
    fun i => gX φ K hn (G.sym i) (nodeIn hn G α i) (α i) with hF
  have e1 : qP φ K hn G α = F k * (F k' * ∏ i ∈ (Finset.univ.erase k).erase k', F i) := by
    unfold qP
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hkk, Finset.mem_univ k'⟩)]
  have e2 : F k * F k' = gX φ K hn (G.sym k) (nodeIn hn G α k) (α k) *
      gX φ K hn (G.sym k) (nodeIn hn G α k) (α k') := by
    simp only [hF, hs, hin]
  have hc := gX_coll φ K hn hf (nodeIn hn G α k) hne
  rw [← e2] at hc
  rw [e1, ← mul_assoc]
  have hcd : (F k * F k').totalDegree ≤ 2 := by
    refine le_trans (totalDegree_mul _ _) ?_
    have := totalDegree_gX φ K hn (G.sym k) (nodeIn hn G α k) (α k)
    have := totalDegree_gX φ K hn (G.sym k') (nodeIn hn G α k') (α k')
    simp only [hF]; omega
  have hrest : (∏ i ∈ (Finset.univ.erase k).erase k', F i).totalDegree ≤ m - 2 := by
    refine le_trans (totalDegree_finset_prod _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => totalDegree_gX φ K hn _ _ _) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨Ne.symm hkk, Finset.mem_univ k'⟩),
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hm2 : 2 ≤ m := by
    have := k.2; have := k'.2
    rcases Nat.lt_or_ge k.val k'.val with h | h
    · omega
    · have : k.val ≠ k'.val := fun e => hkk (Fin.ext e); omega
  rw [mul_comm]
  have := mul_mem_NSspan_of (NSspan_mono' hcd (mem_NSspan_of_mem hc)) hrest
  exact NSspan_mono' (by omega) this

end Cert

/-! ### Relation atoms and the partial structure of a labeling -/

section Cert2
variable (φ : Sentence) (K : Type) [Field K] {n : ℕ} (hn : 0 < n) (G : DAG)
open Classical

/-- The labels named by a labeling, together with the extra labels `D`. -/
noncomputable def Eset {m : ℕ} (α : Fin m → Fin n) (D : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.image α ∪ D

theorem card_Eset_le {m : ℕ} (α : Fin m → Fin n) (D : Finset (Fin n)) :
    (Eset α D).card ≤ m + D.card := by
  unfold Eset
  refine le_trans (Finset.card_union_le _ _) ?_
  have := Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := α)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The relation variables all of whose labels lie in `E`. -/
noncomputable def Vset (E : Finset (Fin n)) : Finset ((VarSys φ).Rk n) :=
  Finset.univ.biUnion fun R : Fin φ.rels.length =>
    (Fintype.piFinset fun _ : Fin (φ.rels.get R) => E).image (rvN φ n R)

theorem rvN_mem_Vset (E : Finset (Fin n)) (R : Fin φ.rels.length)
    (t : Fin (φ.rels.get R) → Fin n) (ht : ∀ i, t i ∈ E) : rvN φ n R t ∈ Vset φ E :=
  Finset.mem_biUnion.mpr ⟨R, Finset.mem_univ _, Finset.mem_image.mpr
    ⟨t, Fintype.mem_piFinset.mpr ht, rfl⟩⟩

/-- The number of relation atoms over `e` labels. -/
def atomBound (e : ℕ) : ℕ := ∑ R : Fin φ.rels.length, e ^ (φ.rels.get R)

theorem card_Vset_le (E : Finset (Fin n)) : (Vset φ E).card ≤ atomBound φ E.card := by
  unfold Vset atomBound
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun R _ => ?_)
  refine le_trans Finset.card_image_le ?_
  rw [Fintype.card_piFinset]
  simp

theorem atomBound_mono {e e' : ℕ} (h : e ≤ e') : atomBound φ e ≤ atomBound φ e' :=
  Finset.sum_le_sum fun _ _ => Nat.pow_le_pow_left h _

/-- The Boolean monomial of a truth assignment `β ⊆ W` to the relation variables in `W`. -/
noncomputable def uP (W β : Finset ((VarSys φ).Rk n)) : MvPolynomial ((VarSys φ).Rk n) K :=
  (∏ v ∈ β, X v) * ∏ v ∈ W \ β, (1 - X v)

theorem sum_uP (W : Finset ((VarSys φ).Rk n)) : ∑ β ∈ W.powerset, uP φ K W β = 1 := by
  unfold uP
  rw [← Finset.prod_add]
  simp

theorem totalDegree_uP {W β : Finset ((VarSys φ).Rk n)} (hβ : β ⊆ W) :
    (uP φ K W β).totalDegree ≤ W.card := by
  unfold uP
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 : (∏ v ∈ β, (X v : MvPolynomial ((VarSys φ).Rk n) K)).totalDegree ≤ β.card := by
    refine le_trans (totalDegree_finset_prod _ _) ?_
    refine le_trans (Finset.sum_le_sum fun v _ => totalDegree_X_le' (K := K) v) ?_
    simp
  have h2 : (∏ v ∈ W \ β, (1 - X v : MvPolynomial ((VarSys φ).Rk n) K)).totalDegree ≤
      (W \ β).card := by
    refine le_trans (totalDegree_finset_prod _ _) ?_
    have hv : ∀ v ∈ W \ β, (1 - X v : MvPolynomial ((VarSys φ).Rk n) K).totalDegree ≤ 1 :=
      fun v _ => le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_X_le' v))
    refine le_trans (Finset.sum_le_sum hv) ?_
    simp
  have h3 := Finset.card_sdiff_add_card_eq_card hβ
  omega

/-- The relations of a truth assignment. -/
def relOf (β : Finset ((VarSys φ).Rk n)) (R : ℕ) (l : List (Fin n)) : Prop :=
  ∃ h : R < φ.rels.length, rvN φ n ⟨R, h⟩ (tupL hn l) ∈ β

/-- The partial structure of a labeling `α`, extra labels `D` and truth assignment `β`. -/
noncomputable def pstrOf {m : ℕ} (α : Fin m → Fin n) (D : Finset (Fin n))
    (β : Finset ((VarSys φ).Rk n)) : PStr (Fin n) where
  dom x := x ∈ Eset α D
  rel := relOf φ hn β
  fn f l := if h : ∃ k : Fin m, G.sym k = f ∧ nodeIn hn G α k = l then some (α h.choose) else none

theorem pstrOf_fn {m : ℕ} (α : Fin m → Fin n) (D : Finset (Fin n))
    (β : Finset ((VarSys φ).Rk n)) {f : ℕ} {l : List (Fin n)} {y : Fin n}
    (h : (pstrOf φ hn G α D β).fn f l = some y) :
    ∃ k : Fin m, G.sym k = f ∧ nodeIn hn G α k = l ∧ α k = y := by
  simp only [pstrOf] at h
  split_ifs at h with h'
  · exact ⟨h'.choose, h'.choose_spec.1, h'.choose_spec.2, Option.some.inj h⟩

theorem pstrOf_fn_node {m : ℕ} (α : Fin m → Fin n) (hα : Cons hn G α) (D : Finset (Fin n))
    (β : Finset ((VarSys φ).Rk n)) (k : Fin m) :
    (pstrOf φ hn G α D β).fn (G.sym k) (nodeIn hn G α k) = some (α k) := by
  have hex : ∃ k' : Fin m, G.sym k' = G.sym k ∧ nodeIn hn G α k' = nodeIn hn G α k := ⟨k, rfl, rfl⟩
  simp only [pstrOf, dif_pos hex]
  exact congrArg some (hα _ _ hex.choose_spec.1 hex.choose_spec.2)

theorem mem_Eset {m : ℕ} (α : Fin m → Fin n) (D : Finset (Fin n)) (k : Fin m) :
    α k ∈ Eset α D :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

/-! #### Atom values under the translation -/

theorem tupleOf_eq_tupL (ν : ℕ → Fin n) (args : List ℕ) {a : ℕ} (ha : a = args.length) :
    tupleOf ν args a = tupL hn (args.map ν) := by
  subst ha
  funext i
  simp only [tupleOf, tupL]
  rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]

theorem atomVal_graph (ν : ℕ → Fin n) {f : ℕ} {args : List ℕ} (out : ℕ)
    (hf : f < φ.funs.length) (hl : args.length = φ.funs.getD f 0) :
    atomVal (K := K) φ (rvN φ n) (gvN φ n) ν (Atom.graph f args out) =
      gX φ K hn f (args.map ν) (ν out) := by
  have ha : φ.funs.get ⟨f, hf⟩ = args.length := by
    rw [hl, List.getD_eq_getElem _ _ hf]; rfl
  simp only [atomVal, dif_pos (And.intro hf hl), gX, dif_pos hf]
  rw [tupleOf_eq_tupL hn ν args ha]

theorem atomVal_rel (ν : ℕ → Fin n) {R : ℕ} {args : List ℕ}
    (hR : R < φ.rels.length) (hl : args.length = φ.rels.getD R 0) :
    atomVal (K := K) φ (rvN φ n) (gvN φ n) ν (Atom.rel R args) =
      X (rvN φ n ⟨R, hR⟩ (tupL hn (args.map ν))) := by
  have ha : φ.rels.get ⟨R, hR⟩ = args.length := by
    rw [hl, List.getD_eq_getElem _ _ hR]; rfl
  simp only [atomVal, dif_pos (And.intro hR hl)]
  rw [tupleOf_eq_tupL hn ν args ha]

end Cert2

/-! ### Falsified clause instances and the degree bound -/

section Cert3
variable (φ : Sentence) (K : Type) [Field K] {n : ℕ} (hn : 0 < n) (G : DAG)
open Classical

/-- Telescoping over the factors of a clause product. -/
theorem mul_one_sub_prod {σ : Type} {Γ : Set (MvPolynomial σ K)} (P : MvPolynomial σ K) (d : ℕ) :
    ∀ L : List (MvPolynomial σ K),
      (∀ F ∈ L, P * (1 - F) ∈ NSspan Γ (d + 1) ∧ F.totalDegree ≤ 1) →
      P * (1 - L.prod) ∈ NSspan Γ (d + L.length)
  | [], _ => by simp
  | F :: L, h => by
    have ih := mul_one_sub_prod P d L (fun F' hF' => h F' (List.mem_cons_of_mem _ hF'))
    obtain ⟨h1, h2⟩ := h F List.mem_cons_self
    have e : P * (1 - (F :: L).prod) = P * (1 - F) + F * (P * (1 - L.prod)) := by
      rw [List.prod_cons]; ring
    rw [e, List.length_cons]
    refine add_mem (NSspan_mono' (by omega) h1) ?_
    have := mul_mem_NSspan_of ih h2
    exact NSspan_mono' (by omega) this

theorem qP_split {m : ℕ} (α : Fin m → Fin n) (k : Fin m) :
    ∃ r, qP φ K hn G α = gX φ K hn (G.sym k) (nodeIn hn G α k) (α k) * r ∧
      r.totalDegree + 1 ≤ m := by
  refine ⟨∏ i ∈ Finset.univ.erase k, gX φ K hn (G.sym i) (nodeIn hn G α i) (α i),
    (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm, ?_⟩
  refine le_trans (Nat.add_le_add_right (le_trans (totalDegree_finset_prod _ _)
    (Finset.sum_le_sum fun i _ => totalDegree_gX φ K hn _ _ _)) 1) ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ, Fintype.card_fin]
  have := k.2
  omega

theorem uP_split_in {W β : Finset ((VarSys φ).Rk n)} (hβ : β ⊆ W) {v : (VarSys φ).Rk n}
    (hv : v ∈ β) : ∃ r, uP φ K W β = X v * r ∧ r.totalDegree + 1 ≤ W.card := by
  refine ⟨(∏ w ∈ β.erase v, X w) * ∏ w ∈ W \ β, (1 - X w), ?_, ?_⟩
  · unfold uP
    rw [← Finset.mul_prod_erase _ _ hv, mul_assoc]
  · have h1 : (∏ w ∈ β.erase v, (X w : MvPolynomial ((VarSys φ).Rk n) K)).totalDegree ≤
        (β.erase v).card := by
      refine le_trans (totalDegree_finset_prod _ _) ?_
      refine le_trans (Finset.sum_le_sum fun w _ => totalDegree_X_le' (K := K) w) ?_
      simp
    have h2 : (∏ w ∈ W \ β, (1 - X w : MvPolynomial ((VarSys φ).Rk n) K)).totalDegree ≤
        (W \ β).card := by
      refine le_trans (totalDegree_finset_prod _ _) ?_
      have hw : ∀ w ∈ W \ β, (1 - X w : MvPolynomial ((VarSys φ).Rk n) K).totalDegree ≤ 1 :=
        fun w _ => le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_X_le' w))
      refine le_trans (Finset.sum_le_sum hw) ?_
      simp
    have h3 := Finset.card_sdiff_add_card_eq_card hβ
    have h4 := Finset.card_erase_add_one hv
    refine le_trans (Nat.add_le_add_right (totalDegree_mul _ _) 1) ?_
    omega

theorem uP_split_out {W β : Finset ((VarSys φ).Rk n)} (hβ : β ⊆ W) {v : (VarSys φ).Rk n}
    (hv : v ∈ W) (hvb : v ∉ β) :
    ∃ r, uP φ K W β = (1 - X v) * r ∧ r.totalDegree + 1 ≤ W.card := by
  have hv' : v ∈ W \ β := Finset.mem_sdiff.mpr ⟨hv, hvb⟩
  refine ⟨(∏ w ∈ β, X w) * ∏ w ∈ (W \ β).erase v, (1 - X w), ?_, ?_⟩
  · unfold uP
    rw [← Finset.mul_prod_erase _ _ hv']
    ring
  · have h1 : (∏ w ∈ β, (X w : MvPolynomial ((VarSys φ).Rk n) K)).totalDegree ≤ β.card := by
      refine le_trans (totalDegree_finset_prod _ _) ?_
      refine le_trans (Finset.sum_le_sum fun w _ => totalDegree_X_le' (K := K) w) ?_
      simp
    have h2 : (∏ w ∈ (W \ β).erase v, (1 - X w : MvPolynomial ((VarSys φ).Rk n) K)).totalDegree ≤
        ((W \ β).erase v).card := by
      refine le_trans (totalDegree_finset_prod _ _) ?_
      have hw : ∀ w ∈ (W \ β).erase v,
          (1 - X w : MvPolynomial ((VarSys φ).Rk n) K).totalDegree ≤ 1 :=
        fun w _ => le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_X_le' w))
      refine le_trans (Finset.sum_le_sum hw) ?_
      simp
    have h3 := Finset.card_sdiff_add_card_eq_card hβ
    have h4 := Finset.card_erase_add_one hv'
    refine le_trans (Nat.add_le_add_right (totalDegree_mul _ _) 1) ?_
    omega

theorem bool_mem_deg (v : (VarSys φ).Rk n) :
    (X v ^ 2 - X v : MvPolynomial ((VarSys φ).Rk n) K).totalDegree ≤ 2 :=
  le_trans (totalDegree_sub _ _) (max_le (le_trans (totalDegree_pow _ _)
    (by have := totalDegree_X_le' (K := K) v; omega)) (le_trans (totalDegree_X_le' v) (by omega)))

/-- **One literal.**  A false literal of an instance is absorbed by `q_α u_β`. -/
theorem lit_step {m : ℕ} (α : Fin m → Fin n) (D : Finset (Fin n))
    (β : Finset ((VarSys φ).Rk n)) (hβ : β ⊆ Vset φ (Eset α D)) (ν : ℕ → Fin n) (l : Lit)
    (hwf : AtomWF φ l.2) (hdom : ∀ v ∈ l.2.vars, ν v ∈ Eset α D)
    (hdef : Defined (pstrOf φ hn G α D β) ν l.2)
    (hfalse : ¬ litHoldsP φ (pstrOf φ hn G α D β) ν l) :
    qP φ K hn G α * uP φ K (Vset φ (Eset α D)) β *
      (1 - litFactor (K := K) φ (rvN φ n) (gvN φ n) ν l) ∈
      NSspan ((template φ K).inst n) (m + (Vset φ (Eset α D)).card + 1) := by
  set W := Vset φ (Eset α D) with hW
  obtain ⟨s, a⟩ := l
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · -- a relation atom
    obtain ⟨hR, hl⟩ := hwf
    set v := rvN φ n ⟨R, hR⟩ (tupL hn (args.map ν)) with hv
    have hvW : v ∈ W := by
      apply rvN_mem_Vset
      intro i
      have hi : i.val < args.length := by
        have := i.2
        have e : φ.rels.get ⟨R, hR⟩ = args.length := by
          rw [hl, List.getD_eq_getElem _ _ hR]; rfl
        omega
      simp only [tupL]
      rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_map]
      exact hdom _ (List.getElem_mem hi)
    have hval := atomVal_rel φ K hn ν hR hl
    have hhold : atomHoldsP φ (pstrOf φ hn G α D β) ν (Atom.rel R args) ↔ v ∈ β := by
      simp only [atomHoldsP, pstrOf, relOf]
      constructor
      · rintro ⟨_, _, _, h⟩; exact h
      · intro h; exact ⟨hR, hl, hR, h⟩
    cases s
    · -- negative literal: the relation is true, so `v ∈ β`
      have hin : v ∈ β := by
        have := hfalse
        simp only [litHoldsP, Bool.false_eq_true, if_false, not_not] at this
        exact hhold.mp this
      obtain ⟨r, hr, hdr⟩ := uP_split_in φ K hβ hin
      have e : qP φ K hn G α * uP φ K W β *
          (1 - litFactor (K := K) φ (rvN φ n) (gvN φ n) ν (false, Atom.rel R args)) =
          -((qP φ K hn G α * r) * (X v ^ 2 - X v)) := by
        simp only [litFactor, Bool.false_eq_true, if_false]
        rw [hval, hr]; ring
      rw [e]
      refine Submodule.neg_mem _ (mul_mem_NSspan (bool_mem φ K v) ?_)
      have := le_trans (totalDegree_mul (qP φ K hn G α) r)
        (Nat.add_le_add (totalDegree_qP φ K hn G α) (le_refl _))
      have := bool_mem_deg φ K v
      omega
    · -- positive literal: the relation is false, so `v ∉ β`
      have hout : v ∉ β := by
        have := hfalse
        simp only [litHoldsP, if_true] at this
        exact fun h => this (hhold.mpr h)
      obtain ⟨r, hr, hdr⟩ := uP_split_out φ K hβ hvW hout
      have e : qP φ K hn G α * uP φ K W β *
          (1 - litFactor (K := K) φ (rvN φ n) (gvN φ n) ν (true, Atom.rel R args)) =
          -((qP φ K hn G α * r) * (X v ^ 2 - X v)) := by
        simp only [litFactor, if_true]
        rw [hval, hr]; ring
      rw [e]
      refine Submodule.neg_mem _ (mul_mem_NSspan (bool_mem φ K v) ?_)
      have := le_trans (totalDegree_mul (qP φ K hn G α) r)
        (Nat.add_le_add (totalDegree_qP φ K hn G α) (le_refl _))
      have := bool_mem_deg φ K v
      omega
  · -- a graph atom
    obtain ⟨hf, hl⟩ := hwf
    obtain ⟨y, hy⟩ := hdef
    obtain ⟨k, hks, hkin, hky⟩ := pstrOf_fn φ hn G α D β hy
    obtain ⟨r, hr, hdr⟩ := qP_split φ K hn G α k
    rw [hks, hkin, hky] at hr
    have hval := atomVal_graph φ K hn ν out hf hl
    have hdu := totalDegree_uP φ K hβ
    cases s
    · -- negative literal: the application is true, so `y = ν out`
      have hyo : y = ν out := by
        have := hfalse
        simp only [litHoldsP, Bool.false_eq_true, if_false, not_not, atomHoldsP] at this
        rw [hy] at this
        exact Option.some.inj this.2.2
      set w := gvN φ n ⟨f, hf⟩ (tupL hn (args.map ν)) y
      have hgw : gX φ K hn f (args.map ν) y = X w := by simp only [gX, dif_pos hf]; rfl
      have e : qP φ K hn G α * uP φ K W β *
          (1 - litFactor (K := K) φ (rvN φ n) (gvN φ n) ν (false, Atom.graph f args out)) =
          -((r * uP φ K W β) * (X w ^ 2 - X w)) := by
        simp only [litFactor, Bool.false_eq_true, if_false]
        rw [hval, hr, ← hyo, hgw]; ring
      rw [e]
      refine Submodule.neg_mem _ (mul_mem_NSspan (bool_mem φ K w) ?_)
      have := totalDegree_mul r (uP φ K W β)
      have := bool_mem_deg φ K w
      omega
    · -- positive literal: the application is false, so `y ≠ ν out`
      have hyo : y ≠ ν out := by
        intro h
        apply hfalse
        simp only [litHoldsP, if_true, atomHoldsP]
        exact ⟨hf, hl, by rw [hy, h]⟩
      have e : qP φ K hn G α * uP φ K W β *
          (1 - litFactor (K := K) φ (rvN φ n) (gvN φ n) ν (true, Atom.graph f args out)) =
          (r * uP φ K W β) * (gX φ K hn f (args.map ν) y * gX φ K hn f (args.map ν) (ν out)) := by
        simp only [litFactor, if_true]
        rw [hval, hr]; ring
      rw [e]
      refine mul_mem_NSspan (gX_coll φ K hn hf _ hyo) ?_
      have := totalDegree_mul r (uP φ K W β)
      have : (gX φ K hn f (args.map ν) y * gX φ K hn f (args.map ν) (ν out)).totalDegree ≤ 2 :=
        le_trans (totalDegree_mul _ _) (by
          have := totalDegree_gX φ K hn f (args.map ν) y
          have := totalDegree_gX φ K hn f (args.map ν) (ν out)
          omega)
      omega
  · -- an equality atom: its factor is `1`
    have hz : 1 - litFactor (K := K) φ (rvN φ n) (gvN φ n) ν (s, Atom.eq i j) = 0 := by
      cases s
      · have h : ν i = ν j := by
          have := hfalse
          simp only [litHoldsP, Bool.false_eq_true, if_false, not_not, atomHoldsP] at this
          exact this
        simp [litFactor, atomVal, h]
      · have h : ν i ≠ ν j := by
          have := hfalse
          simp only [litHoldsP, if_true, atomHoldsP] at this
          exact this
        simp [litFactor, atomVal, h]
    rw [hz, mul_zero]
    exact Submodule.zero_mem _

/-- **A falsified clause instance** makes `q_α u_β` NS-derivable at a degree independent of
the universe. -/
theorem qu_mem (hwf : WF φ) {m : ℕ} (α : Fin m → Fin n) (D : Finset (Fin n))
    (β : Finset ((VarSys φ).Rk n)) (hβ : β ⊆ Vset φ (Eset α D)) {c : Clause}
    (hc : c ∈ φ.clauses) (σ : ℕ → Fin n) (hdom : ∀ v < nvars c, σ v ∈ Eset α D)
    (hdef : ∀ l ∈ c, Defined (pstrOf φ hn G α D β) σ l.2)
    (hfalse : ∀ l ∈ c, ¬ litHoldsP φ (pstrOf φ hn G α D β) σ l) :
    qP φ K hn G α * uP φ K (Vset φ (Eset α D)) β ∈
      NSspan ((template φ K).inst n) (m + (Vset φ (Eset α D)).card + c.length) := by
  set W := Vset φ (Eset α D) with hW
  set Pq := qP φ K hn G α * uP φ K W β with hPq
  obtain ⟨ci, rfl⟩ := List.get_of_mem hc
  set c := φ.clauses.get ci with hcdef
  let σ' : Fin (nvars c) → Fin n := fun v => σ v.val
  set ν := νOf (nvars_pos c) σ' with hνdef
  have hν : ∀ v < nvars c, ν v = σ v := fun v hv => by
    simp only [hνdef, νOf, dif_pos hv, σ']
  have hax : clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c ∈ (template φ K).inst n :=
    ⟨⟨Sum.inr (Sum.inr (Sum.inr ci)), σ'⟩, poly_clause φ K n ci σ'⟩
  have hvars : ∀ l ∈ c, ∀ v ∈ l.2.vars, ν v = σ v := fun l hl v hv => hν v (var_lt_nvars hl hv)
  have hdeg : Pq.totalDegree ≤ m + W.card :=
    le_trans (totalDegree_mul _ _)
      (Nat.add_le_add (totalDegree_qP φ K hn G α) (totalDegree_uP φ K hβ))
  -- the clause axiom times `q u`
  have h1 : Pq * clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c ∈
      NSspan ((template φ K).inst n) (m + W.card + c.length) := by
    rw [mul_comm]
    have := totalDegree_clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c
    exact mul_comm Pq _ ▸ mul_mem_NSspan hax (by omega)
  -- `q u` times one minus the clause product
  have h2 : Pq * (1 - clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c) ∈
      NSspan ((template φ K).inst n) (m + W.card + c.length) := by
    have := mul_one_sub_prod K Pq (m + W.card) (c.map (litFactor (K := K) φ (rvN φ n) (gvN φ n) ν))
      (by
        intro F hF
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hF
        refine ⟨?_, totalDegree_litFactor φ _ _ ν l⟩
        have hwfl := hwf c (List.get_mem _ _) l hl
        refine lit_step φ K hn G α D β hβ ν l hwfl ?_ ?_ ?_
        · intro v hv; rw [hvars l hl v hv]; exact hdom v (var_lt_nvars hl hv)
        · exact (defined_congr _ l.2 (hvars l hl)).mpr (hdef l hl)
        · intro h
          apply hfalse l hl
          unfold litHoldsP at h ⊢
          have e := atomHoldsP_congr φ (pstrOf φ hn G α D β) l.2 (hvars l hl)
          by_cases hb : l.1 = true
          · rw [if_pos hb] at h ⊢; exact e.mp h
          · rw [if_neg hb] at h ⊢; exact fun h' => h (e.mpr h'))
    simpa only [List.length_map, clausePoly] using this
  have e : Pq = Pq * clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c +
      Pq * (1 - clausePoly (K := K) φ (rvN φ n) (gvN φ n) ν c) := by ring
  rw [e]
  exact add_mem h1 h2

/-- **The finite-term certificate.**  If for every consistent labeling of an `m`-node term DAG
and every truth assignment the resulting partial structure (named labels plus the labels `D`)
fails local satisfaction, then the translation at size `n` has an NS refutation of degree
`m + Σ_R (m + |D|)^{ar R} + maxWidth φ`, independent of `n`. -/
theorem nsRefutes_of_local (hwf : WF φ) {m : ℕ} (hG : G.Valid φ m) (D : Finset (Fin n))
    (hloc : ∀ α : Fin m → Fin n, Cons hn G α → ∀ β : Finset ((VarSys φ).Rk n),
      ¬ LocSat φ (pstrOf φ hn G α D β)) :
    NSRefutes ((template φ K).inst n) (m + atomBound φ (m + D.card) + maxWidth φ) := by
  rw [nsRefutes_iff_one_mem_NSspan]
  set B := m + atomBound φ (m + D.card) + maxWidth φ with hB
  have hS : (∑ α : Fin m → Fin n, qP φ K hn G α) ∈ NSspan ((template φ K).inst n) B := by
    refine Submodule.sum_mem _ fun α _ => ?_
    by_cases hα : Cons hn G α
    · set W := Vset φ (Eset α D)
      rw [← mul_one (qP φ K hn G α), ← sum_uP φ K W, Finset.mul_sum]
      refine Submodule.sum_mem _ fun β hβ => ?_
      have hβW : β ⊆ W := Finset.mem_powerset.mp hβ
      have h := hloc α hα β
      unfold LocSat at h
      push_neg at h
      obtain ⟨c, hc, σ, hdom, hdef, hfalse⟩ := h
      have hmem := qu_mem φ K hn G hwf α D β hβW hc σ hdom hdef hfalse
      refine NSspan_mono' ?_ hmem
      have h1 := card_Vset_le φ (Eset α D)
      have h2 := atomBound_mono φ (card_Eset_le α D)
      have h3 : c.length ≤ maxWidth φ := le_foldr_max _ _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
      omega
    · exact NSspan_mono' (by omega) (qP_mem_of_not_cons φ K hn G hG α hα)
  have hT := NSspan_mono' (show m ≤ B by omega) (sum_qP_sub_one φ K hn G m hG)
  have := sub_mem hS hT
  rwa [sub_sub_cancel] at this

end Cert3

end ClaudeUndec
