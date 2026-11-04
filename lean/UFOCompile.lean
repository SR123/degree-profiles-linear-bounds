/-
Claude, 27 Sep 2026.  Undecidability, part A2: the graph-and-sum translation of a normalized
sentence, as an actual Stage 5 uniform template.

For a normalized sentence `φ` and universe `[n] = {0, …, n-1}` the translation `Γ_φ(n)` has
Boolean variables `r^R_ī` (relation atoms) and `x^f_{ī,j}` (function graphs, `j` the output),
and the axioms

    totality     Σ_j x^f_{ī,j} - 1,
    collisions   x^f_{ī,j} x^f_{ī,j'}            (j ≠ j'),
    Booleans     z² - z                          (every relation or graph variable z),
    clauses      Π_{L ∈ C} (1 - val(L))          (every clause C and every grounding),

with truth value `1`; a negative literal contributes `val`, a positive one `1 - val`, a domain
equality has value `δ`.  Ill-formed atoms have value `0` (false), matching `UFOSyntax`.

The variables form the basis system `VarSys φ` (a finite sum of tuple systems) and the axiom
indices the basis system `AxSys φ`; `template φ R` is the Stage 5 `Template` with explicit
support bounds `k, s`, degree bound `D` and stabilisation threshold `n0 = k·D + s + 1`.  All
template fields are proved; nothing is assumed.
-/
import UFOSyntax
import DegreeProfilesReview.TemplateExample

set_option autoImplicit false
open MvPolynomial DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem

namespace ClaudeUndec

/-! ### Tuples from argument lists -/

/-- The tuple of labels of an argument list under an assignment (total; it is the intended
tuple when the list has the right length; the default entry is `ν 0`). -/
def tupleOf {β : Type} (ν : ℕ → β) (args : List ℕ) (a : ℕ) : Fin a → β :=
  fun i => (args.map ν).getD i (ν 0)

theorem ofFn_tupleOf {β : Type} (ν : ℕ → β) (args : List ℕ) :
    List.ofFn (tupleOf ν args args.length) = args.map ν := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, tupleOf]
    rw [List.getD_eq_getElem _ _ h2]

theorem totalDegree_X_le' {σ K : Type*} [CommSemiring K] (s : σ) :
    (X s : MvPolynomial σ K).totalDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial K with h | h
  · rw [Subsingleton.elim (X s : MvPolynomial σ K) 0]; simp
  · rw [totalDegree_X]

theorem tupleOf_comp {β γ : Type} (e : β → γ) (ν : ℕ → β) (args : List ℕ) (a : ℕ) :
    tupleOf (e ∘ ν) args a = e ∘ tupleOf ν args a := by
  funext i
  simp only [tupleOf, Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (args[(i : ℕ)]?) <;> rfl

variable (φ : Sentence)

/-! ### The variable basis system -/

/-- Variable kinds: relation symbols (`inl`) and function symbols (`inr`). -/
abbrev VIdx := Fin φ.rels.length ⊕ Fin φ.funs.length

/-- Number of labels of a variable of a given kind. -/
def vArity : VIdx φ → ℕ
  | Sum.inl R => φ.rels.get R
  | Sum.inr f => φ.funs.get f + 1

/-- The variables: `⟨inl R, t⟩` is `r^R_t`, `⟨inr f, t⟩` is `x^f_{init t, last t}`. -/
def VarSys : BasisSystem := sigma fun i : VIdx φ => tuples (vArity φ i)

/-- The largest number of labels of a variable. -/
def maxVArity : ℕ := (φ.rels.foldr max 0) + (φ.funs.foldr max 0) + 1

theorem get_le_foldr_max (l : List ℕ) (i : Fin l.length) : l.get i ≤ l.foldr max 0 :=
  le_foldr_max l _ (List.get_mem l i)

theorem vArity_le (i : VIdx φ) : vArity φ i ≤ maxVArity φ := by
  unfold maxVArity
  cases i with
  | inl R => have := get_le_foldr_max φ.rels R; simp only [vArity]; omega
  | inr f => have := get_le_foldr_max φ.funs f; simp only [vArity]; omega

theorem varSys_bounded : (VarSys φ).Bounded (maxVArity φ) :=
  sigma_bounded fun i => (tuples_bounded _).mono (vArity_le φ i)


/-! ### Clause polynomials, for any label type -/

section Generic
variable {L V : Type} (rv : (R : Fin φ.rels.length) → (Fin (φ.rels.get R) → L) → V)
  (gv : (f : Fin φ.funs.length) → (Fin (φ.funs.get f) → L) → L → V)
  {K : Type} [CommRing K]

open Classical in
/-- The value of an atom (`1` = true) under a label assignment `ν`. -/
noncomputable def atomVal (ν : ℕ → L) : Atom → MvPolynomial V K
  | Sum.inl (R, args) =>
      if h : R < φ.rels.length ∧ args.length = φ.rels.getD R 0 then
        X (rv ⟨R, h.1⟩ (tupleOf ν args _)) else 0
  | Sum.inr (Sum.inl ((f, args), out)) =>
      if h : f < φ.funs.length ∧ args.length = φ.funs.getD f 0 then
        X (gv ⟨f, h.1⟩ (tupleOf ν args _) (ν out)) else 0
  | Sum.inr (Sum.inr (i, j)) => if ν i = ν j then 1 else 0

/-- The factor `1 - val(L)`: `1 - val` for a positive literal, `val` for a negative one. -/
noncomputable def litFactor (ν : ℕ → L) (l : Lit) : MvPolynomial V K :=
  if l.1 then 1 - atomVal φ rv gv ν l.2 else atomVal φ rv gv ν l.2

/-- The clause polynomial `Π_{L ∈ C} (1 - val(L))`. -/
noncomputable def clausePoly (ν : ℕ → L) (c : Clause) : MvPolynomial V K :=
  (c.map (litFactor φ rv gv ν)).prod

theorem totalDegree_atomVal (ν : ℕ → L) (a : Atom) :
    (atomVal (K := K) φ rv gv ν a).totalDegree ≤ 1 := by
  classical
  rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
  · simp only [atomVal]; split_ifs
    · exact (totalDegree_X_le' _)
    · simp
  · simp only [atomVal]; split_ifs
    · exact (totalDegree_X_le' _)
    · simp
  · simp only [atomVal]; split_ifs <;> simp

theorem totalDegree_litFactor (ν : ℕ → L) (l : Lit) :
    (litFactor (K := K) φ rv gv ν l).totalDegree ≤ 1 := by
  unfold litFactor
  split_ifs
  · exact le_trans (totalDegree_sub _ _)
      (max_le (by simp) (totalDegree_atomVal φ rv gv ν l.2))
  · exact totalDegree_atomVal φ rv gv ν l.2

theorem totalDegree_clausePoly (ν : ℕ → L) (c : Clause) :
    (clausePoly (K := K) φ rv gv ν c).totalDegree ≤ c.length := by
  unfold clausePoly
  induction c with
  | nil => simp
  | cons l c ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons]
    exact le_trans (totalDegree_mul _ _)
      (by have := totalDegree_litFactor φ rv gv ν (K := K) l; omega)

/-- Renaming labels injectively and variables compatibly renames clause polynomials. -/
theorem rename_clausePoly {L' V' : Type}
    (rv' : (R : Fin φ.rels.length) → (Fin (φ.rels.get R) → L') → V')
    (gv' : (f : Fin φ.funs.length) → (Fin (φ.funs.get f) → L') → L' → V')
    (e : L → L') (he : Function.Injective e) (ψ : V → V')
    (hr : ∀ R t, ψ (rv R t) = rv' R (e ∘ t)) (hg : ∀ f t j, ψ (gv f t j) = gv' f (e ∘ t) (e j))
    (ν : ℕ → L) (c : Clause) :
    rename ψ (clausePoly (K := K) φ rv gv ν c) = clausePoly φ rv' gv' (e ∘ ν) c := by
  classical
  have hatom : ∀ a, rename ψ (atomVal (K := K) φ rv gv ν a) = atomVal φ rv' gv' (e ∘ ν) a := by
    intro a
    rcases a with ⟨R, args⟩ | ⟨⟨f, args⟩, out⟩ | ⟨i, j⟩
    · simp only [atomVal]
      split_ifs
      · rw [rename_X, hr, tupleOf_comp]
      · simp
    · simp only [atomVal]
      split_ifs
      · rw [rename_X, hg, tupleOf_comp]; rfl
      · simp
    · simp only [atomVal, Function.comp_apply, he.eq_iff]
      split_ifs <;> simp
  unfold clausePoly
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, litFactor]
  split_ifs
  · rw [map_sub, map_one, hatom]
  · rw [hatom]

end Generic

/-! ### Variables of the translation, on all labels and at rank `n` -/

/-- `r^R_t` on labels in `ℕ`. -/
def rvO (R : Fin φ.rels.length) (t : Fin (φ.rels.get R) → ℕ) : (VarSys φ).Obj := ⟨Sum.inl R, t⟩

/-- `x^f_{t,j}` on labels in `ℕ`. -/
def gvO (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → ℕ) (j : ℕ) : (VarSys φ).Obj :=
  ⟨Sum.inr f, Fin.snoc (α := fun _ => ℕ) t j⟩

/-- `r^R_t` at rank `n`. -/
def rvN (n : ℕ) (R : Fin φ.rels.length) (t : Fin (φ.rels.get R) → Fin n) : (VarSys φ).Rk n :=
  ⟨Sum.inl R, t⟩

/-- `x^f_{t,j}` at rank `n`. -/
def gvN (n : ℕ) (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j : Fin n) :
    (VarSys φ).Rk n :=
  ⟨Sum.inr f, Fin.snoc (α := fun _ => Fin n) t j⟩

theorem up_rvN (n : ℕ) (R : Fin φ.rels.length) (t : Fin (φ.rels.get R) → Fin n) :
    (VarSys φ).up n (rvN φ n R t) = rvO φ R (Fin.val ∘ t) := rfl

theorem up_gvN (n : ℕ) (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → Fin n) (j : Fin n) :
    (VarSys φ).up n (gvN φ n f t j) = gvO φ f (Fin.val ∘ t) j.val := by
  show (⟨Sum.inr f, fun k => ((Fin.snoc (α := fun _ => Fin n) t j) k).val⟩ : (VarSys φ).Obj) =
    ⟨Sum.inr f, Fin.snoc (α := fun _ => ℕ) (Fin.val ∘ t) j.val⟩
  congr 1
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc, Function.comp_apply]

theorem smul_rvO (g : Equiv.Perm ℕ) (R : Fin φ.rels.length) (t : Fin (φ.rels.get R) → ℕ) :
    g • rvO φ R t = rvO φ R (g ∘ t) := rfl

theorem smul_gvO (g : Equiv.Perm ℕ) (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → ℕ)
    (j : ℕ) : g • gvO φ f t j = gvO φ f (g ∘ t) (g j) := by
  show (⟨Sum.inr f, fun k => g ((Fin.snoc (α := fun _ => ℕ) t j) k)⟩ : (VarSys φ).Obj) =
    ⟨Sum.inr f, Fin.snoc (α := fun _ => ℕ) (g ∘ t) (g j)⟩
  congr 1
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc, Function.comp_apply]

theorem gvO_injective {f : Fin φ.funs.length} {t t' : Fin (φ.funs.get f) → ℕ} {j j' : ℕ}
    (h : gvO φ f t j = gvO φ f t' j') : t = t' ∧ j = j' := by
  have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  refine ⟨?_, ?_⟩
  · funext i
    have := congrFun h2 (Fin.castSucc i)
    simpa only [Fin.snoc_castSucc] using this
  · have := congrFun h2 (Fin.last _)
    simpa only [Fin.snoc_last] using this

/-! ### The axiom basis system -/

/-- Collision indices: input tuple followed by two distinct outputs. -/
def collSys (a : ℕ) : BasisSystem :=
  (tuples (a + 2)).sub (fun b => b ⟨a, by omega⟩ ≠ b ⟨a + 1, by omega⟩) (fun g b => by
    show g (b ⟨a, _⟩) ≠ g (b ⟨a + 1, _⟩) ↔ _
    rw [Ne, g.injective.eq_iff])

/-- Axiom kinds: totality (per function symbol), collision (per function symbol), Boolean
(one kind, indexed by the variables), clause (per clause). -/
abbrev AIdx := Fin φ.funs.length ⊕ Fin φ.funs.length ⊕ Unit ⊕ Fin φ.clauses.length

def AxComp : AIdx φ → BasisSystem
  | Sum.inl f => tuples (φ.funs.get f)
  | Sum.inr (Sum.inl f) => collSys (φ.funs.get f)
  | Sum.inr (Sum.inr (Sum.inl _)) => VarSys φ
  | Sum.inr (Sum.inr (Sum.inr c)) => tuples (nvars (φ.clauses.get c))

def AxSys : BasisSystem := sigma (AxComp φ)

/-- The largest clause width and the largest number of clause variables. -/
def maxWidth : ℕ := (φ.clauses.map List.length).foldr max 0
def maxNvars : ℕ := (φ.clauses.map nvars).foldr max 0

theorem width_le (c : Fin φ.clauses.length) : (φ.clauses.get c).length ≤ maxWidth φ :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨_, List.get_mem _ c, rfl⟩)

theorem nvars_le (c : Fin φ.clauses.length) : nvars (φ.clauses.get c) ≤ maxNvars φ :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨_, List.get_mem _ c, rfl⟩)

/-- Support bound for axiom indices. -/
def axSupp : ℕ := maxVArity φ + 1 + maxNvars φ

theorem axSys_bounded : (AxSys φ).Bounded (axSupp φ) := by
  apply sigma_bounded
  intro i
  unfold axSupp
  rcases i with f | f | u | c
  · exact (tuples_bounded _).mono (by have := vArity_le φ (Sum.inr f); simp only [vArity] at this; omega)
  · show (collSys (φ.funs.get f)).Bounded _
    exact (BasisSystem.sub_bounded (tuples_bounded (φ.funs.get f + 2)) _ _).mono
      (by have := vArity_le φ (Sum.inr f); simp only [vArity] at this; omega)
  · exact (varSys_bounded φ).mono (by omega)
  · exact (tuples_bounded _).mono (by have := nvars_le φ c; omega)

/-! ### Coefficients of the axioms -/

section Coeff
variable (K : Type) [Field K]

/-- The label assignment of a clause grounding (the variable `0` serves as default). -/
def νOf {β : Type} {m : ℕ} (hm : 0 < m) (σ : Fin m → β) (x : ℕ) : β :=
  if h : x < m then σ ⟨x, h⟩ else σ ⟨0, hm⟩

theorem nvars_pos (c : Clause) : 0 < nvars c := Nat.succ_pos _

theorem νOf_comp {β γ : Type} {m : ℕ} (hm : 0 < m) (e : β → γ) (σ : Fin m → β) :
    νOf hm (e ∘ σ) = e ∘ νOf hm σ := by
  funext x; simp only [νOf, Function.comp_apply]; split_ifs <;> rfl

/-- Input tuple and the two outputs of a collision index. -/
def collIn {a : ℕ} {β : Type} (b : Fin (a + 2) → β) : Fin a → β :=
  fun i => b ⟨i, by omega⟩
def collOut1 {a : ℕ} {β : Type} (b : Fin (a + 2) → β) : β := b ⟨a, by omega⟩
def collOut2 {a : ℕ} {β : Type} (b : Fin (a + 2) → β) : β := b ⟨a + 1, by omega⟩

open Classical in
/-- Totality `Σ_j x^f_{t,j} - 1`, as a coefficient function on all monomials. -/
noncomputable def totCoeff (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → ℕ)
    (m : (VarSys φ).Obj →₀ ℕ) : K :=
  if m = 0 then -1 else if ∃ j, m = Finsupp.single (gvO φ f t j) 1 then 1 else 0

/-- The collision `x^f_{t,j} x^f_{t,j'}`. -/
noncomputable def collPoly (f : Fin φ.funs.length) (b : Fin (φ.funs.get f + 2) → ℕ) :
    MvPolynomial (VarSys φ).Obj K :=
  X (gvO φ f (collIn b) (collOut1 b)) * X (gvO φ f (collIn b) (collOut2 b))

/-- The clause polynomial of clause `c` at grounding `σ`, on all labels. -/
noncomputable def clauseO (c : Fin φ.clauses.length) (σ : Fin (nvars (φ.clauses.get c)) → ℕ) :
    MvPolynomial (VarSys φ).Obj K :=
  clausePoly φ (rvO φ) (gvO φ) (νOf (nvars_pos _) σ) (φ.clauses.get c)

/-- The coefficient function of the translation. -/
noncomputable def axCoeff : (AxSys φ).Obj → ((VarSys φ).Obj →₀ ℕ) → K
  | ⟨Sum.inl f, t⟩, m => totCoeff φ K f t m
  | ⟨Sum.inr (Sum.inl f), b⟩, m => (collPoly φ K f b.1).coeff m
  | ⟨Sum.inr (Sum.inr (Sum.inl _)), v⟩, m => ((X v ^ 2 - X v : MvPolynomial _ K)).coeff m
  | ⟨Sum.inr (Sum.inr (Sum.inr c)), σ⟩, m => (clauseO φ K c σ).coeff m

/-! ### Invariance and degree -/

theorem coeff_rename_smul (g : Equiv.Perm ℕ) (P : MvPolynomial (VarSys φ).Obj K)
    (m : (VarSys φ).Obj →₀ ℕ) :
    (rename (fun v => g • v) P).coeff ((VarSys φ).monSMul g m) = P.coeff m :=
  coeff_rename_mapDomain _ (MulAction.injective g) P m

theorem rename_collPoly (g : Equiv.Perm ℕ) (f : Fin φ.funs.length)
    (b : Fin (φ.funs.get f + 2) → ℕ) :
    rename (fun v => g • v) (collPoly φ K f b) = collPoly φ K f (g ∘ b) := by
  simp only [collPoly, map_mul, rename_X, smul_gvO]
  rfl

theorem rename_clauseO (g : Equiv.Perm ℕ) (c : Fin φ.clauses.length)
    (σ : Fin (nvars (φ.clauses.get c)) → ℕ) :
    rename (fun v => g • v) (clauseO φ K c σ) = clauseO φ K c (g ∘ σ) := by
  unfold clauseO
  rw [rename_clausePoly φ (rvO φ) (gvO φ) (rvO φ) (gvO φ) g g.injective (fun v => g • v)
    (fun R t => smul_rvO φ g R t) (fun f t j => smul_gvO φ g f t j), νOf_comp]

theorem monSMul_single (g : Equiv.Perm ℕ) (v : (VarSys φ).Obj) (e : ℕ) :
    (VarSys φ).monSMul g (Finsupp.single v e) = Finsupp.single (g • v) e :=
  Finsupp.mapDomain_single

theorem totCoeff_inv (g : Equiv.Perm ℕ) (f : Fin φ.funs.length) (t : Fin (φ.funs.get f) → ℕ)
    (m : (VarSys φ).Obj →₀ ℕ) :
    totCoeff φ K f (g ∘ t) ((VarSys φ).monSMul g m) = totCoeff φ K f t m := by
  classical
  have h0 : (VarSys φ).monSMul g m = 0 ↔ m = 0 := by
    constructor
    · intro h
      apply (VarSys φ).monSMul_injective g
      rw [h]; exact Finsupp.mapDomain_zero.symm
    · rintro rfl; exact Finsupp.mapDomain_zero
  have h1 : (∃ j, (VarSys φ).monSMul g m = Finsupp.single (gvO φ f (g ∘ t) j) 1) ↔
      ∃ j, m = Finsupp.single (gvO φ f t j) 1 := by
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨g⁻¹ j, (VarSys φ).monSMul_injective g ?_⟩
      rw [hj, monSMul_single, smul_gvO]
      simp
    · rintro ⟨j, rfl⟩
      exact ⟨g j, by rw [monSMul_single, smul_gvO]⟩
  unfold totCoeff
  rw [if_congr h0 rfl rfl, if_congr h1 rfl rfl]

theorem axCoeff_inv (g : Equiv.Perm ℕ) (i : (AxSys φ).Obj) (m : (VarSys φ).Obj →₀ ℕ) :
    axCoeff φ K (g • i) ((VarSys φ).monSMul g m) = axCoeff φ K i m := by
  obtain ⟨i, u⟩ := i
  rcases i with f | f | _ | c
  · exact totCoeff_inv φ K g f u m
  · show (collPoly φ K f (g ∘ u.1)).coeff _ = (collPoly φ K f u.1).coeff m
    rw [← rename_collPoly, coeff_rename_smul]
  · show ((X (g • u) ^ 2 - X (g • u) : MvPolynomial _ K)).coeff _ =
      ((X u ^ 2 - X u : MvPolynomial _ K)).coeff m
    have e : (X (g • u) ^ 2 - X (g • u) : MvPolynomial _ K) =
        rename (fun v => g • v) (X u ^ 2 - X u) := by
      simp only [map_sub, map_pow, rename_X]
    rw [e]
    exact coeff_rename_smul φ K g _ m
  · show (clauseO φ K c (g ∘ u)).coeff _ = (clauseO φ K c u).coeff m
    rw [← rename_clauseO, coeff_rename_smul]

theorem mdeg_le_of_coeff {P : MvPolynomial (VarSys φ).Obj K} {m : (VarSys φ).Obj →₀ ℕ}
    (h : P.coeff m ≠ 0) : mdeg m ≤ P.totalDegree :=
  le_totalDegree (mem_support_iff.mpr h)

/-- Degree bound of the translation. -/
def degD : ℕ := maxWidth φ + 2

theorem axCoeff_deg (i : (AxSys φ).Obj) (m : (VarSys φ).Obj →₀ ℕ)
    (h : axCoeff φ K i m ≠ 0) : mdeg m ≤ degD φ := by
  classical
  obtain ⟨i, u⟩ := i
  unfold degD
  rcases i with f | f | _ | c
  · change totCoeff φ K f u m ≠ 0 at h
    unfold totCoeff at h
    split_ifs at h with h0 h1
    · subst h0; simp [mdeg]
    · obtain ⟨j, rfl⟩ := h1
      rw [mdeg_single]; omega
    · exact absurd rfl h
  · change (collPoly φ K f u.1).coeff m ≠ 0 at h
    refine le_trans (mdeg_le_of_coeff φ K h) ?_
    unfold collPoly
    exact le_trans (totalDegree_mul _ _)
      (by have := totalDegree_X_le' (K := K) (gvO φ f (collIn u.1) (collOut1 u.1))
          have := totalDegree_X_le' (K := K) (gvO φ f (collIn u.1) (collOut2 u.1)); omega)
  · change ((X u ^ 2 - X u : MvPolynomial _ K)).coeff m ≠ 0 at h
    refine le_trans (mdeg_le_of_coeff φ K h) ?_
    refine le_trans (totalDegree_sub _ _) (max_le ?_ ?_)
    · exact le_trans (totalDegree_pow _ _)
        (by have := totalDegree_X_le' (K := K) u; nlinarith)
    · exact le_trans (totalDegree_X_le' _) (by omega)
  · change (clauseO φ K c u).coeff m ≠ 0 at h
    exact le_trans (mdeg_le_of_coeff φ K h)
      (le_trans (totalDegree_clausePoly φ _ _ _ _) (by have := width_le φ c; omega))

/-- **The graph-and-sum translation as a uniform template** (manuscript `prop:FO`), with
`k = maxVArity`, `s = axSupp`, `D = maxWidth + 2`, `n0 = kD + s + 1`. -/
noncomputable def template : Template K where
  Var := VarSys φ
  Ax := AxSys φ
  k := maxVArity φ
  s := axSupp φ
  D := degD φ
  n0 := maxVArity φ * degD φ + axSupp φ + 1
  hk := by unfold maxVArity; omega
  hn0 := by omega
  hn0' := by omega
  var_bounded := varSys_bounded φ
  ax_bounded := axSys_bounded φ
  coeff := axCoeff φ K
  coeff_inv := axCoeff_inv φ K
  coeff_deg := axCoeff_deg φ K

end Coeff

end ClaudeUndec
