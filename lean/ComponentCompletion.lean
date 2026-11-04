import TriangularMatching

namespace SelfContainedCycle075
open MvPolynomial SelfContainedCycle054 SelfContainedCycle058 SelfContainedCycle072 SelfContainedCycle074
open DegreeProfilesReview.PC DegreeProfilesReview.NS
variable {F σ τ : Type*} [Field F]

/-- The previous line-by-line substitution proof applies to arbitrary derived lines. -/
theorem derives_substitution (φ : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)
    (hX : ∀ i, (∃ c, φ (X i)=C c) ∨ ∃ j, φ (X i)=X j)
    {Γ : Set (MvPolynomial σ F)} {Δ : Set (MvPolynomial τ F)}
    (hΓ : ∀ f∈Γ, φ f=0 ∨ φ f∈Δ) {d} {f : MvPolynomial σ F}
    (h : Derives Γ d f) : Derives Δ d (φ f) := by
  obtain ⟨l,hp,hb,hm⟩ := h
  refine ⟨l.map φ,proof_substitution φ hX hΓ hp,?_,List.mem_map_of_mem hm⟩
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  apply (degree_substitution φ ?_ v).trans (hb v hv)
  intro i
  rcases hX i with ⟨c,hc⟩ | ⟨j,hj⟩
  · simp [hc]
  · simp [hj]

/-- Rename an affine polynomial without needing the renaming to be surjective. -/
theorem rename_affine [Fintype σ] [Fintype τ] (f : σ → τ)
    (c : F) (a : σ → F) :
    ∃ (b : τ → F), rename f (C c+∑ i,a i • X i)=C c+∑ j,b j • X j := by
  classical
  refine ⟨fun j => ∑ i, if f i=j then a i else 0,?_⟩
  simp only [map_add,map_sum,map_smul,rename_C,rename_X]
  congr 1
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_smul,zero_smul]
  simp

/-- Put a smaller H system in the first pigeons of a common H system. -/
noncomputable def rowRename {n m : ℕ} (h : ℕ) (hnm : n≤m) :
    MvPolynomial (Var n h) F →ₐ[F] MvPolynomial (Var m h) F :=
  rename (fun v => (labelCast hnm v.1,v.2))
@[simp] theorem rowRename_X {n m h : ℕ} (hnm : n≤m) (v : Var n h) :
    rowRename (F:=F) h hnm (X v)=X (labelCast hnm v.1,v.2) := rename_X _ _

theorem rowRename_axiom {n m h : ℕ} (hnm : n≤m)
    {f : MvPolynomial (Var n h) F} (hf : IsHAxiom n h f) :
    IsHAxiom m h (rowRename h hnm f) := by
  classical
  cases hf with
  | row i =>
    simpa only [rowAxiom,map_sub,map_sum,map_one,rowRename_X]
      using (IsHAxiom.row (F:=F) (h:=h) (labelCast hnm i))
  | boolean v =>
    simpa only [boolAxiom,map_sub,map_pow,rowRename_X]
      using (IsHAxiom.boolean (F:=F) (labelCast hnm v.1,v.2))
  | rowCollision i j k hne =>
    simpa only [map_mul,rowRename_X] using
      (IsHAxiom.rowCollision (F:=F) (labelCast hnm i) j k hne)
  | colCollision i k j hne =>
    simpa only [map_mul,rowRename_X] using
      (IsHAxiom.colCollision (F:=F) (labelCast hnm i) (labelCast hnm k) j
        (fun he => hne (labelCast_injective hnm he)))

noncomputable def triangleToCommon {n m : ℕ} (h : ℕ) (hnm : n≤m) :
    MvPolynomial (TVar n h) F →ₐ[F] MvPolynomial (Var m h) F :=
  (rowRename h hnm).comp (completeT n h)

theorem triangleToCommon_affine {n m h : ℕ} (hnm : n≤m) (v : TVar n h) :
    ∃ (c : F) (b : Var m h → F), triangleToCommon h hnm (X v)=C c+∑ j,b j • X j := by
  obtain ⟨c,a,ha⟩ := completeT_affine (F:=F) v
  obtain ⟨b,hb⟩ := rename_affine (fun v : Var n h => (labelCast hnm v.1,v.2)) c a
  refine ⟨c,b,?_⟩
  change rowRename h hnm (completeT n h (X v))=_
  rw [ha]
  exact hb

theorem triangleToCommon_axiom {n m h : ℕ} (hnm : n≤m)
    {f : MvPolynomial (TVar n h) F} (hf : IsTAxiom n h f) :
    Derives {g : MvPolynomial (Var m h) F | IsHAxiom m h g} 2
      (triangleToCommon h hnm f) := by
  apply derives_substitution (rowRename h hnm) ?_ ?_ (completeT_axiom hf)
  · intro v; exact Or.inr ⟨_,rowRename_X hnm v⟩
  · intro g hg; exact Or.inr (rowRename_axiom hnm hg)

/-- A routed component's intermediate diagonal is a column sum, not a Boolean
    quotient operation. Its Boolean input has an actual degree-two H derivation. -/
theorem column_boolean_derives {n h : ℕ} (i : Label h) :
    Derives {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2
      ((∑ a : Label n,X (a,i))^2-(∑ a : Label n,X (a,i))) := by
  have he : ((∑ a : Label n,(X (a,i) : MvPolynomial (Var n h) F))^2-
      (∑ a : Label n,X (a,i)))=(slack i)^2-slack i := by
    unfold slack
    ring
  rw [he]
  exact slack_boolean_derives i

/-- The two surviving edges at each intermediate vertex are orthogonal in
    degree two: one is the column sum and the other its complement. -/
theorem column_slack_derives {n h : ℕ} (i : Label h) :
    Derives {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2
      ((∑ a : Label n,X (a,i))*slack i) := by
  have he : ((∑ a : Label n,(X (a,i) : MvPolynomial (Var n h) F))*slack i)=
      -((slack i)^2-slack i) := by
    unfold slack
    ring
  rw [he]
  exact (derivable {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2).neg_mem
    (slack_boolean_derives i)

abbrev UVar {κ : Type*} (N : κ → ℕ) (h : ℕ) := (i : κ) × TVar (N i) h
/-- An actual disjoint union of full triangular matching systems of unequal sizes. -/
inductive IsUAxiom {κ : Type*} (N : κ → ℕ) (h : ℕ) : MvPolynomial (UVar N h) F → Prop
  | component (i : κ) (f : MvPolynomial (TVar (N i) h) F) (hf : IsTAxiom (N i) h f) :
      IsUAxiom N h (rename (Sigma.mk i) f)

noncomputable def unionToCommon {κ : Type*} (N : κ → ℕ) (h m : ℕ) (hN : ∀ i,N i≤m) :
    MvPolynomial (UVar N h) F →ₐ[F] MvPolynomial (Var m h) F :=
  aeval (fun v => triangleToCommon h (hN v.1) (X v.2))

@[simp] theorem unionToCommon_component {κ : Type*} (N : κ → ℕ) (h m : ℕ)
    (hN : ∀ i,N i≤m) (i : κ) (f : MvPolynomial (TVar (N i) h) F) :
    unionToCommon N h m hN (rename (Sigma.mk i) f)=triangleToCommon h (hN i) f := by
  have he : (unionToCommon (F:=F) N h m hN).comp (rename (Sigma.mk i))=
      triangleToCommon h (hN i) := by
    ext v
    simp [unionToCommon]
  exact DFunLike.congr_fun he f

/-- Components may share target variables: every input is nevertheless discharged
    in one common hard H system, so no disjoint-union hardness premise is assumed. -/
theorem union_to_H {κ : Type*} (N : κ → ℕ) (h m : ℕ) (hN : ∀ i,N i≤m) {d : ℕ}
    (href : Refutes {f : MvPolynomial (UVar N h) F | IsUAxiom N h f} d) :
    Refutes {f : MvPolynomial (Var m h) F | IsHAxiom m h f} (max 2 d) := by
  apply affine_refutes (unionToCommon N h m hN) ?_ ?_ href
  · intro v
    simpa only [unionToCommon,aeval_X] using triangleToCommon_affine (F:=F) (hN v.1) v.2
  · intro f hf
    cases hf with
    | component i f hf =>
      rw [unionToCommon_component]
      exact triangleToCommon_axiom (hN i) hf

/-- Unconditional original-PC and NS lower bounds for ANY finite collection of
    triangular components, with all sizes and all axiom transports constructed. -/
theorem union_half_linear {κ : Type*} [Fintype κ] (N : κ → ℕ) {p h d : ℕ}
    (hp : p.Prime) [CharP F p] (hh : 4≤h)
    (href : NSRefutes {f : MvPolynomial (UVar N h) F | IsUAxiom N h f} d ∨
      Refutes {f : MvPolynomial (UVar N h) F | IsUAxiom N h f} d) : h<2*d := by
  classical
  have hc : Refutes {f : MvPolynomial (UVar N h) F | IsUAxiom N h f} d :=
    href.elim refutes_of_nsRefutes id
  have hN (i : κ) : N i≤∑ j,N j := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  have hb := H_half_linear hp (by omega : 1≤h) (Or.inr (union_to_H N h (∑ j,N j) hN hc))
  have hd : 2≤d := by
    by_contra! hd
    rw [max_eq_left (by omega : d≤2)] at hb
    omega
  simpa only [max_eq_right hd] using hb
end SelfContainedCycle075
