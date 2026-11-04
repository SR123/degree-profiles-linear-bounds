import AffineTransport
import PigeonholePadding

namespace SelfContainedCycle074
open MvPolynomial SelfContainedCycle054 SelfContainedCycle058 SelfContainedCycle072
open DegreeProfilesReview.PC DegreeProfilesReview.NS
variable {F : Type*} [Field F]

abbrev TVar (n h : ℕ) := Sum (Var n h) (Sum (Var n h) (Var h h))
noncomputable def tx {n h : ℕ} (v : Var n h) : MvPolynomial (TVar n h) F := X (Sum.inl v)
noncomputable def ty {n h : ℕ} (v : Var n h) : MvPolynomial (TVar n h) F := X (Sum.inr (Sum.inl v))
noncomputable def tz {n h : ℕ} (v : Var h h) : MvPolynomial (TVar n h) F := X (Sum.inr (Sum.inr v))

/-- Original matching equations on the allowed blocks A-C, B-C, B-D;
    sizes A=D=n and B=C=h. No quotient, auxiliary premise or missing totality. -/
inductive IsTAxiom (n h : ℕ) : MvPolynomial (TVar n h) F → Prop
  | left (f : MvPolynomial (Var n h) F) (hf : IsHAxiom n h f) :
      IsTAxiom n h (rename Sum.inl f)
  | right (f : MvPolynomial (Var n h) F) (hf : IsHAxiom n h f) :
      IsTAxiom n h (rename (Sum.inr ∘ Sum.inl) f)
  | middleBoolean (v : Var h h) : IsTAxiom n h ((tz v)^2-tz v)
  | middleRow (i j k : Label h) (hne : j≠k) : IsTAxiom n h (tz (i,j)*tz (i,k))
  | middleCol (i k j : Label h) (hne : i≠k) : IsTAxiom n h (tz (i,j)*tz (k,j))
  | rowB (i : Label h) : IsTAxiom n h ((∑ a,ty (a,i))+(∑ j,tz (i,j))-1)
  | colC (i : Label h) : IsTAxiom n h ((∑ a,tx (a,i))+(∑ j,tz (j,i))-1)
  | rowMixed (a : Label n) (i j : Label h) : IsTAxiom n h (ty (a,i)*tz (i,j))
  | colMixed (a : Label n) (i j : Label h) : IsTAxiom n h (tx (a,j)*tz (i,j))

noncomputable def slack {n h : ℕ} (i : Label h) : MvPolynomial (Var n h) F := 1-∑ a,X (a,i)
noncomputable def tValue {n h : ℕ} : TVar n h → MvPolynomial (Var n h) F
  | Sum.inl v => X v
  | Sum.inr (Sum.inl v) => X v
  | Sum.inr (Sum.inr (i,j)) => if i=j then slack i else 0
noncomputable def completeT (n h : ℕ) : MvPolynomial (TVar n h) F →ₐ[F] MvPolynomial (Var n h) F := aeval tValue
@[simp] theorem completeT_X {n h : ℕ} (v : TVar n h) : completeT (F:=F) n h (X v)=tValue v := aeval_X _ _
@[simp] theorem completeT_left {n h : ℕ} (f : MvPolynomial (Var n h) F) :
    completeT n h (rename Sum.inl f)=f := by
  rw [completeT,aeval_rename]
  change aeval X f=f
  simp
@[simp] theorem completeT_right {n h : ℕ} (f : MvPolynomial (Var n h) F) :
    completeT n h (rename (Sum.inr ∘ Sum.inl) f)=f := by
  rw [completeT,aeval_rename]
  change aeval X f=f
  simp

/-- Every original no-onto axiom has degree at most two. -/
theorem H_axiom_derives {n h : ℕ} {f : MvPolynomial (Var n h) F} (hf : IsHAxiom n h f) :
    Derives {f | IsHAxiom n h f} 2 f := by
  have hd : f.totalDegree≤2 := by
    cases hf with
    | row i =>
      apply (totalDegree_sub _ _).trans
      apply max_le _ (by simp)
      apply (totalDegree_finset_sum _ _).trans
      exact Finset.sup_le (fun _ _ => by simp)
    | boolean v =>
      apply (totalDegree_sub _ _).trans
      apply max_le _ (by simp)
      exact (totalDegree_pow _ _).trans (by simp)
    | rowCollision i j k hne => exact (totalDegree_mul _ _).trans (by simp)
    | colCollision i k j hne => exact (totalDegree_mul _ _).trans (by simp)
  exact ⟨[f],IsProof.ax IsProof.nil hf,DegBounded.cons hd (by simp [DegBounded]),by simp⟩

theorem slack_entry_derives {n h : ℕ} (a : Label n) (i : Label h) :
    Derives {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2 (slack i*X (a,i)) := by
  classical
  rw [slack,slack_times_entry]
  change _ ∈ derivable {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2
  apply (derivable {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2).sub_mem
  · exact (derivable {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2).neg_mem (H_axiom_derives (IsHAxiom.boolean (a,i)))
  · apply Submodule.sum_mem
    intro b hb
    exact H_axiom_derives (IsHAxiom.colCollision b a i (Finset.ne_of_mem_erase hb))

theorem slack_boolean_derives {n h : ℕ} (i : Label h) :
    Derives {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2 ((slack i)^2-slack i) := by
  classical
  rw [slack,slack_boolean]
  apply (derivable _ 2).add_mem
  · apply Submodule.sum_mem
    intro a _
    exact H_axiom_derives (IsHAxiom.boolean (a,i))
  · apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro b hb
    exact H_axiom_derives (IsHAxiom.colCollision b a i (Finset.ne_of_mem_erase hb))

/-- Every triangle axiom maps to an actual degree-two H consequence. -/
theorem completeT_axiom {n h : ℕ} {f : MvPolynomial (TVar n h) F} (hf : IsTAxiom n h f) :
    Derives {f | IsHAxiom n h f} 2 (completeT n h f) := by
  classical
  cases hf with
  | left f hf => simpa using H_axiom_derives hf
  | right f hf => simpa using H_axiom_derives hf
  | middleBoolean v =>
    rcases v with ⟨i,j⟩
    simp only [map_sub,map_pow,tz,completeT_X,tValue]
    by_cases he : i=j
    · simpa [he] using slack_boolean_derives (F:=F) j
    · simp only [if_neg he,zero_pow (by decide : 2≠0),sub_zero]
      exact (derivable _ 2).zero_mem
  | middleRow i j k hne =>
    simp only [map_mul,tz,completeT_X,tValue]
    split_ifs with h1 h2 h2
    · exact False.elim (hne (h1.symm.trans h2))
    all_goals simp only [mul_zero,zero_mul]; exact (derivable _ 2).zero_mem
  | middleCol i k j hne =>
    simp only [map_mul,tz,completeT_X,tValue]
    split_ifs with h1 h2 h2
    · exact False.elim (hne (h1.trans h2.symm))
    all_goals simp only [mul_zero,zero_mul]; exact (derivable _ 2).zero_mem
  | rowB i =>
    simp only [map_sub,map_add,map_sum,map_one,ty,tz,completeT_X,tValue]
    convert (derivable {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2).zero_mem using 1
    simp [slack]
  | colC i =>
    simp only [map_sub,map_add,map_sum,map_one,tx,tz,completeT_X,tValue]
    convert (derivable {f : MvPolynomial (Var n h) F | IsHAxiom n h f} 2).zero_mem using 1
    simp [slack]
  | rowMixed a i j =>
    simp only [map_mul,ty,tz,completeT_X,tValue]
    by_cases he : i=j
    · simpa [he,mul_comm] using slack_entry_derives (F:=F) a j
    · simp only [if_neg he,mul_zero]
      exact (derivable _ 2).zero_mem
  | colMixed a i j =>
    simp only [map_mul,tx,tz,completeT_X,tValue]
    by_cases he : i=j
    · simpa [he,mul_comm] using slack_entry_derives (F:=F) a j
    · simp only [if_neg he,mul_zero]
      exact (derivable _ 2).zero_mem

/-- The completion is genuinely affine; coefficients are constructed. -/
theorem completeT_affine {n h : ℕ} (v : TVar n h) :
    ∃ (c : F) (a : Var n h → F), completeT n h (X v)=C c+∑ j,a j • X j := by
  classical
  have hx (v : Var n h) : ∃ (c : F) (a : Var n h → F),
      (X v : MvPolynomial (Var n h) F)=C c+∑ j,a j • X j := by
    refine ⟨0,fun j => if j=v then 1 else 0,?_⟩
    simp
  have hz : ∃ (c : F) (a : Var n h → F),
      (0 : MvPolynomial (Var n h) F)=C c+∑ j,a j • X j := ⟨0,fun _ => 0,by simp⟩
  have hs (i : Label h) : ∃ (c : F) (a : Var n h → F),
      (slack i : MvPolynomial (Var n h) F)=C c+∑ j,a j • X j := by
    refine ⟨1,fun j => if j.2=i then -1 else 0,?_⟩
    simp only [slack,C_1,Fintype.sum_prod_type]
    simp [sub_eq_add_neg,Finset.sum_neg_distrib]
  rw [completeT_X]
  rcases v with v | v
  · exact hx v
  rcases v with v | ⟨i,j⟩
  · exact hx v
  · simp only [tValue]
    split_ifs
    · exact hs i
    · exact hz

/-- Concrete PC transport, with all axioms discharged, not assumed. -/
theorem triangle_to_H {n h d : ℕ}
    (href : Refutes {f : MvPolynomial (TVar n h) F | IsTAxiom n h f} d) :
    Refutes {f : MvPolynomial (Var n h) F | IsHAxiom n h f} (max 2 d) :=
  affine_refutes (completeT n h) completeT_affine (fun _ hf => completeT_axiom hf) href

/-- Reverse transport just uses the A-C copy of the H axioms. -/
theorem H_to_triangle {n h d : ℕ}
    (href : Refutes {f : MvPolynomial (Var n h) F | IsHAxiom n h f} d) :
    Refutes {f : MvPolynomial (TVar n h) F | IsTAxiom n h f} d := by
  apply refutes_substitution (rename Sum.inl) ?_ ?_ href
  · intro v
    exact Or.inr ⟨_,rename_X _ _⟩
  · intro f hf
    exact Or.inr (IsTAxiom.left f hf)

/-- Exact original-PC degree thresholds for every degree at least two. -/
theorem triangle_PC_iff_H {n h d : ℕ} (hd : 2≤d) :
    Refutes {f : MvPolynomial (TVar n h) F | IsTAxiom n h f} d ↔
    Refutes {f : MvPolynomial (Var n h) F | IsHAxiom n h f} d := by
  constructor
  · intro ht
    simpa only [max_eq_right hd] using triangle_to_H ht
  · exact H_to_triangle

/-- A characteristic-independent constant for the actual balanced triangle:
    every NS or ordinary-PC degree is strictly larger than half its inner part. -/
theorem triangle_half_linear {p n h d : ℕ} (hp : p.Prime) [CharP F p]
    (hh : 4≤h)
    (href : NSRefutes {f : MvPolynomial (TVar n h) F | IsTAxiom n h f} d ∨
      Refutes {f : MvPolynomial (TVar n h) F | IsTAxiom n h f} d) :
    h<2*d := by
  have hc : Refutes {f : MvPolynomial (TVar n h) F | IsTAxiom n h f} d :=
    href.elim refutes_of_nsRefutes id
  have hb := H_half_linear hp (by omega : 1≤h) (Or.inr (triangle_to_H hc))
  have hd : 2≤d := by
    by_contra! hd
    rw [max_eq_left (by omega : d≤2)] at hb
    omega
  simpa only [max_eq_right hd] using hb
end SelfContainedCycle074
