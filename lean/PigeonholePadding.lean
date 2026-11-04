import PigeonholeRestriction

namespace SelfContainedCycle074
open MvPolynomial SelfContainedCycle054 SelfContainedCycle058 SelfContainedCycle072
open DegreeProfilesReview.PC DegreeProfilesReview.NS
variable {F : Type*} [Field F]

def labelCast {n m : ℕ} (hnm : n≤m) (i : Label n) : Label m :=
  ⟨i.val,Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp i.property).1,(Finset.mem_Icc.mp i.property).2.trans hnm⟩⟩
theorem labelCast_injective {n m : ℕ} (hnm : n≤m) : Function.Injective (labelCast hnm) := by
  intro i j hij
  exact Subtype.ext (congrArg (fun v : Label m => v.val) hij)
noncomputable def padH {n m : ℕ} (h : ℕ) (hnm : n≤m) :
    MvPolynomial (Var n h) F →ₐ[F] MvPolynomial (Var h m) F :=
  aeval (fun v => X (v.2,labelCast hnm v.1))
@[simp] theorem padH_X {n m h : ℕ} (hnm : n≤m) (v : Var n h) :
    padH (F:=F) h hnm (X v)=X (v.2,labelCast hnm v.1) := aeval_X _ _

theorem padH_axiom {n m h : ℕ} (hnm : n≤m) {f : MvPolynomial (Var n h) F}
    (hf : IsHAxiom n h f) : IsBAxiom h m (padH h hnm f) := by
  classical
  cases hf with
  | row i =>
    simpa only [rowAxiom,map_sub,map_sum,map_one,padH_X]
      using (IsBAxiom.col (F:=F) (n:=h) (labelCast hnm i))
  | boolean v =>
    simpa only [boolAxiom,map_sub,map_pow,padH_X] using
      (IsBAxiom.boolean (F:=F) (v.2,labelCast hnm v.1))
  | rowCollision i j k hne =>
    simpa only [map_mul,padH_X] using
      (IsBAxiom.colCollision (F:=F) j k (labelCast hnm i) hne)
  | colCollision i k j hne =>
    simpa only [map_mul,padH_X] using
      (IsBAxiom.rowCollision (F:=F) j (labelCast hnm i) (labelCast hnm k)
        (fun he => hne (labelCast_injective hnm he)))

/-- The number of pigeons need not match the hard rectangle's number of columns.
    Padding eliminates all p-adic restrictions on the original instance. -/
theorem no_H_half {p n h d : ℕ} (hp : p.Prime) [CharP F p]
    (hh : 1≤h) (hd : 2*d≤h) :
    ¬ Refutes {f : MvPolynomial (Var n h) F | IsHAxiom n h f} d := by
  let a := Nat.log p d+1
  let q := p^a
  let m := h+q*n
  have hq : 0<q := pow_pos hp.pos _
  have hnq : n≤q*n := by simpa using Nat.mul_le_mul_right n (show 1≤q by omega)
  have hnm : n≤m := by dsimp [m]; omega
  have hhm : h≤m := by dsimp [m]; omega
  have hdiv : p^a∣m-h := by
    change q∣h+q*n-h
    simp
  have hpow : d<p^a := Nat.lt_pow_succ_log_self hp.one_lt d
  intro href
  apply no_PCRefutes_rectangle (F:=F) hp hh hd hpow hhm hdiv
  apply refutes_substitution (padH h hnm) ?_ (fun _ hf => Or.inr (padH_axiom hnm hf)) href
  intro v
  exact Or.inr ⟨_,padH_X hnm v⟩

/-- Every original NS or ordinary-PC refutation has degree strictly above h/2,
    for arbitrary pigeon count and every field of fixed prime characteristic. -/
theorem H_half_linear {p n h d : ℕ} (hp : p.Prime) [CharP F p] (hh : 1≤h)
    (href : NSRefutes {f : MvPolynomial (Var n h) F | IsHAxiom n h f} d ∨
      Refutes {f : MvPolynomial (Var n h) F | IsHAxiom n h f} d) : h<2*d := by
  by_contra! hd
  apply no_H_half (F:=F) (n:=n) hp hh hd
  exact href.elim refutes_of_nsRefutes id
end SelfContainedCycle074
