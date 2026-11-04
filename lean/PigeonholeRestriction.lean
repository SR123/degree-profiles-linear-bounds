import RectangularPC
import Mathlib.Data.Nat.Log

namespace SelfContainedCycle072
open MvPolynomial SelfContainedCycle054 SelfContainedCycle058
open DegreeProfilesReview.PC DegreeProfilesReview.NS

variable {F σ τ : Type*} [Field F]

/-- A degree-one substitution does not increase actual polynomial degree. -/
theorem degree_substitution (φ : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)
    (hX : ∀ i, (φ (X i)).totalDegree ≤ 1) (f : MvPolynomial σ F) :
    (φ f).totalDegree ≤ f.totalDegree := by
  classical
  have hm (μ : σ →₀ ℕ) (c : F) : (φ (monomial μ c)).totalDegree ≤ μ.sum (fun _ e => e) := by
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have hc : φ (C c)=C c := φ.commutes c
    rw [hc]
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    apply (totalDegree_finset_prod _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [map_pow]
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (μ i) (hX i))
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  apply (totalDegree_finset_sum _ _).trans
  exact Finset.sup_le (fun μ hμ => (hm μ _).trans (le_totalDegree hμ))

/-- Substitutions by constants or variables transport every ordinary-PC line, including cancellations. -/
theorem proof_substitution (φ : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)
    (hX : ∀ i, (∃ c, φ (X i)=C c) ∨ ∃ j, φ (X i)=X j)
    {Γ : Set (MvPolynomial σ F)} {Δ : Set (MvPolynomial τ F)}
    (hΓ : ∀ f∈Γ, φ f=0 ∨ φ f∈Δ) {l} (hl : IsProof Γ l) :
    IsProof Δ (l.map φ) := by
  induction hl with
  | nil => exact IsProof.nil
  | ax _ hf ih =>
    rcases hΓ _ hf with hz | ha
    · simp only [List.map_cons, hz]
      exact IsProof.lin ih (Submodule.zero_mem _)
    · exact IsProof.ax ih ha
  | @lin l f _ hf ih =>
    apply IsProof.lin ih
    have hh : Submodule.span F {g | g ∈ l} ≤
        (Submodule.span F {g | g ∈ List.map φ l}).comap φ.toLinearMap := by
      apply Submodule.span_le.mpr
      intro g hg
      exact Submodule.subset_span (List.mem_map_of_mem hg)
    exact hh hf
  | @mulX l g i _ hg ih =>
    simp only [List.map_cons, map_mul]
    rcases hX i with ⟨c,hc⟩ | ⟨j,hj⟩
    · rw [hc, ← smul_eq_C_mul]
      exact IsProof.lin ih (Submodule.smul_mem _ c (Submodule.subset_span (List.mem_map_of_mem hg)))
    · rw [hj]
      exact IsProof.mulX j ih (List.mem_map_of_mem hg)

theorem refutes_substitution (φ : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)
    (hX : ∀ i, (∃ c, φ (X i)=C c) ∨ ∃ j, φ (X i)=X j)
    {Γ : Set (MvPolynomial σ F)} {Δ : Set (MvPolynomial τ F)}
    (hΓ : ∀ f∈Γ, φ f=0 ∨ φ f∈Δ) {d} (h : Refutes Γ d) : Refutes Δ d := by
  obtain ⟨l,hp,hb,hm⟩ := h
  refine ⟨l.map φ,proof_substitution φ hX hΓ hp,?_,?_⟩
  · intro g hg
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    apply (degree_substitution φ ?_ f).trans (hb f hf)
    intro i
    rcases hX i with ⟨c,hc⟩ | ⟨j,hj⟩
    · simp [hc]
    · simp [hj]
  · simpa only [map_one] using List.mem_map_of_mem (f:=φ) hm

/-- Functional injective pigeonhole axioms: no column totality equations. -/
inductive IsHAxiom (n h : ℕ) : MvPolynomial (Var n h) F → Prop
  | row (i : Label n) : IsHAxiom n h (rowAxiom i)
  | boolean (v : Var n h) : IsHAxiom n h (boolAxiom v)
  | rowCollision (i : Label n) (j k : Label h) (hne : j≠k) : IsHAxiom n h (X (i,j)*X (i,k))
  | colCollision (i k : Label n) (j : Label h) (hne : i≠k) : IsHAxiom n h (X (i,j)*X (k,j))

noncomputable def holeValue {n h : ℕ} (r : ℕ) (v : Var n h) : MvPolynomial (Var r n) F :=
  if hj : v.2.val≤r then X (⟨v.2.val,Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp v.2.property).1,hj⟩⟩,v.1) else 0

noncomputable def restrictH (n h r : ℕ) :
    MvPolynomial (Var n h) F →ₐ[F] MvPolynomial (Var r n) F := aeval (holeValue r)

@[simp] theorem restrictH_X {n h r : ℕ} (v : Var n h) :
    restrictH (F:=F) n h r (X v)=holeValue r v := aeval_X _ _

/-- The retained holes are exactly the original smaller label set. -/
theorem sum_holeValue {n h r : ℕ} (hrh : r≤h) (i : Label n) :
    (∑ j : Label h, holeValue (F:=F) r (i,j)) = ∑ j : Label r, X (j,i) := by
  classical
  rw [← Finset.sum_filter_of_ne (p:=fun j : Label h => j.val≤r) (by
    intro j _ hne
    by_contra hj
    exact hne (by simp [holeValue,hj]))]
  apply Finset.sum_bij (fun j hj => (⟨j.val,Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp j.property).1,(Finset.mem_filter.mp hj).2⟩⟩ : Label r))
  · intro _ _; simp
  · intro a ha b hb he; exact Subtype.ext (congrArg (fun x : Label r => x.val) he)
  · intro b _
    refine ⟨⟨b.val,Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp b.property).1,
      (Finset.mem_Icc.mp b.property).2.trans hrh⟩⟩,?_,?_⟩
    · simp [(Finset.mem_Icc.mp b.property).2]
    · rfl
  · intro a ha
    simp only [holeValue, dif_pos (Finset.mem_filter.mp ha).2]

/-- Each actual restricted no-onto axiom is zero or an original rectangular axiom. -/
theorem restrictH_axiom {n h r : ℕ} (hrh : r≤h)
    {f : MvPolynomial (Var n h) F} (hf : IsHAxiom n h f) :
    restrictH n h r f=0 ∨ IsBAxiom r n (restrictH n h r f) := by
  classical
  cases hf with
  | row i =>
    right
    simpa only [rowAxiom, map_sub, map_sum, map_one, restrictH_X, sum_holeValue hrh]
      using (IsBAxiom.col (F:=F) (n:=r) i)
  | boolean v =>
    simp only [boolAxiom, map_sub, map_pow, restrictH_X, holeValue]
    split_ifs
    · exact Or.inr (IsBAxiom.boolean _)
    · simp
  | rowCollision i j k hjk =>
    simp only [map_mul, restrictH_X, holeValue]
    split_ifs with hj hk
    · right
      apply IsBAxiom.colCollision
      intro he
      exact hjk (Subtype.ext (congrArg (fun x : Label r => x.val) he))
    · simp
    · simp
    · simp
  | colCollision i k j hik =>
    simp only [map_mul, restrictH_X, holeValue]
    split_ifs
    · exact Or.inr (IsBAxiom.rowCollision _ _ _ hik)
    · simp

/-- A complete concrete endpoint; no transfer/equivalence/design premise is assumed. -/
theorem no_PCRefutes_H {p a n h r d : ℕ} (hp : p.Prime) [CharP F p]
    (hr : 1≤r) (hsize : 2*d≤r) (hd : d<p^a) (hrn : r≤n)
    (hdiv : p^a∣n-r) (hrh : r≤h) :
    ¬ Refutes {f : MvPolynomial (Var n h) F | IsHAxiom n h f} d := by
  intro href
  apply no_PCRefutes_rectangle (F:=F) hp hr hsize hd hrn hdiv
  apply refutes_substitution (restrictH n h r) ?_ (fun _ hf => restrictH_axiom hrh hf) href
  intro v
  rw [restrictH_X]
  unfold holeValue
  split_ifs
  · exact Or.inr ⟨_,rfl⟩
  · exact Or.inl ⟨0,by simp⟩

/-- Every size n>=3: both no-onto pigeonhole degrees exceed n/(3p).
    The degree is total-product NS degree or maximum ordinary-PC line degree. -/
theorem gap_one_both_linear {p n d : ℕ} (hp : p.Prime) [CharP F p] (hn : 3≤n)
    (href : NSRefutes {f : MvPolynomial (Var n (n-1)) F | IsHAxiom n (n-1) f} d ∨
      Refutes {f : MvPolynomial (Var n (n-1)) F | IsHAxiom n (n-1) f} d) :
    n < 3*p*d := by
  let a := Nat.log p (n/3)
  let q := p^a
  have hqpos : 0<q := pow_pos hp.pos _
  have hqle : q≤n/3 := Nat.pow_log_le_self p (by omega)
  have h3q : 3*q≤n := by omega
  have hqbound : n/3<p*q := by
    simpa only [q,a,pow_succ'] using Nat.lt_pow_succ_log_self hp.one_lt (n/3)
  have hnq : n<3*(p*q) := by omega
  have hqd : q≤d := by
    by_contra! hd
    have hh := no_PCRefutes_H (F:=F) (p:=p) (a:=a) (n:=n) (h:=n-1) (r:=n-q)
      hp (by omega) (by omega) hd (by omega) ?_ (by omega)
    · rcases href with hs | hc
      · exact hh (refutes_of_nsRefutes hs)
      · exact hh hc
    · have he : n-(n-q)=q := by omega
      rw [he]
  have hmul := Nat.mul_le_mul_left (3*p) hqd
  calc n < 3*(p*q) := hnq
       _ = (3*p)*q := by ac_rfl
       _ ≤ 3*p*d := hmul

abbrev GVar (n : ℕ) := Sum (Var n n) (Label n)

/-- The manuscript's fixed first-order graph/sum encoding of an injection omitting a constant. -/
inductive IsGAxiom (n : ℕ) : MvPolynomial (GVar n) F → Prop
  | base (f : MvPolynomial (Var n n) F) (hf : IsHAxiom n n f) :
      IsGAxiom n (rename Sum.inl f)
  | constTotal : IsGAxiom n ((∑ j : Label n, X (Sum.inr j))-1)
  | constBoolean (j : Label n) : IsGAxiom n (X (Sum.inr j)^2-X (Sum.inr j))
  | constCollision (j k : Label n) (hne : j≠k) : IsGAxiom n (X (Sum.inr j)*X (Sum.inr k))
  | guard (i j : Label n) : IsGAxiom n (X (Sum.inl (i,j))*X (Sum.inr j))

noncomputable def gValue {n : ℕ} (r : ℕ) : GVar n → MvPolynomial (Var r n) F
  | Sum.inl v => holeValue r v
  | Sum.inr j => if j.val=n then 1 else 0

noncomputable def restrictG (n r : ℕ) :
    MvPolynomial (GVar n) F →ₐ[F] MvPolynomial (Var r n) F := aeval (gValue r)

@[simp] theorem restrictG_X {n r : ℕ} (v : GVar n) :
    restrictG (F:=F) n r (X v)=gValue r v := aeval_X _ _

@[simp] theorem restrictG_base {n r : ℕ} (f : MvPolynomial (Var n n) F) :
    restrictG n r (rename Sum.inl f)=restrictH (F:=F) n n r f := by
  rw [restrictG,aeval_rename]
  rfl

theorem sum_gValue {n r : ℕ} (hn : 1≤n) :
    (∑ j : Label n, gValue (F:=F) r (Sum.inr j))=1 := by
  classical
  let top : Label n := ⟨n,Finset.mem_Icc.mpr ⟨hn,le_rfl⟩⟩
  have he (j : Label n) : j.val=n ↔ j=top := by
    constructor
    · intro hh; exact Subtype.ext hh
    · intro hh; exact congrArg Subtype.val hh
  simp [gValue,he]

/-- The chosen constant is outside the retained rectangle, so every guard vanishes. -/
theorem restrictG_axiom {n r : ℕ} (hrn : r<n)
    {f : MvPolynomial (GVar n) F} (hf : IsGAxiom n f) :
    restrictG n r f=0 ∨ IsBAxiom r n (restrictG n r f) := by
  classical
  cases hf with
  | base f hf => rw [restrictG_base]; exact restrictH_axiom hrn.le hf
  | constTotal =>
    left
    simp only [map_sub,map_sum,map_one,restrictG_X,sum_gValue (by omega : 1≤n),sub_self]
  | constBoolean j =>
    left
    simp only [map_sub,map_pow,restrictG_X,gValue]
    split_ifs <;> simp
  | constCollision j k hjk =>
    left
    simp only [map_mul,restrictG_X,gValue]
    split_ifs with hj hk
    · exact (hjk (Subtype.ext (hj.trans hk.symm))).elim
    · simp
    · simp
    · simp
  | guard i j =>
    left
    simp only [map_mul,restrictG_X,gValue]
    by_cases hj : j.val=n
    · simp [hj,holeValue,Nat.not_le.mpr hrn]
    · simp [hj]

theorem no_PCRefutes_G {p a n r d : ℕ} (hp : p.Prime) [CharP F p]
    (hr : 1≤r) (hsize : 2*d≤r) (hd : d<p^a) (hrn : r<n)
    (hdiv : p^a∣n-r) :
    ¬ Refutes {f : MvPolynomial (GVar n) F | IsGAxiom n f} d := by
  intro href
  apply no_PCRefutes_rectangle (F:=F) hp hr hsize hd hrn.le hdiv
  apply refutes_substitution (restrictG n r) ?_ (fun _ hf => restrictG_axiom hrn hf) href
  intro v
  rw [restrictG_X]
  cases v with
  | inl v =>
    simp only [gValue,holeValue]
    split_ifs
    · exact Or.inr ⟨_,rfl⟩
    · exact Or.inl ⟨0,by simp⟩
  | inr j =>
    simp only [gValue]
    split_ifs
    · exact Or.inl ⟨1,by simp⟩
    · exact Or.inl ⟨0,by simp⟩

/-- The actual fixed-universe T2 witness has a linear lower bound for both systems,
    over every (possibly infinite) field of any fixed prime characteristic. -/
theorem G_both_linear {p n d : ℕ} (hp : p.Prime) [CharP F p] (hn : 3≤n)
    (href : NSRefutes {f : MvPolynomial (GVar n) F | IsGAxiom n f} d ∨
      Refutes {f : MvPolynomial (GVar n) F | IsGAxiom n f} d) :
    n < 3*p*d := by
  let a := Nat.log p (n/3)
  let q := p^a
  have hqpos : 0<q := pow_pos hp.pos _
  have hqle : q≤n/3 := Nat.pow_log_le_self p (by omega)
  have h3q : 3*q≤n := by omega
  have hqbound : n/3<p*q := by
    simpa only [q,a,pow_succ'] using Nat.lt_pow_succ_log_self hp.one_lt (n/3)
  have hnq : n<3*(p*q) := by omega
  have hqd : q≤d := by
    by_contra! hd
    have hh := no_PCRefutes_G (F:=F) (p:=p) (a:=a) (n:=n) (r:=n-q)
      hp (by omega) (by omega) hd (by omega) ?_
    · rcases href with hs | hc
      · exact hh (refutes_of_nsRefutes hs)
      · exact hh hc
    · have he : n-(n-q)=q := by omega
      rw [he]
  have hmul := Nat.mul_le_mul_left (3*p) hqd
  calc n < 3*(p*q) := hnq
       _ = (3*p)*q := by ac_rfl
       _ ≤ 3*p*d := hmul

/-- Explicit non-vacuous characteristic-two and characteristic-three instances. -/
theorem witness_boundary_examples :
    (¬ Refutes {f : MvPolynomial (GVar 12) (ZMod 2) | IsGAxiom 12 f} 3) ∧
    (¬ Refutes {f : MvPolynomial (GVar 9) (ZMod 3) | IsGAxiom 9 f} 2) := by
  constructor
  · exact no_PCRefutes_G (p:=2) (a:=2) (r:=8) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact no_PCRefutes_G (p:=3) (a:=1) (r:=6) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

end SelfContainedCycle072
