/-
Claude, 27 Sep 2026.  Undecidability, part L: ordinary PC without the NS–PC comparison.

The PC endpoints of parts H1 and K3 were obtained from the NS endpoints through the uniform
NS–PC comparison (`pcType_iff_nsType`, i.e. `ClaudeComparison.types_agree_linear`).  This file
proves them again directly for ordinary PC, using only witness-specific facts:

* satisfiable-block lemma for PC (`pcDegree_conj_eq_left`), by substituting the root of the
  satisfiable block line by line (variables go to variables or constants);
* the halting block is PC-bounded because PC degree is at most NS degree;
* PC types of the witnesses: `ψ₁` (bounded), `η` (the project's PC lower bound
  `G_both_linear`, through a variable renaming), `ψ₃ = η ∧ χ_p` (`iType3_of`), and `B̂` (the
  project's PC rectangle bound `no_PCRefutes_rectangle`, through the project's affine-substitution
  theorem for actual PC proofs `affine_refutes`);
* the PC guarded-join bounds of `UJoinDeg`.

The periodicity of PC profiles (`LinearFinal.linear_classification`, PC part) is still used, since
the types are defined relative to the linear onset.  The audit checks that the endpoints here do
not depend on `ClaudeComparison.upperComparison`.
-/
import UPairs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open MvPolynomial Nat.Partrec DegreeProfilesReview.Uniform DegreeProfilesReview.NS
open DegreeProfilesReview.PC DegreeProfilesReview.Profiles

/-! ### Conjunctions in ordinary PC -/

section ConjPC
variable (φ ψ : Sentence) (n : ℕ) (K : Type) [Field K]

theorem rename_var {σ τ : Type} (e : σ → τ) (v : σ) :
    (∃ c, rename e (X v : MvPolynomial σ K) = C c) ∨ ∃ j, rename e (X v : MvPolynomial σ K) = X j :=
  Or.inr ⟨e v, rename_X _ _⟩

theorem pcDegree_conj_le_left (hφ : WF φ) :
    pcDegree ((template (conj φ ψ) K).inst n) ≤ pcDegree ((template φ K).inst n) :=
  pcDegree_le_of fun _ h => SelfContainedCycle072.refutes_substitution (rename (ιL φ ψ n))
    (rename_var K _) (fun _ hf => Or.inr (inst_left φ ψ n hφ hf)) h

theorem pcDegree_conj_le_right (hψ : WF ψ) :
    pcDegree ((template (conj φ ψ) K).inst n) ≤ pcDegree ((template ψ K).inst n) :=
  pcDegree_le_of fun _ h => SelfContainedCycle072.refutes_substitution (rename (ιR φ ψ n))
    (rename_var K _) (fun _ hf => Or.inr (inst_right φ ψ n hψ hf)) h

theorem subRoot_X_cases (y : (VarSys ψ).Rk n → K) (v : (VarSys (conj φ ψ)).Rk n) :
    (∃ c, subRoot φ ψ n K y (X v) = C c) ∨ ∃ j, subRoot φ ψ n K y (X v) = X j := by
  classical
  simp only [subRoot, aeval_X]
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inl ⟨0, by simp⟩

/-- **Satisfiable-block lemma, ordinary PC**: if the second block has a common root at size `n`,
the conjunction has exactly the PC degree of the first block. -/
theorem pcDegree_conj_eq_left (hφ : WF φ) (hψ : WF ψ) (y : (VarSys ψ).Rk n → K)
    (hy : ∀ g ∈ (template ψ K).inst n, eval y g = 0) :
    pcDegree ((template (conj φ ψ) K).inst n) = pcDegree ((template φ K).inst n) := by
  refine le_antisymm (pcDegree_conj_le_left φ ψ n K hφ) (pcDegree_le_of fun _ h =>
    SelfContainedCycle072.refutes_substitution (subRoot φ ψ n K y) (subRoot_X_cases φ ψ n K y)
      (fun g hg => ?_) h)
  obtain ⟨i, rfl⟩ := hg
  rcases inst_conj φ ψ n hφ hψ i with ⟨f, hf, e⟩ | ⟨g, hg, e⟩
  · rw [e, subRoot_left]; exact Or.inr hf
  · rw [e, subRoot_right, hy g hg, map_zero]; exact Or.inl rfl

end ConjPC

theorem eb_pc_of_ns {K : Type} [Field K] (T : Template K) (h : EventuallyBounded T.nsProfile) :
    EventuallyBounded T.pcProfile := by
  obtain ⟨B, M, hB⟩ := h
  exact ⟨B, M, fun n hn => le_trans (T.pcProfile_le_nsProfile n) (hB n hn)⟩

/-! ### PC types of the witnesses -/

section WitnessPC
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
include hp

theorem pcType_unique (T : Template K) {τ τ' : ℕ} (h : PCType T τ) (h' : PCType T τ') : τ = τ' := by
  have hx := (ClaudeComparison.periodic_linear_pc p T).exactly_one
  rcases τ with _ | _ | _ | _ | _ | τ <;> rcases τ' with _ | _ | _ | _ | _ | τ' <;>
    first | rfl | exact h.elim | exact h'.elim | (simp only [PCType] at h h'; tauto)

theorem psi1_pc_type : IType (template psi1 K).pcProfile 1 :=
  eb_pc_of_ns _ (psi1_type p K)

theorem eta_pc_lower {n d : ℕ} (hn : 3 ≤ n) (h : Refutes ((template eta K).inst n) d) :
    n < 3 * p * d :=
  SelfContainedCycle072.G_both_linear hp.out hn (Or.inr
    (SelfContainedCycle072.refutes_substitution (rename etaVar) (rename_var K _)
      (fun _ hf => (eta_hom_mem K (by omega) hf).symm) h))

theorem eta_pc_type : IType (template eta K).pcProfile 2 := by
  show Rec _ = ∅
  ext d
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hd
  obtain ⟨n, hn, hv⟩ := hd (3 * p * (d + 1) + 3)
  have := eta_pc_lower p K (by omega) ((pcDegree_le_iff _ d).mp (le_of_eq hv))
  have : 3 * p * d ≤ 3 * p * (d + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

omit [CharP K p] in
theorem psi3_pc_eq_eta {n : ℕ} (hn : 0 < n) (hpn : p ∣ n) :
    (template (psi3 p) K).pcProfile n = (template eta K).pcProfile n := by
  obtain ⟨y, hy⟩ := (hasRoot_iff (chi p) K hn).mpr (chi_model hp.out.two_le hn hpn)
  exact pcDegree_conj_eq_left eta (chi p) n K eta_WF (chi_WF p) y hy

theorem psi3_pc_le {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) :
    (template (psi3 p) K).pcProfile n ≤ (p : ℕ∞) :=
  le_trans ((template (psi3 p) K).pcProfile_le_nsProfile n) (psi3_le p K hn hpn)

theorem psi3_pc_type : IType (template (psi3 p) K).pcProfile 3 :=
  iType3_of hp.out.two_le p (eta_pc_type p K) (fun n hn hpn => psi3_pc_le p K (by omega) hpn)
    (fun n hn hpn => (psi3_pc_eq_eta p K (by omega) hpn).ge)

omit hp in
theorem lin_X {σ : Type} [Fintype σ] [DecidableEq σ] (u : σ) :
    (X u : MvPolynomial σ K) = C 0 + ∑ j, (if j = u then (1 : K) else 0) • X j := by
  simp only [map_zero, zero_add, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

omit hp in
theorem lin_XX {σ : Type} [Fintype σ] [DecidableEq σ] (u w : σ) :
    (X u + X w : MvPolynomial σ K) =
      C 0 + ∑ j, ((if j = u then (1 : K) else 0) + (if j = w then (1 : K) else 0)) • X j := by
  simp only [map_zero, zero_add, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit hp in
/-- The substitution `B̂ → B_{n,2n}` is affine in every variable. -/
theorem bVal_affine {n : ℕ} (v : (VarSys bhat).Rk n) :
    ∃ (c : K) (a : SelfContainedCycle054.Var n (2 * n) → K),
      aeval (bVal K) (X v : MvPolynomial ((VarSys bhat).Rk n) K) = C c + ∑ j, a j • X j := by
  classical
  rw [aeval_X]
  rcases v with ⟨R | f, t⟩
  · exact R.elim0
  · simp only [bVal]
    split_ifs
    · exact ⟨0, _, lin_X K _⟩
    · exact ⟨0, _, lin_X K _⟩
    · exact ⟨0, _, lin_XX K _ _⟩

omit hp in
/-- An actual PC refutation of `B̂` gives one of `B_{n,2n}` of the same degree. -/
theorem bhat_refutes_B {n d : ℕ} (hn : 0 < n) (h : Refutes ((template bhat K).inst n) d) :
    Refutes {f : MvPolynomial (SelfContainedCycle054.Var n (2 * n)) K |
      SelfContainedCycle054.IsBAxiom n (2 * n) f} d := by
  have h' := SelfContainedCycle080.refutes_filter_iff.mp h
  have := SelfContainedCycle074.affine_refutes (aeval (bVal K)) (bVal_affine K) (e := d)
    (fun f hf => Vinf_le_derivable _ _ (NSspan_le_Vinf _ _
      (NSspan_mono' hf.2 (bhat_hom_mem K hn hf.1)))) h'
  rwa [max_self] at this

theorem bhat_pc_lower {n : ℕ} (hn : 0 < n) {a d : ℕ} (hdiv : p ^ a ∣ n) (hsize : 2 * d ≤ n)
    (hd : d < p ^ a) : ¬ Refutes ((template bhat K).inst n) d := fun h =>
  SelfContainedCycle058.no_PCRefutes_rectangle (F := K) (a := a) (n := n) (m := 2 * n) (D := d)
    hp.out (by omega) hsize hd (by omega) (by rw [show 2 * n - n = n by omega]; exact hdiv)
    (bhat_refutes_B K hn h)

theorem bhat_pc_type : IType (template bhat K).pcProfile 4 := by
  show (Rec (template bhat K).pcProfile).Infinite
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  have hq : 0 < p ^ b := pow_pos hp.out.pos b
  have hbq : b < p ^ b := Nat.lt_pow_self hp.out.one_lt
  have hval : ∀ k, ∃ d : ℕ, (template bhat K).pcProfile (p ^ b * (p * (k + 1) + 1)) = d ∧
      p ^ b ≤ d ∧ d ≤ p ^ b + 4 := by
    intro k
    have hn : 0 < p ^ b * (p * (k + 1) + 1) := Nat.mul_pos hq (by omega)
    have hu : ¬ p ∣ p * (k + 1) + 1 := by
      intro hdvd
      have : p ∣ 1 := (Nat.dvd_add_right (Nat.dvd_mul_right p _)).mp hdvd
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
    obtain ⟨d, hd, hdle⟩ := exists_of_le_coe (le_trans
      ((template bhat K).pcProfile_le_nsProfile _)
      ((nsDegree_le_iff _ _).mpr (bhat_upper K hn hp.out hu rfl)))
    refine ⟨d, hd, ?_, hdle⟩
    by_contra hlt
    push_neg at hlt
    have h3 : 3 ≤ p * (k + 1) + 1 := by nlinarith [hp.out.two_le]
    have h4 : 2 * d ≤ p ^ b * (p * (k + 1) + 1) := by nlinarith
    exact bhat_pc_lower p K hn (a := b) (Nat.dvd_mul_right _ _) h4 hlt
      ((pcDegree_le_iff _ d).mp (le_of_eq hd))
  have hM' : ∀ d : ℕ, ∃ M, p ^ b ≤ d → d ≤ p ^ b + 4 → ∀ n, M ≤ n →
      (template bhat K).pcProfile n ≠ (d : ℕ∞) := by
    intro d
    by_cases h1 : p ^ b ≤ d ∧ d ≤ p ^ b + 4
    · by_contra hc
      push_neg at hc
      have hrec : d ∈ Rec (template bhat K).pcProfile := by
        intro M
        obtain ⟨_, _, n, hn, hv⟩ := hc M
        exact ⟨n, hn, hv⟩
      have := hb hrec
      omega
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h1⟩
  choose M hMs using hM'
  obtain ⟨d, hd, h1, h2⟩ := hval ((Finset.range (p ^ b + 5)).sup M)
  apply hMs d h1 h2 _ _ hd
  have hsup : M d ≤ (Finset.range (p ^ b + 5)).sup M :=
    Finset.le_sup (f := M) (Finset.mem_range.mpr (by omega))
  have h5 : (Finset.range (p ^ b + 5)).sup M ≤ p * ((Finset.range (p ^ b + 5)).sup M + 1) :=
    le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_left _ hp.out.pos)
  have h6 : p * ((Finset.range (p ^ b + 5)).sup M + 1) + 1 ≤
      p ^ b * (p * ((Finset.range (p ^ b + 5)).sup M + 1) + 1) := Nat.le_mul_of_pos_left _ hq
  omega

/-- **The witnesses have the four types** (ordinary PC, direct). -/
theorem wit_pc_type (τ : ℕ) (hτ : τ ∈ ({1, 2, 3, 4} : Set ℕ)) :
    PCType (template (wit p τ) K) τ := by
  rw [pcType_iff_intrinsic p]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl | rfl | rfl
  · exact psi1_pc_type p K
  · exact eta_pc_type p K
  · exact psi3_pc_type p K
  · exact bhat_pc_type p K

theorem bhat_pc_le_five {n : ℕ} (hn : 1 ≤ n) (hpn : ¬ p ∣ n) :
    (template bhat K).pcProfile n ≤ (5 : ℕ) :=
  le_trans ((template bhat K).pcProfile_le_nsProfile n) (bhat_le_five p K hn hpn)

end WitnessPC

/-! ### The reductions, ordinary PC -/

section ReductionPC
variable (K : Type) [Field K]

theorem conj_pc_nonhalt (ψ : Sentence) (hψ : WF ψ) (P : Prog) (hP : ¬ P.Halts) (n : ℕ)
    (hn : 1 ≤ n) : (template (conj ψ (theta P)) K).pcProfile n = (template ψ K).pcProfile n := by
  obtain ⟨y, hy⟩ := (hasRoot_iff (theta P) K (n := n) (by omega)).mpr (switch_i P hP (by omega))
  exact pcDegree_conj_eq_left ψ (theta P) n K hψ (theta_WF P) y hy

theorem conj_pc_halt (ψ : Sentence) (P : Prog) (hP : P.Halts) :
    EventuallyBounded (template (conj ψ (theta P)) K).pcProfile := by
  obtain ⟨C, N, hC⟩ := theta_eventually_bounded P K hP
  exact ⟨C, N, fun n hn => le_trans (pcDegree_conj_le_right ψ (theta P) n K (theta_WF P))
    (le_trans ((template (theta P) K).pcProfile_le_nsProfile n) (hC n hn))⟩

theorem join_pc_sandwich (A B : Sentence) (hA : WF A) (hB : WF B) :
    (∀ n, 1 ≤ n → max ((template A K).pcProfile n) ((template B K).pcProfile n) ≤
      (template (join A B) K).pcProfile n) ∧
    (∀ n, 1 ≤ n → (template (join A B) K).pcProfile n ≤
      max ((template A K).pcProfile n) ((template B K).pcProfile n) + 1) :=
  ⟨fun n hn => pcDegree_join_ge A B K n hA hB hn, fun n hn => pcDegree_join_le A B K n hA hB hn⟩

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

omit hp [CharP K p] in
theorem red_pc_halt (τ : ℕ) (c : Code) (h : (Code.eval c 0).Dom) :
    PCType (template (red p τ c) K) 1 :=
  conj_pc_halt K _ _ ((eval_dom_iff_halts c).mp h)

include hp in
theorem red_pc_nonhalt (τ : ℕ) (hτ : τ ∈ ({1, 2, 3, 4} : Set ℕ)) (c : Code)
    (h : ¬ (Code.eval c 0).Dom) : PCType (template (red p τ c) K) τ := by
  have hP : ¬ (univProg (Encodable.encode c)).Halts := fun h' => h ((eval_dom_iff_halts c).mpr h')
  rw [pcType_iff_intrinsic p, red, iType_congr (conj_pc_nonhalt K _ (wit_WF p τ) _ hP)]
  exact (pcType_iff_intrinsic p _ τ).mp (wit_pc_type p K τ hτ)

include hp in
theorem red2_pc_halt (a b : ℕ) (ha : a ∈ ({1, 2, 3, 4} : Set ℕ)) (c : Code)
    (h : (Code.eval c 0).Dom) : PCType (template (red2 p a b c) K) a := by
  have hB : WF (conj (wit p b) (theta (univProg (Encodable.encode c)))) :=
    conj_WF (wit_WF p b) (theta_WF _)
  obtain ⟨hlo, hhi⟩ := join_pc_sandwich K _ _ (wit_WF p a) hB
  have hg := conj_pc_halt K (wit p b) _ ((eval_dom_iff_halts c).mp h)
  rw [pcType_iff_intrinsic p, red2, iType_sandwich hg hlo hhi]
  exact (pcType_iff_intrinsic p _ a).mp (wit_pc_type p K a ha)

include hp in
theorem red2_pc_nonhalt (a b : ℕ) (ha : a ∈ ({1, 2, 3, 4} : Set ℕ))
    (hb : b ∈ ({1, 2, 3, 4} : Set ℕ)) (hab : wrank a < wrank b) (c : Code)
    (h : ¬ (Code.eval c 0).Dom) : PCType (template (red2 p a b c) K) b := by
  have hP : ¬ (univProg (Encodable.encode c)).Halts := fun h' => h ((eval_dom_iff_halts c).mpr h')
  have hB : WF (conj (wit p b) (theta (univProg (Encodable.encode c)))) :=
    conj_WF (wit_WF p b) (theta_WF _)
  obtain ⟨hlo, hhi⟩ := join_pc_sandwich K _ _ (wit_WF p a) hB
  have heq := conj_pc_nonhalt K (wit p b) (wit_WF p b) _ hP
  have hlo' : ∀ n, 1 ≤ n → max ((template (wit p a) K).pcProfile n)
      ((template (wit p b) K).pcProfile n) ≤ (template (red2 p a b c) K).pcProfile n :=
    fun n hn => by rw [← heq n hn]; exact hlo n hn
  have hhi' : ∀ n, 1 ≤ n → (template (red2 p a b c) K).pcProfile n ≤
      max ((template (wit p a) K).pcProfile n) ((template (wit p b) K).pcProfile n) + 1 :=
    fun n hn => by rw [← heq n hn]; exact hhi n hn
  rw [pcType_iff_intrinsic p]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  by_cases ha1 : a = 1
  · subst ha1
    have hg : EventuallyBounded (template (wit p 1) K).pcProfile := psi1_pc_type p K
    rw [iType_sandwich (h := (template (wit p b) K).pcProfile) hg
      (fun n hn => by rw [max_comm]; exact hlo' n hn)
      (fun n hn => by rw [max_comm]; exact hhi' n hn)]
    exact (pcType_iff_intrinsic p _ b).mp (wit_pc_type p K b (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hb))
  · by_cases hb2 : b = 2
    · subst hb2
      exact iType2_mono (eta_pc_type p K) fun n hn => le_trans (le_max_right _ _) (hlo' n hn)
    · have h43 : a = 4 ∧ b = 3 := by
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp_all [wrank]
      obtain ⟨rfl, rfl⟩ := h43
      refine iType3_of hp.out.two_le (max 5 p + 1) (eta_pc_type p K) (fun n hn hpn => ?_)
        (fun n hn hpn => ?_)
      · refine le_trans (hhi' n hn) ?_
        have e : ((max 5 p + 1 : ℕ) : ℕ∞) = max ((5 : ℕ) : ℕ∞) (p : ℕ∞) + 1 := by
          rw [max_coe]; push_cast; rfl
        rw [e]
        have h1 := bhat_pc_le_five p K hn hpn
        have h2 := psi3_pc_le p K (n := n) (by omega) hpn
        change max ((template bhat K).pcProfile n) ((template (psi3 p) K).pcProfile n) + 1 ≤ _
        gcongr
      · rw [← psi3_pc_eq_eta p K (by omega) hpn]
        exact le_trans (le_max_right _ _) (hlo' n hn)

end ReductionPC

/-! ### The theorems, ordinary PC, without the NS–PC comparison -/

section FinalPC
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
include hp

/-- **Every pair of distinct PC types is undecidable** (direct PC proof). -/
theorem undecidable_pair_PC_direct (a b : ℕ) (ha : a ∈ ({1, 2, 3, 4} : Set ℕ))
    (hb : b ∈ ({1, 2, 3, 4} : Set ℕ)) (hab : a ≠ b) :
    ¬ TypeSep (fun φ τ => PCType (template φ K) τ) {a} {b} := by
  rintro ⟨D, hD, h1, h2⟩
  rcases wrank_ne ha hb hab with hlt | hlt
  · exact ComputablePred.halting_problem 0 (sep_decides hD h1 h2 (red2 p a b)
      (red2_primrec p a b).to_comp (red2_promised p a b) (fun c => (Code.eval c 0).Dom)
      (fun c hc => ⟨a, rfl, red2_pc_halt K p a b ha c hc⟩)
      (fun c hc => ⟨b, rfl, red2_pc_nonhalt K p a b ha hb hlt c hc⟩))
  · have hnot := sep_decides hD h1 h2 (red2 p b a) (red2_primrec p b a).to_comp
      (red2_promised p b a) (fun c => ¬ (Code.eval c 0).Dom)
      (fun c hc => ⟨a, rfl, red2_pc_nonhalt K p b a hb ha hlt c hc⟩)
      (fun c hc => ⟨b, rfl, red2_pc_halt K p b a hb c (not_not.mp hc)⟩)
    exact ComputablePred.halting_problem 0 (by simpa only [not_not] using hnot.not)

/-- **Every pair of nonempty disjoint PC type sets is undecidable** (direct PC proof). -/
theorem undecidable_disjoint_PC_direct (A B : Set ℕ) (hA : A ⊆ {1, 2, 3, 4})
    (hB : B ⊆ {1, 2, 3, 4}) (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B) :
    ¬ TypeSep (fun φ τ => PCType (template φ K) τ) A B :=
  (pairs_iff_disjoint _ {1, 2, 3, 4}).mp
    (fun a ha b hb hab => undecidable_pair_PC_direct p K a b ha hb hab) A B hA hB hAne hBne hdisj

/-- **Every union of PC types is undecidable** (direct PC proof, partial algorithms), through
the historical `T1`-versus-`τ` reduction `c ↦ ψ_τ ∧ θ_{U(c)}`. -/
theorem undecidable_union_PC_direct (A : Set ℕ) (hA : A ⊆ {1, 2, 3, 4}) (hne : A.Nonempty)
    (hprop : ∃ τ ∈ ({1, 2, 3, 4} : Set ℕ), τ ∉ A) :
    ¬ ∃ D : Sentence →. Bool, Partrec D ∧
      ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ ∃ τ ∈ A, PCType (template φ K) τ) := by
  rintro ⟨D, hD, hcorr⟩
  have hdec : ∀ τ, ComputablePred fun c : Code => ∃ τ' ∈ A, PCType (template (red p τ c) K) τ' :=
    fun τ => decides_of_promise hD hcorr (red p τ) (red_primrec p τ).to_comp (red_promised p τ)
  by_cases h1 : (1 : ℕ) ∈ A
  · obtain ⟨τ, hτ, hτA⟩ := hprop
    refine ComputablePred.halting_problem 0 ((hdec τ).of_eq fun c => ?_)
    constructor
    · rintro ⟨τ', hτ'A, hty⟩
      by_contra hdom
      have := pcType_unique p K _ hty (red_pc_nonhalt K p τ hτ c hdom)
      subst this; exact hτA hτ'A
    · intro hdom; exact ⟨1, h1, red_pc_halt K p τ c hdom⟩
  · obtain ⟨τ, hτA⟩ := hne
    have hτ := hA hτA
    have hnot : ComputablePred fun c : Code => ¬ (Code.eval c 0).Dom := (hdec τ).of_eq fun c => by
      constructor
      · rintro ⟨τ', hτ'A, hty⟩ hdom
        have := pcType_unique p K _ hty (red_pc_halt K p τ c hdom)
        subst this; exact h1 hτ'A
      · intro hdom; exact ⟨τ, hτA, red_pc_nonhalt K p τ hτ c hdom⟩
    exact ComputablePred.halting_problem 0 (by simpa only [not_not] using hnot.not)

end FinalPC

end ClaudeUndec
