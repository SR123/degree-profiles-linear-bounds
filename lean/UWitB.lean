/-
Claude, 27 Sep 2026.  Undecidability, part E4: the fluctuating witness `B̂` (type T4; manuscript
`lem:witness`).

`B̂`: unary functions `f, g` are injective, have disjoint images, and cover the universe, the
covering being Skolemized by a unary `h` (`f(h(z)) = z ∨ g(h(z)) = z`).  All nonempty sizes are
unsatisfiable.  Variables `a_{ij}` (`f(i) = j`), `b_{ij}` (`g(i) = j`), `w_{ji}` (`h(j) = i`).

* Lower bound (`bhat_lower`): the substitution `a ↦ X_{j,i}`, `b ↦ X_{j,n+i}`, `w_{ji} ↦ a + b`
  maps every axiom into the NS span of the project's bijection system `B_{n,2n}` at its own degree
  (`IsBAxiom n (2n)`), so `SelfContainedCycle058.no_PCRefutes_rectangle` excludes degree `D` when
  `2D ≤ n`, `D < p^a` and `p^a ∣ n`.
* Upper bound (`bhat_upper`): the column sums `Σ_i (a_{ij} + b_{ij}) - 1` are derived in NS degree
  `4` from the witness `h`, and the counting certificate `UCounting.counting` gives
  `C(2n, q) - C(n, q)` in degree `q + 4`; with `q = p^{v_p(n)}` this scalar is the nonzero digit
  `n/q mod p` (Lucas, `SelfContainedCycle073.choose_prime_power_digit`).
-/
import UWitCycles
import UCounting
import AffinePeaks
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open MvPolynomial DegreeProfilesReview.NS DegreeProfilesReview.Uniform

/-- `B̂`.  Function symbols: `f = 0`, `g = 1`, `h = 2`, all unary. -/
def bhat : Sentence := (([], [1, 1, 1]),
  [[neg (Atom.graph 0 [0] 2), neg (Atom.graph 0 [1] 2), pos (Atom.eq 0 1)],
   [neg (Atom.graph 1 [0] 2), neg (Atom.graph 1 [1] 2), pos (Atom.eq 0 1)],
   [neg (Atom.graph 0 [0] 2), neg (Atom.graph 1 [1] 2)],
   [neg (Atom.graph 2 [0] 1), pos (Atom.graph 0 [1] 0), pos (Atom.graph 1 [1] 0)]])

theorem bhat_WF : WF bhat := by
  intro c hc l hl
  simp only [bhat, Sentence.clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> trivial

theorem bhat_no_model {n : ℕ} (hn : 0 < n) : ¬ HasModelOfSize bhat n := by
  rintro ⟨M, hM⟩
  have hinj : Function.Injective (fun x : Fin n => M.fn 0 [x]) := by
    intro x y hxy
    have h := hM [neg (Atom.graph 0 [0] 2), neg (Atom.graph 0 [1] 2), pos (Atom.eq 0 1)]
      (by simp [bhat, Sentence.clauses])
      (fun v => if v = 0 then x else if v = 1 then y else M.fn 0 [x])
    simp only [clauseHolds, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litHolds, neg, pos, if_true, Bool.false_eq_true, if_false, atomHolds,
      bhat, Sentence.funs] at h
    simp at h
    tauto
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj) (M.fn 1 [⟨0, hn⟩])
  have h := hM [neg (Atom.graph 0 [0] 2), neg (Atom.graph 1 [1] 2)]
    (by simp [bhat, Sentence.clauses])
    (fun v => if v = 0 then y else if v = 1 then ⟨0, hn⟩ else M.fn 0 [y])
  simp only [clauseHolds, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, litHolds, neg, Bool.false_eq_true, if_false, atomHolds,
    bhat, Sentence.funs] at h
  simp at h
  exact h hy

/-! ### The matrix of `B̂` -/

section Matrix
variable (K : Type) [Field K] {n : ℕ} (hn : 0 < n)

/-- `a_{ij}`, `b_{ij}` and `w_{ji}`. -/
noncomputable def av' (i j : Fin n) : MvPolynomial ((VarSys bhat).Rk n) K := gX bhat K hn 0 [i] j
noncomputable def bv (i j : Fin n) : MvPolynomial ((VarSys bhat).Rk n) K := gX bhat K hn 1 [i] j
noncomputable def wv (j i : Fin n) : MvPolynomial ((VarSys bhat).Rk n) K := gX bhat K hn 2 [j] i

/-- The combined `2n × n` matrix: rows `inl i` (for `f`) and `inr i` (for `g`). -/
noncomputable def bx : Fin n ⊕ Fin n → Fin n → MvPolynomial ((VarSys bhat).Rk n) K
  | Sum.inl i, j => av' K hn i j
  | Sum.inr i, j => bv K hn i j

@[simp] theorem bx_inl (i j : Fin n) : bx K hn (Sum.inl i) j = gX bhat K hn 0 [i] j := rfl
@[simp] theorem bx_inr (i j : Fin n) : bx K hn (Sum.inr i) j = gX bhat K hn 1 [i] j := rfl

theorem bx_deg (r : Fin n ⊕ Fin n) (j : Fin n) : (bx K hn r j).totalDegree ≤ 1 := by
  rcases r with i | i <;> exact totalDegree_gX _ _ _ _ _ _

theorem mem2 {g : MvPolynomial ((VarSys bhat).Rk n) K} (hg : g ∈ ((template bhat K).inst n)) (hd : g.totalDegree ≤ 2) :
    g ∈ NSspan ((template bhat K).inst n) 2 := NSspan_mono' hd (mem_NSspan_of_mem hg)

theorem deg2_gX (f f' : ℕ) (l l' : List (Fin n)) (j j' : Fin n) :
    (gX bhat K hn f l j * gX bhat K hn f' l' j').totalDegree ≤ 2 :=
  le_trans (totalDegree_mul _ _) (by
    have := totalDegree_gX bhat K hn f l j
    have := totalDegree_gX bhat K hn f' l' j'
    omega)

/-- Row collisions (functionality of `f` and `g`). -/
theorem bx_rowcoll (r : Fin n ⊕ Fin n) (j j' : Fin n) (h : j ≠ j') :
    bx K hn r j * bx K hn r j' ∈ NSspan ((template bhat K).inst n) 2 := by
  rcases r with i | i
  · rw [bx_inl, bx_inl]
    exact mem2 K (gX_coll bhat K hn (f := 0) (by decide) [i] h) (deg2_gX K hn _ _ _ _ _ _)
  · rw [bx_inr, bx_inr]
    exact mem2 K (gX_coll bhat K hn (f := 1) (by decide) [i] h) (deg2_gX K hn _ _ _ _ _ _)

/-- The grounding of the disjointness clause. -/
theorem ab_mem (i i' j : Fin n) : av' K hn i j * bv K hn i' j ∈ ((template bhat K).inst n) := by
  have hax := clause_mem bhat K (c := [neg (Atom.graph 0 [0] 2), neg (Atom.graph 1 [1] 2)])
    (by simp [bhat, Sentence.clauses]) (fun v => if v = 0 then i else if v = 1 then i' else j)
  simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    litFactor, neg, Bool.false_eq_true, if_false] at hax
  rw [atomVal_graph bhat K hn _ 2 (by decide) rfl, atomVal_graph bhat K hn _ 2 (by decide) rfl]
    at hax
  simpa [av', bv] using hax

/-- The grounding of an injectivity clause. -/
theorem inj_mem (f : ℕ) (hf : f = 0 ∨ f = 1) (i i' j : Fin n) (hii : i ≠ i') :
    gX bhat K hn f [i] j * gX bhat K hn f [i'] j ∈ ((template bhat K).inst n) := by
  have hc : [neg (Atom.graph f [0] 2), neg (Atom.graph f [1] 2), pos (Atom.eq 0 1)] ∈
      bhat.clauses := by
    rcases hf with rfl | rfl <;> simp [bhat, Sentence.clauses]
  have hax := clause_mem bhat K hc (fun v => if v = 0 then i else if v = 1 then i' else j)
  have hfl : f < bhat.funs.length := by rcases hf with rfl | rfl <;> decide
  simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    litFactor, neg, pos, Bool.false_eq_true, if_false, if_true] at hax
  rw [atomVal_graph bhat K hn _ 2 hfl (by rcases hf with rfl | rfl <;> rfl),
    atomVal_graph bhat K hn _ 2 hfl (by rcases hf with rfl | rfl <;> rfl)] at hax
  simp only [atomVal, List.map_cons, List.map_nil] at hax
  simpa [hii] using hax

/-- Column collisions (injectivity and disjointness). -/
theorem bx_colcoll (r r' : Fin n ⊕ Fin n) (j : Fin n) (h : r ≠ r') :
    bx K hn r j * bx K hn r' j ∈ NSspan ((template bhat K).inst n) 2 := by
  rcases r with i | i <;> rcases r' with i' | i'
  · rw [bx_inl, bx_inl]
    exact mem2 K (inj_mem K hn 0 (Or.inl rfl) i i' j (fun e => h (by rw [e])))
      (deg2_gX K hn _ _ _ _ _ _)
  · rw [bx_inl, bx_inr]
    exact mem2 K (ab_mem K hn i i' j) (deg2_gX K hn _ _ _ _ _ _)
  · rw [bx_inr, bx_inl, mul_comm]
    exact mem2 K (ab_mem K hn i' i j) (deg2_gX K hn _ _ _ _ _ _)
  · rw [bx_inr, bx_inr]
    exact mem2 K (inj_mem K hn 1 (Or.inr rfl) i i' j (fun e => h (by rw [e])))
      (deg2_gX K hn _ _ _ _ _ _)

/-- Row sums (totality of `f` and `g`). -/
theorem bx_rowsum (r : Fin n ⊕ Fin n) : (∑ j, bx K hn r j) - 1 ∈ NSspan ((template bhat K).inst n) 4 := by
  rcases r with i | i
  · have := gX_tot bhat K hn (f := 0) (by decide) [i]
    refine NSspan_mono' ?_ (mem_NSspan_of_mem this)
    refine le_trans (totalDegree_sub _ _) (max_le ?_ (by simp))
    exact le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun j _ =>
      le_trans (totalDegree_gX _ _ _ _ _ _) (by omega))
  · have := gX_tot bhat K hn (f := 1) (by decide) [i]
    refine NSspan_mono' ?_ (mem_NSspan_of_mem this)
    refine le_trans (totalDegree_sub _ _) (max_le ?_ (by simp))
    exact le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun j _ =>
      le_trans (totalDegree_gX _ _ _ _ _ _) (by omega))

/-- `T x_{r₀ j} - x_{r₀ j}` from the Boolean axiom and the column collisions. -/
theorem colsum_mul_sub (j : Fin n) (r₀ : Fin n ⊕ Fin n) :
    (∑ r, bx K hn r j) * bx K hn r₀ j - bx K hn r₀ j ∈ NSspan ((template bhat K).inst n) 2 := by
  classical
  rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ r₀)]
  have e : bx K hn r₀ j * bx K hn r₀ j + ∑ r ∈ Finset.univ.erase r₀, bx K hn r j * bx K hn r₀ j -
      bx K hn r₀ j = (bx K hn r₀ j ^ 2 - bx K hn r₀ j) +
        ∑ r ∈ Finset.univ.erase r₀, bx K hn r j * bx K hn r₀ j := by ring
  rw [e]
  refine add_mem ?_ (Submodule.sum_mem _ fun r hr => bx_colcoll K hn r r₀ j
    (Finset.ne_of_mem_erase hr))
  rcases r₀ with i | i
  · rw [bx_inl]
    simp only [gX, dif_pos (show 0 < bhat.funs.length by decide)]
    exact mem2 K (bool_mem bhat K _) (bool_mem_deg bhat K _)
  · rw [bx_inr]
    simp only [gX, dif_pos (show 1 < bhat.funs.length by decide)]
    exact mem2 K (bool_mem bhat K _) (bool_mem_deg bhat K _)

/-- The covering clause grounding `w_{ji}(1 - a_{ij})(1 - b_{ij})`. -/
theorem cover_mem (j i : Fin n) :
    wv K hn j i * ((1 - av' K hn i j) * (1 - bv K hn i j)) ∈ ((template bhat K).inst n) := by
  have hax := clause_mem bhat K
    (c := [neg (Atom.graph 2 [0] 1), pos (Atom.graph 0 [1] 0), pos (Atom.graph 1 [1] 0)])
    (by simp [bhat, Sentence.clauses]) (fun v => if v = 0 then j else i)
  simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    litFactor, neg, pos, Bool.false_eq_true, if_false, if_true] at hax
  rw [atomVal_graph bhat K hn _ 1 (by decide) rfl, atomVal_graph bhat K hn _ 0 (by decide) rfl,
    atomVal_graph bhat K hn _ 0 (by decide) rfl] at hax
  simpa [wv, av', bv] using hax

/-- **Column sums from the witness** (manuscript `lem:witness`), in NS degree `4`. -/
theorem bx_colsum (j : Fin n) : (∑ r, bx K hn r j) - 1 ∈ NSspan ((template bhat K).inst n) 4 := by
  classical
  set T := ∑ r, bx K hn r j with hT
  set u : Fin n → MvPolynomial ((VarSys bhat).Rk n) K := fun i => av' K hn i j + bv K hn i j
  set Z := ∑ i, wv K hn j i * u i with hZ
  have hTu : T = ∑ i, u i := by
    rw [hT, Fintype.sum_sum_type, ← Finset.sum_add_distrib]; rfl
  -- `Z - 1` in degree `3`
  have hZ1 : Z - 1 ∈ NSspan ((template bhat K).inst n) 3 := by
    have e : Z - 1 = (∑ i, (wv K hn j i - wv K hn j i * ((1 - av' K hn i j) * (1 - bv K hn i j)) +
        wv K hn j i * (av' K hn i j * bv K hn i j))) - 1 := by
      rw [hZ]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [u]; ring
    rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e2 : (∑ i, wv K hn j i) - (∑ i, wv K hn j i * ((1 - av' K hn i j) * (1 - bv K hn i j))) +
        (∑ i, wv K hn j i * (av' K hn i j * bv K hn i j)) - 1 =
        ((∑ i, wv K hn j i) - 1) -
          (∑ i, wv K hn j i * ((1 - av' K hn i j) * (1 - bv K hn i j))) +
          (∑ i, wv K hn j i * (av' K hn i j * bv K hn i j)) := by ring
    rw [e2]
    refine add_mem (sub_mem ?_ ?_) ?_
    · have := gX_tot bhat K hn (f := 2) (by decide) [j]
      refine NSspan_mono' ?_ (mem_NSspan_of_mem this)
      refine le_trans (totalDegree_sub _ _) (max_le ?_ (by simp))
      exact le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun i _ =>
        le_trans (totalDegree_gX _ _ _ _ _ _) (by omega))
    · refine Submodule.sum_mem _ fun i _ => ?_
      refine NSspan_mono' ?_ (mem_NSspan_of_mem (cover_mem K hn j i))
      refine le_trans (totalDegree_mul _ _) ?_
      have h1 : (wv K hn j i).totalDegree ≤ 1 := totalDegree_gX bhat K hn 2 [j] i
      have ha : (1 - av' K hn i j).totalDegree ≤ 1 :=
        le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_gX bhat K hn 0 [i] j))
      have hb : (1 - bv K hn i j).totalDegree ≤ 1 :=
        le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_gX bhat K hn 1 [i] j))
      have h2 := le_trans (totalDegree_mul (1 - av' K hn i j) (1 - bv K hn i j))
        (Nat.add_le_add ha hb)
      omega
    · refine Submodule.sum_mem _ fun i _ => ?_
      have hab := mem2 K (ab_mem K hn i i j) (deg2_gX K hn _ _ _ _ _ _)
      have := mul_mem_NSspan_of hab (totalDegree_gX bhat K hn 2 [j] i)
      exact this
  -- `T u_i - u_i` in degree `2`
  have hA : ∀ i, T * u i - u i ∈ NSspan ((template bhat K).inst n) 2 := by
    intro i
    have e : T * u i - u i = (T * bx K hn (Sum.inl i) j - bx K hn (Sum.inl i) j) +
        (T * bx K hn (Sum.inr i) j - bx K hn (Sum.inr i) j) := by
      simp only [u, bx]; ring
    rw [e]
    exact add_mem (colsum_mul_sub K hn j _) (colsum_mul_sub K hn j _)
  -- `T - 1 = Σ_i w_i (T u_i - u_i) - (T - 1)(Z - 1)`
  have e : T - 1 = ∑ i, wv K hn j i * (T * u i - u i) - (T - 1) * (Z - 1) := by
    have : ∑ i, wv K hn j i * (T * u i - u i) = T * Z - Z := by
      rw [hZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [this]; ring
  rw [e]
  refine sub_mem (Submodule.sum_mem _ fun i _ => ?_) ?_
  · have := mul_mem_NSspan_of (hA i) (totalDegree_gX bhat K hn 2 [j] i)
    exact NSspan_mono' (by omega) this
  · have hTd : (T - 1).totalDegree ≤ 1 := by
      refine le_trans (totalDegree_sub _ _) (max_le ?_ (by simp))
      exact le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun r _ => bx_deg K hn r j)
    have := mul_mem_NSspan_of hZ1 hTd
    exact NSspan_mono' (by omega) this

include hn in
/-- **The counting certificate for `B̂`**: `C(2n, k) - C(n, k)` in NS degree `k + 4`. -/
theorem bhat_count (k : ℕ) :
    (((2 * n).choose k : ℕ) : MvPolynomial ((VarSys bhat).Rk n) K) - ((n.choose k : ℕ) : _) ∈
      NSspan ((template bhat K).inst n) (k + 4) := by
  have := counting ((template bhat K).inst n) (bx K hn) k (bx_deg K hn) (bx_rowcoll K hn) (bx_colcoll K hn)
    (bx_rowsum K hn) (bx_colsum K hn)
  simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using this

include hn in
/-- **Upper bound at level `v_p(n) = a`**: NS degree at most `p^a + 4`. -/
theorem bhat_upper {p : ℕ} (hp : p.Prime) [CharP K p] {a u : ℕ} (hu : ¬ p ∣ u)
    (hnu : n = p ^ a * u) : NSRefutes ((template bhat K).inst n) (p ^ a + 4) := by
  rw [nsRefutes_iff_one_mem_NSspan]
  have hc := bhat_count K hn (p ^ a)
  have hq : 0 < p ^ a := pow_pos hp.pos a
  have h1 := SelfContainedCycle073.choose_prime_power_digit hp a (2 * n)
  have h2 := SelfContainedCycle073.choose_prime_power_digit hp a n
  have hd1 : 2 * n / p ^ a = 2 * u := by rw [hnu]; rw [show 2 * (p ^ a * u) = p ^ a * (2 * u) by ring,
    Nat.mul_div_cancel_left _ hq]
  have hd2 : n / p ^ a = u := by rw [hnu, Nat.mul_div_cancel_left _ hq]
  rw [hd1] at h1
  rw [hd2] at h2
  have e1 : (((2 * n).choose (p ^ a) : ℕ) : K) = ((2 * u : ℕ) : K) :=
    (CharP.natCast_eq_natCast K p).mpr h1
  have e2 : ((n.choose (p ^ a) : ℕ) : K) = ((u : ℕ) : K) := (CharP.natCast_eq_natCast K p).mpr h2
  have hs : ((((2 * n).choose (p ^ a) : ℕ) : K) - ((n.choose (p ^ a) : ℕ) : K)) = (u : K) := by
    rw [e1, e2]; push_cast; ring
  have hu0 : (u : K) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff K p]; exact hu
  have e3 : (((2 * n).choose (p ^ a) : ℕ) : MvPolynomial ((VarSys bhat).Rk n) K) -
      ((n.choose (p ^ a) : ℕ) : MvPolynomial ((VarSys bhat).Rk n) K) = C (u : K) := by
    rw [← hs, map_sub, map_natCast, map_natCast]
  rw [e3] at hc
  have : (1 : MvPolynomial ((VarSys bhat).Rk n) K) = (u : K)⁻¹ • C (u : K) := by
    rw [smul_eq_C_mul, ← map_mul, inv_mul_cancel₀ hu0, map_one]
  rw [this]
  exact Submodule.smul_mem _ _ hc

end Matrix

/-! ### Degree lower bounds for single axioms -/

section DegLow
variable {σ K : Type} [Field K]

theorem deg_X_sub_one (v : σ) : (X v - 1 : MvPolynomial σ K).totalDegree = 1 := by
  classical
  apply le_antisymm
  · exact le_trans (totalDegree_sub _ _) (max_le (totalDegree_X_le' v) (by simp))
  · have h : (X v - 1 : MvPolynomial σ K).coeff (Finsupp.single v 1) ≠ 0 := by
      rw [coeff_sub, coeff_X, coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
      simp
    have := le_totalDegree (mem_support_iff.mpr h)
    simpa using this

theorem X_sub_one_ne (v : σ) : (X v - 1 : MvPolynomial σ K) ≠ 0 := by
  intro h; have := deg_X_sub_one (K := K) v; rw [h] at this; simp at this

theorem deg_XX (u v : σ) : 2 ≤ (X u * X v : MvPolynomial σ K).totalDegree := by
  rw [totalDegree_mul_of_isDomain (X_ne_zero _) (X_ne_zero _), totalDegree_X, totalDegree_X]

theorem deg_bool (v : σ) : 2 ≤ (X v ^ 2 - X v : MvPolynomial σ K).totalDegree := by
  have e : (X v ^ 2 - X v : MvPolynomial σ K) = X v * (X v - 1) := by ring
  rw [e, totalDegree_mul_of_isDomain (X_ne_zero _) (X_sub_one_ne v), totalDegree_X,
    deg_X_sub_one]

theorem deg_cover (w a b : σ) :
    3 ≤ (X w * ((1 - X a) * (1 - X b)) : MvPolynomial σ K).totalDegree := by
  have e1 : (1 - X a : MvPolynomial σ K) = -(X a - 1) := by ring
  have e2 : (1 - X b : MvPolynomial σ K) = -(X b - 1) := by ring
  have hna : (1 - X a : MvPolynomial σ K) ≠ 0 := by rw [e1]; exact neg_ne_zero.mpr (X_sub_one_ne a)
  have hnb : (1 - X b : MvPolynomial σ K) ≠ 0 := by rw [e2]; exact neg_ne_zero.mpr (X_sub_one_ne b)
  rw [totalDegree_mul_of_isDomain (X_ne_zero _) (mul_ne_zero hna hnb),
    totalDegree_mul_of_isDomain hna hnb, totalDegree_X, e1, e2, totalDegree_neg, totalDegree_neg,
    deg_X_sub_one, deg_X_sub_one]

end DegLow

/-! ### The substitution into `B_{n,2n}` -/

section Lower
open SelfContainedCycle054 SelfContainedCycle058
variable (K : Type) [Field K] {n : ℕ}

/-- Columns of `B_{n,2n}`: `f`-pigeons `1, …, n`, `g`-pigeons `n+1, …, 2n`. -/
def fcol (i : Fin n) : Label (2 * n) := ⟨i.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
def gcol (i : Fin n) : Label (2 * n) := ⟨n + i.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem fcol_inj : Function.Injective (fcol (n := n)) := fun i j h => by
  have := congrArg Subtype.val h; simp only [fcol] at this; exact Fin.ext (by omega)
theorem gcol_inj : Function.Injective (gcol (n := n)) := fun i j h => by
  have := congrArg Subtype.val h; simp only [gcol] at this; exact Fin.ext (by omega)
theorem fcol_ne_gcol (i j : Fin n) : fcol i ≠ gcol j := fun h => by
  have := congrArg Subtype.val h; simp only [fcol, gcol] at this; omega

noncomputable def colEquiv : Fin n ⊕ Fin n ≃ Label (2 * n) :=
  Equiv.ofBijective (Sum.elim fcol gcol) ⟨by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (fcol_inj h)
    · exact absurd h (fcol_ne_gcol i j)
    · exact absurd h.symm (fcol_ne_gcol j i)
    · exact congrArg Sum.inr (gcol_inj h), by
    rintro ⟨v, hv⟩
    have := Finset.mem_Icc.mp hv
    by_cases h : v ≤ n
    · exact ⟨Sum.inl ⟨v - 1, by omega⟩, Subtype.ext (by simp [fcol]; omega)⟩
    · exact ⟨Sum.inr ⟨v - n - 1, by omega⟩, Subtype.ext (by simp [gcol]; omega)⟩⟩

theorem sum_cols {M : Type} [AddCommMonoid M] (F : Label (2 * n) → M) :
    ∑ c : Label (2 * n), F c = ∑ i : Fin n, F (fcol i) + ∑ i : Fin n, F (gcol i) := by
  rw [← Fintype.sum_equiv colEquiv (fun r => F (colEquiv r)) F (fun _ => rfl),
    Fintype.sum_sum_type]
  rfl

/-- The substitution: `a_{ij} ↦ X_{j,i}`, `b_{ij} ↦ X_{j,n+i}`, `w_{ji} ↦ a_{ij} + b_{ij}`. -/
noncomputable def bVal : (VarSys bhat).Rk n → MvPolynomial (Var n (2 * n)) K
  | ⟨Sum.inl R, _⟩ => R.elim0
  | ⟨Sum.inr f, t⟩ =>
      let t' : Fin (bhat.funs.get f + 1) → Fin n := t
      if f.val = 0 then X (lab (t' (Fin.last _)), fcol (t' 0))
      else if f.val = 1 then X (lab (t' (Fin.last _)), gcol (t' 0))
      else X (lab (t' 0), fcol (t' (Fin.last _))) + X (lab (t' 0), gcol (t' (Fin.last _)))

theorem bVal_a (t : Fin (bhat.funs.get ⟨0, by decide⟩) → Fin n) (j : Fin n) :
    bVal K (gvN bhat n ⟨0, by decide⟩ t j) = X (lab j, fcol (t ⟨0, by decide⟩)) := by
  simp only [bVal, gvN, if_true]; rfl
theorem bVal_b (t : Fin (bhat.funs.get ⟨1, by decide⟩) → Fin n) (j : Fin n) :
    bVal K (gvN bhat n ⟨1, by decide⟩ t j) = X (lab j, gcol (t ⟨0, by decide⟩)) := by
  simp only [bVal, gvN]; rfl
theorem bVal_w (t : Fin (bhat.funs.get ⟨2, by decide⟩) → Fin n) (i : Fin n) :
    bVal K (gvN bhat n ⟨2, by decide⟩ t i) =
      X (lab (t ⟨0, by decide⟩), fcol i) + X (lab (t ⟨0, by decide⟩), gcol i) := by
  simp only [bVal, gvN]; rfl

theorem bVal_deg (v : (VarSys bhat).Rk n) :
    (aeval (bVal K) (X v : MvPolynomial ((VarSys bhat).Rk n) K)).totalDegree ≤ 1 := by
  rw [aeval_X]
  rcases v with ⟨R | f, t⟩
  · exact R.elim0
  · simp only [bVal]
    split_ifs
    · exact totalDegree_X_le' _
    · exact totalDegree_X_le' _
    · exact le_trans (totalDegree_add _ _) (max_le (totalDegree_X_le' _) (totalDegree_X_le' _))

/-- Every variable of `B̂` is `gvN` of a function symbol. -/
theorem bhat_var (v : (VarSys bhat).Rk n) :
    ∃ (f : Fin bhat.funs.length) (t : Fin (bhat.funs.get f) → Fin n) (j : Fin n),
      v = gvN bhat n f t j := by
  rcases v with ⟨R | f, t⟩
  · exact R.elim0
  · let t' : Fin (bhat.funs.get f + 1) → Fin n := t
    refine ⟨f, Fin.init t', t' (Fin.last _), ?_⟩
    show (Sigma.mk (β := fun i => (tuples (vArity bhat i)).Rk n) (Sum.inr f) t :
      (VarSys bhat).Rk n) = Sigma.mk (β := fun i => (tuples (vArity bhat i)).Rk n) (Sum.inr f)
        (Fin.snoc (α := fun _ => Fin n) (Fin.init t') (t' (Fin.last _)))
    rw [Fin.snoc_init_self]

theorem bmap_gX0 (hn : 0 < n) (a b : Fin n) :
    aeval (bVal K) (gX bhat K hn 0 [a] b) = X (lab b, fcol a) := by
  simp only [gX, dif_pos (show 0 < bhat.funs.length by decide), aeval_X, bVal_a]; rfl
theorem bmap_gX1 (hn : 0 < n) (a b : Fin n) :
    aeval (bVal K) (gX bhat K hn 1 [a] b) = X (lab b, gcol a) := by
  simp only [gX, dif_pos (show 1 < bhat.funs.length by decide), aeval_X, bVal_b]; rfl
theorem bmap_gX2 (hn : 0 < n) (z x : Fin n) :
    aeval (bVal K) (gX bhat K hn 2 [z] x) = X (lab z, fcol x) + X (lab z, gcol x) := by
  simp only [gX, dif_pos (show 2 < bhat.funs.length by decide), aeval_X, bVal_w]; rfl

/-- **Every axiom of `B̂` is mapped into the NS span of `B_{n,2n}` at its own degree.** -/
theorem bhat_hom_mem (hn : 0 < n) {g : MvPolynomial ((VarSys bhat).Rk n) K}
    (hg : g ∈ (template bhat K).inst n) :
    aeval (bVal K) g ∈ NSspan {f : MvPolynomial (Var n (2 * n)) K | IsBAxiom n (2 * n) f}
      g.totalDegree := by
  classical
  have hdeg := totalDegree_map_le (aeval (bVal K)) (bVal_deg K) g
  have inΔ : ∀ {f : MvPolynomial (Var n (2 * n)) K}, IsBAxiom n (2 * n) f →
      f ∈ NSspan {f : MvPolynomial (Var n (2 * n)) K | IsBAxiom n (2 * n) f} f.totalDegree :=
    fun h => mem_NSspan_of_mem h
  have inΔ2 : ∀ {f : MvPolynomial (Var n (2 * n)) K}, IsBAxiom n (2 * n) f → f.totalDegree ≤ 2 →
      f ∈ NSspan {f : MvPolynomial (Var n (2 * n)) K | IsBAxiom n (2 * n) f} 2 :=
    fun h hd => NSspan_mono' hd (mem_NSspan_of_mem h)
  have dXX : ∀ u v : Var n (2 * n), (X u * X v : MvPolynomial (Var n (2 * n)) K).totalDegree ≤ 2 :=
    fun u v => le_trans (totalDegree_mul _ _)
      (by have := totalDegree_X_le' (K := K) u; have := totalDegree_X_le' (K := K) v; omega)
  have dB : ∀ u : Var n (2 * n), (X u ^ 2 - X u : MvPolynomial (Var n (2 * n)) K).totalDegree ≤ 2 :=
    fun u => le_trans (totalDegree_sub _ _) (max_le (le_trans (totalDegree_pow _ _)
        (by have := totalDegree_X_le' (K := K) u; omega)) (le_trans (totalDegree_X_le' u) (by omega)))
  have hdg : ∀ q : MvPolynomial ((VarSys bhat).Rk n) K,
      (aeval (bVal K) q).totalDegree ≤ q.totalDegree :=
    fun q => totalDegree_map_le (aeval (bVal K)) (bVal_deg K) q
  rcases inst_cases bhat K hg with ⟨f, t, rfl⟩ | ⟨f, t, j, j', hjj, rfl⟩ | ⟨v, rfl⟩ |
    ⟨c, hc, ν, rfl⟩
  · -- totality
    match f, t with
    | ⟨0, h⟩, t =>
      have e : aeval (bVal K) ((∑ j : Fin n, X (gvN bhat n ⟨0, h⟩ t j)) - 1 :
          MvPolynomial ((VarSys bhat).Rk n) K) = colAxiom (fcol (t ⟨0, Nat.one_pos⟩)) := by
        simp only [map_sub, map_sum, aeval_X, map_one, colAxiom, bVal_a]
        rw [sum_lab (fun r => (X (r, fcol (t ⟨0, Nat.one_pos⟩)) : MvPolynomial (Var n (2 * n)) K))]
      rw [e]; exact NSspan_mono' (e ▸ hdeg) (inΔ (IsBAxiom.col _))
    | ⟨1, h⟩, t =>
      have e : aeval (bVal K) ((∑ j : Fin n, X (gvN bhat n ⟨1, h⟩ t j)) - 1 :
          MvPolynomial ((VarSys bhat).Rk n) K) = colAxiom (gcol (t ⟨0, Nat.one_pos⟩)) := by
        simp only [map_sub, map_sum, aeval_X, map_one, colAxiom, bVal_b]
        rw [sum_lab (fun r => (X (r, gcol (t ⟨0, Nat.one_pos⟩)) : MvPolynomial (Var n (2 * n)) K))]
      rw [e]; exact NSspan_mono' (e ▸ hdeg) (inΔ (IsBAxiom.col _))
    | ⟨2, h⟩, t =>
      have e : aeval (bVal K) ((∑ j : Fin n, X (gvN bhat n ⟨2, h⟩ t j)) - 1 :
          MvPolynomial ((VarSys bhat).Rk n) K) = rowAxiom (lab (t ⟨0, Nat.one_pos⟩)) := by
        simp only [map_sub, map_sum, aeval_X, map_one, rowAxiom, bVal_w]
        rw [sum_cols (fun c => (X (lab (t ⟨0, Nat.one_pos⟩), c) : MvPolynomial (Var n (2 * n)) K)),
          Finset.sum_add_distrib]
      rw [e]; exact NSspan_mono' (e ▸ hdeg) (inΔ (IsBAxiom.row _))
  · -- collisions
    match f, t with
    | ⟨0, h⟩, t =>
      have e : aeval (bVal K) (X (gvN bhat n ⟨0, h⟩ t j) * X (gvN bhat n ⟨0, h⟩ t j') :
          MvPolynomial ((VarSys bhat).Rk n) K) =
          X (lab j, fcol (t ⟨0, Nat.one_pos⟩)) * X (lab j', fcol (t ⟨0, Nat.one_pos⟩)) := by
        simp only [map_mul, aeval_X, bVal_a]
      rw [e]
      exact NSspan_mono' (e ▸ hdeg)
        (inΔ (IsBAxiom.colCollision _ _ _ (fun h' => hjj (lab_injective h'))))
    | ⟨1, h⟩, t =>
      have e : aeval (bVal K) (X (gvN bhat n ⟨1, h⟩ t j) * X (gvN bhat n ⟨1, h⟩ t j') :
          MvPolynomial ((VarSys bhat).Rk n) K) =
          X (lab j, gcol (t ⟨0, Nat.one_pos⟩)) * X (lab j', gcol (t ⟨0, Nat.one_pos⟩)) := by
        simp only [map_mul, aeval_X, bVal_b]
      rw [e]
      exact NSspan_mono' (e ▸ hdeg)
        (inΔ (IsBAxiom.colCollision _ _ _ (fun h' => hjj (lab_injective h'))))
    | ⟨2, h⟩, t =>
      set z := lab (t ⟨0, Nat.one_pos⟩)
      have e : aeval (bVal K) (X (gvN bhat n ⟨2, h⟩ t j) * X (gvN bhat n ⟨2, h⟩ t j') :
          MvPolynomial ((VarSys bhat).Rk n) K) =
          X (z, fcol j) * X (z, fcol j') + X (z, fcol j) * X (z, gcol j') +
            X (z, gcol j) * X (z, fcol j') + X (z, gcol j) * X (z, gcol j') := by
        simp only [map_mul, aeval_X, bVal_w]; ring
      rw [e]
      refine NSspan_mono' (deg_XX _ _) (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_)
      · exact inΔ2 (IsBAxiom.rowCollision _ _ _ (fun h' => hjj (fcol_inj h'))) (dXX _ _)
      · exact inΔ2 (IsBAxiom.rowCollision _ _ _ (fcol_ne_gcol _ _)) (dXX _ _)
      · exact inΔ2 (IsBAxiom.rowCollision _ _ _ (fun h' => fcol_ne_gcol _ _ h'.symm)) (dXX _ _)
      · exact inΔ2 (IsBAxiom.rowCollision _ _ _ (fun h' => hjj (gcol_inj h'))) (dXX _ _)
  · -- Booleans
    obtain ⟨f, t, j, rfl⟩ := bhat_var v
    match f, t with
    | ⟨0, h⟩, t =>
      have e : aeval (bVal K) (X (gvN bhat n ⟨0, h⟩ t j) ^ 2 - X (gvN bhat n ⟨0, h⟩ t j) :
          MvPolynomial ((VarSys bhat).Rk n) K) = boolAxiom (lab j, fcol (t ⟨0, Nat.one_pos⟩)) := by
        simp only [map_sub, map_pow, aeval_X, bVal_a, boolAxiom]
      rw [e]; exact NSspan_mono' (e ▸ hdeg) (inΔ (IsBAxiom.boolean _))
    | ⟨1, h⟩, t =>
      have e : aeval (bVal K) (X (gvN bhat n ⟨1, h⟩ t j) ^ 2 - X (gvN bhat n ⟨1, h⟩ t j) :
          MvPolynomial ((VarSys bhat).Rk n) K) = boolAxiom (lab j, gcol (t ⟨0, Nat.one_pos⟩)) := by
        simp only [map_sub, map_pow, aeval_X, bVal_b, boolAxiom]
      rw [e]; exact NSspan_mono' (e ▸ hdeg) (inΔ (IsBAxiom.boolean _))
    | ⟨2, h⟩, t =>
      set z := lab (t ⟨0, Nat.one_pos⟩)
      have e : aeval (bVal K) (X (gvN bhat n ⟨2, h⟩ t j) ^ 2 - X (gvN bhat n ⟨2, h⟩ t j) :
          MvPolynomial ((VarSys bhat).Rk n) K) =
          boolAxiom (z, fcol j) + boolAxiom (z, gcol j) + 2 * (X (z, fcol j) * X (z, gcol j)) := by
        simp only [map_sub, map_pow, aeval_X, bVal_w, boolAxiom]; ring
      rw [e]
      refine NSspan_mono' (deg_bool _) (add_mem (add_mem ?_ ?_) ?_)
      · exact inΔ2 (IsBAxiom.boolean _) (dB _)
      · exact inΔ2 (IsBAxiom.boolean _) (dB _)
      · have := inΔ2 (IsBAxiom.rowCollision z _ _ (fcol_ne_gcol j j)) (dXX _ _)
        have e2 : (2 : MvPolynomial (Var n (2 * n)) K) * (X (z, fcol j) * X (z, gcol j)) =
            (2 : K) • (X (z, fcol j) * X (z, gcol j)) := by
          rw [smul_eq_C_mul]; rfl
        rw [e2]; exact Submodule.smul_mem _ _ this
  · -- clause groundings
    simp only [bhat, Sentence.clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · have h0 := atomVal_graph bhat K hn ν (f := 0) (args := [0]) 2 (by decide) rfl
      have h1 := atomVal_graph bhat K hn ν (f := 0) (args := [1]) 2 (by decide) rfl
      simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        litFactor, neg, pos, Bool.false_eq_true, if_false, if_true, h0, h1]
      by_cases he : ν 0 = ν 1
      · refine mem_NSspan_of_image (Or.inr ?_) (hdg _)
        simp [atomVal, he]
      · have e : aeval (bVal K) (gX bhat K hn 0 [ν 0] (ν 2) * (gX bhat K hn 0 [ν 1] (ν 2) *
            (1 - atomVal (K := K) bhat (rvN bhat n) (gvN bhat n) ν (Atom.eq 0 1)))) =
            X (lab (ν 2), fcol (ν 0)) * X (lab (ν 2), fcol (ν 1)) := by
          simp only [atomVal, if_neg he, sub_zero, mul_one, map_mul, bmap_gX0]
        refine mem_NSspan_of_image (Or.inl ?_) (hdg _)
        rw [e]
        exact IsBAxiom.rowCollision _ _ _ (fun h' => he (fcol_inj h'))
    · have h0 := atomVal_graph bhat K hn ν (f := 1) (args := [0]) 2 (by decide) rfl
      have h1 := atomVal_graph bhat K hn ν (f := 1) (args := [1]) 2 (by decide) rfl
      simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        litFactor, neg, pos, Bool.false_eq_true, if_false, if_true, h0, h1]
      by_cases he : ν 0 = ν 1
      · refine mem_NSspan_of_image (Or.inr ?_) (hdg _)
        simp [atomVal, he]
      · have e : aeval (bVal K) (gX bhat K hn 1 [ν 0] (ν 2) * (gX bhat K hn 1 [ν 1] (ν 2) *
            (1 - atomVal (K := K) bhat (rvN bhat n) (gvN bhat n) ν (Atom.eq 0 1)))) =
            X (lab (ν 2), gcol (ν 0)) * X (lab (ν 2), gcol (ν 1)) := by
          simp only [atomVal, if_neg he, sub_zero, mul_one, map_mul, bmap_gX1]
        refine mem_NSspan_of_image (Or.inl ?_) (hdg _)
        rw [e]
        exact IsBAxiom.rowCollision _ _ _ (fun h' => he (gcol_inj h'))
    · have h0 := atomVal_graph bhat K hn ν (f := 0) (args := [0]) 2 (by decide) rfl
      have h1 := atomVal_graph bhat K hn ν (f := 1) (args := [1]) 2 (by decide) rfl
      simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        litFactor, neg, Bool.false_eq_true, if_false, h0, h1]
      have e : aeval (bVal K) (gX bhat K hn 0 [ν 0] (ν 2) * gX bhat K hn 1 [ν 1] (ν 2)) =
          X (lab (ν 2), fcol (ν 0)) * X (lab (ν 2), gcol (ν 1)) := by
        simp only [map_mul, bmap_gX0, bmap_gX1]
      refine mem_NSspan_of_image (Or.inl ?_) (hdg _)
      rw [e]
      exact IsBAxiom.rowCollision _ _ _ (fcol_ne_gcol _ _)
    · have h0 := atomVal_graph bhat K hn ν (f := 2) (args := [0]) 1 (by decide) rfl
      have h1 := atomVal_graph bhat K hn ν (f := 0) (args := [1]) 0 (by decide) rfl
      have h2 := atomVal_graph bhat K hn ν (f := 1) (args := [1]) 0 (by decide) rfl
      simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        litFactor, neg, pos, Bool.false_eq_true, if_false, if_true, h0, h1, h2]
      set A : Var n (2 * n) := (lab (ν 0), fcol (ν 1))
      set B : Var n (2 * n) := (lab (ν 0), gcol (ν 1))
      have e : aeval (bVal K) (gX bhat K hn 2 [ν 0] (ν 1) * ((1 - gX bhat K hn 0 [ν 1] (ν 0)) *
          (1 - gX bhat K hn 1 [ν 1] (ν 0)))) =
          -((1 - X B) * (X A ^ 2 - X A)) - (1 - X A) * (X B ^ 2 - X B) := by
        simp only [map_mul, map_sub, map_one, bmap_gX0, bmap_gX1, bmap_gX2, A, B]; ring
      have hlow : 3 ≤ (gX bhat K hn 2 [ν 0] (ν 1) * ((1 - gX bhat K hn 0 [ν 1] (ν 0)) *
          (1 - gX bhat K hn 1 [ν 1] (ν 0)))).totalDegree := by
        simp only [gX, dif_pos (show 2 < bhat.funs.length by decide),
          dif_pos (show 0 < bhat.funs.length by decide),
          dif_pos (show 1 < bhat.funs.length by decide)]
        exact deg_cover _ _ _
      rw [e]
      refine NSspan_mono' hlow (sub_mem (neg_mem ?_) ?_)
      · refine mul_mem_NSspan (IsBAxiom.boolean A) ?_
        have h1 : (1 - X B : MvPolynomial (Var n (2 * n)) K).totalDegree ≤ 1 :=
          le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_X_le' _))
        have := dB A
        simp only [boolAxiom] at *
        omega
      · refine mul_mem_NSspan (IsBAxiom.boolean B) ?_
        have h1 : (1 - X A : MvPolynomial (Var n (2 * n)) K).totalDegree ≤ 1 :=
          le_trans (totalDegree_sub _ _) (max_le (by simp) (totalDegree_X_le' _))
        have := dB B
        simp only [boolAxiom] at *
        omega

/-- An NS refutation of `B̂` gives one of `B_{n,2n}` of the same degree. -/
theorem bhat_nsRefutes_B (hn : 0 < n) {d : ℕ} (h : NSRefutes ((template bhat K).inst n) d) :
    NSRefutes {f : MvPolynomial (Var n (2 * n)) K | IsBAxiom n (2 * n) f} d :=
  nsRefutes_of_hom (aeval (bVal K)) (bVal_deg K) (fun _ hf => bhat_hom_mem K hn hf) h

/-- **Lower bound at level `a`** (`p^a ∣ n`): no NS refutation of degree `d` with `2d ≤ n` and
`d < p^a` (project theorem `no_PCRefutes_rectangle`). -/
theorem bhat_lower {p : ℕ} (hp : p.Prime) [CharP K p] (hn : 0 < n) {a d : ℕ} (hdiv : p ^ a ∣ n)
    (hsize : 2 * d ≤ n) (hd : d < p ^ a) : ¬ NSRefutes ((template bhat K).inst n) d := by
  intro h
  apply no_PCRefutes_rectangle (F := K) (a := a) (n := n) (m := 2 * n) (D := d) hp (by omega)
    hsize hd (by omega) (by rw [show 2 * n - n = n by omega]; exact hdiv)
  exact DegreeProfilesReview.NS.refutes_of_nsRefutes (bhat_nsRefutes_B K hn h)

end Lower

end ClaudeUndec
