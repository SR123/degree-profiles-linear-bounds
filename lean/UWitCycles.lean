/-
Claude, 27 Sep 2026.  Undecidability, part E2: the cycle system `χ_p` (manuscript `lem:cycles`).

`χ_p` says that a unary function `f` satisfies `f^p(x) = x` and `f(x) ≠ x`; its finite models are
the disjoint unions of `p`-cycles.

* `chi_model`: if `p ∣ n` (and `n ≥ 1`), `χ_p` has a model of size `n` (rotation in blocks of `p`).
* `chi_nsRefutes`: if `p ∤ n`, the translation has an NS refutation of degree `p` over any field of
  characteristic `p`.  Sum the monomials of all walks of length `p`: telescoping with the totality
  sums gives `Σ walks − n` in degree `p`.  Open walks are clause groundings of `f^p(x) = x`.  A closed
  walk that is not injective contains a collision or, if it follows its own successors, is constant
  (the period divides the prime `p`) and contains `x_{ii}`, a grounding of `f(x) ≠ x`.  The
  injective closed walks are permuted freely by the rotations, a group of order `p`; each monomial
  occurs a multiple of `p` times (`IsPGroup.card_modEq_card_fixedPoints`), so they sum to `0`.
-/
import UWitEta

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open MvPolynomial DegreeProfilesReview.NS DegreeProfilesReview.Uniform

/-- The clause `f^p(x) = x`, flattened: `¬(y₁ = f(x)) ∨ ¬(y₂ = f(y₁)) ∨ ⋯ ∨ y_p = x`
(variables `x = 0`, `y_k = k`). -/
def cycClause (p : ℕ) : Clause :=
  (List.range p).map (fun k => neg (Atom.graph 0 [k] (k + 1))) ++ [pos (Atom.eq p 0)]

/-- `χ_p`: `f^p(x) = x` and `f(x) ≠ x`. -/
def chi (p : ℕ) : Sentence :=
  (([], [1]), [cycClause p, [neg (Atom.graph 0 [0] 1), neg (Atom.eq 1 0)]])

theorem chi_WF (p : ℕ) : WF (chi p) := by
  intro c hc l hl
  simp only [chi, Sentence.clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · simp only [cycClause, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hl
    rcases hl with ⟨k, -, rfl⟩ | rfl
    · exact ⟨Nat.one_pos, rfl⟩
    · trivial
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨Nat.one_pos, rfl⟩
    · trivial

/-! ### Models at multiples of `p` -/

/-- Rotation inside consecutive blocks of `p` labels. -/
def rotB (p i : ℕ) : ℕ := p * (i / p) + (i % p + 1) % p

theorem rotB_iter {p : ℕ} (hp : 0 < p) (k i : ℕ) :
    (rotB p)^[k] i = p * (i / p) + (i % p + k) % p := by
  induction k with
  | zero => simp [Nat.div_add_mod]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold rotB
    have h1 : (p * (i / p) + (i % p + k) % p) / p = i / p := by
      rw [Nat.mul_add_div hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp), add_zero]
    have h2 : (p * (i / p) + (i % p + k) % p) % p = (i % p + k) % p := by
      rw [Nat.mul_add_mod, Nat.mod_mod]
    rw [h1, h2]
    congr 1
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]

theorem rotB_lt {p n : ℕ} (hp : 0 < p) (hpn : p ∣ n) {i : ℕ} (hi : i < n) : rotB p i < n := by
  obtain ⟨m, rfl⟩ := hpn
  unfold rotB
  have h1 : i / p < m := by rw [Nat.div_lt_iff_lt_mul hp]; rw [mul_comm] at hi; exact hi
  have h2 : (i % p + 1) % p < p := Nat.mod_lt _ hp
  calc p * (i / p) + (i % p + 1) % p < p * (i / p) + p := by omega
    _ = p * (i / p + 1) := by ring
    _ ≤ p * m := Nat.mul_le_mul_left _ h1

theorem rotB_ne {p : ℕ} (hp : 2 ≤ p) (i : ℕ) : rotB p i ≠ i := by
  unfold rotB
  intro h
  have hi := Nat.div_add_mod i p
  have h3 : (i % p + 1) % p = i % p := by omega
  have h4 : i % p < p := Nat.mod_lt _ (by omega)
  by_cases h5 : i % p + 1 < p
  · rw [Nat.mod_eq_of_lt h5] at h3; omega
  · have : i % p + 1 = p := by omega
    rw [this, Nat.mod_self] at h3
    omega

/-- The model: rotation in blocks. -/
def chiStr (p n : ℕ) (hp : 0 < p) (hn : 0 < n) (hpn : p ∣ n) : Str (Fin n) where
  rel _ _ := False
  fn _ l := ⟨rotB p (l.headD ⟨0, hn⟩).val, rotB_lt hp hpn (l.headD ⟨0, hn⟩).2⟩

theorem chi_model {p n : ℕ} (hp : 2 ≤ p) (hn : 0 < n) (hpn : p ∣ n) :
    HasModelOfSize (chi p) n := by
  refine ⟨chiStr p n (by omega) hn hpn, ?_⟩
  intro c hc σ
  simp only [chi, Sentence.clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · -- `f^p(x) = x`
    by_contra hno
    simp only [clauseHolds, not_exists, not_and] at hno
    have hstep : ∀ k < p, (σ (k + 1)).val = rotB p (σ k).val := by
      intro k hk
      have := hno (neg (Atom.graph 0 [k] (k + 1)))
        (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
      simp only [litHolds, neg, Bool.false_eq_true, if_false, not_not, atomHolds, chi,
        Sentence.funs] at this
      rw [this.2.2]
      rfl
    have hiter : ∀ k ≤ p, (σ k).val = (rotB p)^[k] (σ 0).val := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        rw [hstep k (by omega), ih (by omega), Function.iterate_succ_apply']
    have hp0 : (σ p).val = (σ 0).val := by
      rw [hiter p le_rfl, rotB_iter (by omega), Nat.add_mod_right, Nat.mod_mod,
        Nat.div_add_mod]
    apply hno (pos (Atom.eq p 0)) (List.mem_append_right _ (List.mem_singleton_self _))
    simp only [litHolds, pos, if_true, atomHolds]
    exact Fin.ext hp0
  · -- `f(x) ≠ x`
    by_cases h1 : σ 1 = σ 0
    · refine ⟨neg (Atom.graph 0 [0] 1), List.mem_cons_self, ?_⟩
      simp only [litHolds, neg, Bool.false_eq_true, if_false, atomHolds, chi, Sentence.funs]
      rintro ⟨-, -, h⟩
      rw [h1] at h
      apply rotB_ne hp (σ 0).val
      have := congrArg Fin.val h
      simp only [chiStr, List.map_cons, List.map_nil, List.headD_cons] at this
      exact this.symm
    · exact ⟨neg (Atom.eq 1 0), by simp, by simp [litHolds, neg, atomHolds, h1]⟩

/-! ### Walks and the telescoping sum -/

theorem prod_map_range {M : Type} [CommMonoid M] (g : ℕ → M) :
    ∀ k, ((List.range k).map g).prod = ∏ i : Fin k, g i
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_map_range g k,
      Fin.prod_univ_castSucc]
    simp

section Walks
variable (p : ℕ) (K : Type) [Field K] {n : ℕ} (hn : 0 < n)

/-- The edge variable `x_{ab}` (`f(a) = b`). -/
noncomputable def xe (a b : Fin n) : MvPolynomial ((VarSys (chi p)).Rk n) K :=
  gX (chi p) K hn 0 [a] b

theorem xe_deg (a b : Fin n) : (xe p K hn a b).totalDegree ≤ 1 := totalDegree_gX _ _ _ _ _ _

/-- The monomial of a walk `w₀ → w₁ → ⋯ → w_k`. -/
noncomputable def walkM {k : ℕ} (w : Fin (k + 1) → Fin n) : MvPolynomial ((VarSys (chi p)).Rk n) K :=
  ∏ i : Fin k, xe p K hn (w i.castSucc) (w i.succ)

theorem walkM_deg {k : ℕ} (w : Fin (k + 1) → Fin n) : (walkM p K hn w).totalDegree ≤ k := by
  unfold walkM
  refine le_trans (totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => xe_deg p K hn _ _) ?_
  simp

theorem walkM_snoc {k : ℕ} (w : Fin (k + 1) → Fin n) (j : Fin n) :
    walkM p K hn (Fin.snoc (α := fun _ => Fin n) w j) = walkM p K hn w * xe p K hn (w (Fin.last k)) j := by
  unfold walkM
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

/-- **Telescoping**: the sum of all walk monomials of length `k` is `n` modulo NS degree `k`. -/
theorem walk_telescope : ∀ k : ℕ,
    (∑ w : Fin (k + 1) → Fin n, walkM p K hn w) - (n : MvPolynomial ((VarSys (chi p)).Rk n) K) ∈
      NSspan ((template (chi p) K).inst n) k
  | 0 => by
    have : (∑ w : Fin 1 → Fin n, walkM p K hn w) = (n : MvPolynomial ((VarSys (chi p)).Rk n) K) := by
      simp [walkM]
    rw [this, sub_self]; exact Submodule.zero_mem _
  | k + 1 => by
    have ih := walk_telescope k
    have hs : ∀ (x : Fin n) (y : Fin (k + 1) → Fin n),
        (Fin.snocEquiv (fun _ => Fin n)) (x, y) = Fin.snoc (α := fun _ => Fin n) y x :=
      fun _ _ => rfl
    rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [hs, walkM_snoc, ← Finset.mul_sum]
    have e : ∀ w : Fin (k + 1) → Fin n, walkM p K hn w *
        (∑ j : Fin n, xe p K hn (w (Fin.last k)) j) =
        walkM p K hn w + walkM p K hn w * ((∑ j : Fin n, xe p K hn (w (Fin.last k)) j) - 1) := by
      intro w; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, add_sub_right_comm]
    refine add_mem (NSspan_mono' (by omega) ih) (Submodule.sum_mem _ fun w _ => ?_)
    have htot := gX_tot (chi p) K hn (f := 0) Nat.one_pos [w (Fin.last k)]
    have hdeg : ((∑ j : Fin n, xe p K hn (w (Fin.last k)) j) - 1).totalDegree ≤ 1 := by
      refine le_trans (totalDegree_sub _ _) (max_le ?_ (by simp))
      refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun j _ => ?_)
      exact xe_deg p K hn _ _
    have h1 := NSspan_mono' hdeg (mem_NSspan_of_mem htot)
    have h2 := mul_mem_NSspan_of h1 (walkM_deg p K hn w)
    exact NSspan_mono' (by omega) h2

/-- A walk as a clause grounding. -/
def walkNu {k : ℕ} (w : Fin (k + 1) → Fin n) (v : ℕ) : Fin n :=
  if h : v < k + 1 then w ⟨v, h⟩ else w 0

/-- The grounding of `f^p(x) = x` along a walk is the walk monomial, times `0` if the walk is
closed. -/
theorem cyc_clause_eq (w : Fin (p + 1) → Fin n) :
    clausePoly (K := K) (chi p) (rvN (chi p) n) (gvN (chi p) n) (walkNu w) (cycClause p) =
      walkM p K hn w * (1 - if w (Fin.last p) = w 0 then 1 else 0) := by
  unfold clausePoly cycClause
  rw [List.map_append, List.prod_append, List.map_map]
  congr 1
  · rw [prod_map_range]
    unfold walkM
    apply Finset.prod_congr rfl
    intro i _
    simp only [Function.comp_apply, litFactor, neg, Bool.false_eq_true, if_false]
    rw [atomVal_graph (chi p) K hn (walkNu w) (i.val + 1) (Nat.one_pos) rfl]
    simp only [List.map_cons, List.map_nil, xe, walkNu, dif_pos (show i.val < p + 1 by omega),
      dif_pos (show i.val + 1 < p + 1 by omega)]
    rfl
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, litFactor,
      pos, if_true, atomVal, walkNu, dif_pos (show p < p + 1 by omega),
      dif_pos (show 0 < p + 1 by omega)]
    rfl

end Walks

/-! ### Closed walks -/

section Closed
variable (q : ℕ) (K : Type) [Field K] {n : ℕ} (hn : 0 < n)

/-- The monomial of a closed walk `u₀ → u₁ → ⋯ → u_q → u₀` (indices in `ℤ/(q+1)`). -/
noncomputable def cycM (u : Fin (q + 1) → Fin n) : MvPolynomial ((VarSys (chi (q + 1))).Rk n) K :=
  ∏ k : Fin (q + 1), xe (q + 1) K hn (u k) (u (k + 1))

theorem walkM_closed (u : Fin (q + 1) → Fin n) :
    walkM (q + 1) K hn u * xe (q + 1) K hn (u (Fin.last q)) (u 0) = cycM q K hn u := by
  unfold cycM walkM
  rw [Fin.prod_univ_castSucc (fun k => xe (q + 1) K hn (u k) (u (k + 1)))]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.coeSucc_eq_succ]
  · rw [Fin.last_add_one]

theorem cycM_rot (u : Fin (q + 1) → Fin n) (c : Fin (q + 1)) :
    cycM q K hn (fun k => u (k + c)) = cycM q K hn u := by
  unfold cycM
  exact Fintype.prod_equiv (Equiv.addRight c) _ _ (fun k => by
    simp only [Equiv.coe_addRight]
    rw [add_right_comm])

theorem nsmul_val (d : Fin (q + 1)) : ∀ m : ℕ, (m • d).val = (m * d.val) % (q + 1)
  | 0 => by simp
  | m + 1 => by
    rw [succ_nsmul, Fin.val_add, nsmul_val d m, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1; ring

variable [hp : Fact (q + 1).Prime]
include hp
open Fin.NatCast

/-- A closed walk that is not injective is NS-derivable in degree `q + 1`. -/
theorem cyc_noninj (u : Fin (q + 1) → Fin n) (hu : ¬ Function.Injective u) :
    cycM q K hn u ∈ NSspan ((template (chi (q + 1)) K).inst n) (q + 1) := by
  classical
  have hq1 : 1 ≤ q := by have := hp.out.two_le; omega
  set F : Fin (q + 1) → MvPolynomial ((VarSys (chi (q + 1))).Rk n) K :=
    fun k => xe (q + 1) K hn (u k) (u (k + 1)) with hF
  by_cases hA : ∃ k k', u k = u k' ∧ u (k + 1) ≠ u (k' + 1)
  · -- a collision
    obtain ⟨k, k', he, hne⟩ := hA
    have hkk : k ≠ k' := fun h => hne (by rw [h])
    have e1 : cycM q K hn u = F k * (F k' * ∏ i ∈ (Finset.univ.erase k).erase k', F i) := by
      unfold cycM
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hkk, Finset.mem_univ k'⟩)]
    have hc := gX_coll (chi (q + 1)) K hn (f := 0) Nat.one_pos [u k] hne
    have e2 : F k * F k' = gX (chi (q + 1)) K hn 0 [u k] (u (k + 1)) *
        gX (chi (q + 1)) K hn 0 [u k] (u (k' + 1)) := by
      simp only [hF, xe, he]
    rw [e1, ← mul_assoc, e2, mul_comm]
    have hrest : (∏ i ∈ (Finset.univ.erase k).erase k', F i).totalDegree ≤ q - 1 := by
      refine le_trans (totalDegree_finset_prod _ _) ?_
      refine le_trans (Finset.sum_le_sum fun i _ => xe_deg (q + 1) K hn _ _) ?_
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨Ne.symm hkk, Finset.mem_univ k'⟩),
        Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
      omega
    have hcd : (gX (chi (q + 1)) K hn 0 [u k] (u (k + 1)) *
        gX (chi (q + 1)) K hn 0 [u k] (u (k' + 1))).totalDegree ≤ 2 :=
      le_trans (totalDegree_mul _ _) (by
        have := totalDegree_gX (chi (q + 1)) K hn 0 [u k] (u (k + 1))
        have := totalDegree_gX (chi (q + 1)) K hn 0 [u k] (u (k' + 1))
        omega)
    have := mul_mem_NSspan_of (NSspan_mono' hcd (mem_NSspan_of_mem hc)) hrest
    exact NSspan_mono' (by omega) this
  · -- the walk follows its own successors, hence is constant
    push_neg at hA
    obtain ⟨k, k', he, hkk⟩ : ∃ k k', u k = u k' ∧ k ≠ k' := by
      unfold Function.Injective at hu
      push_neg at hu
      obtain ⟨a, b, h1, h2⟩ := hu
      exact ⟨a, b, h1, h2⟩
    have hshift : ∀ t : ℕ, u (k + (t : Fin (q + 1))) = u (k' + (t : Fin (q + 1))) := by
      intro t
      induction t with
      | zero => simpa using he
      | succ t ih =>
        have := hA _ _ ih
        rw [Nat.cast_succ, ← add_assoc, ← add_assoc]
        exact this
    have hper : ∀ j, u (j + (k' - k)) = u j := by
      intro j
      have h1 := hshift (j - k).val
      rw [Fin.cast_val_eq_self] at h1
      have e1 : k + (j - k) = j := by abel
      have e2 : k' + (j - k) = j + (k' - k) := by abel
      rw [e1, e2] at h1
      exact h1.symm
    have hmul : ∀ m : ℕ, ∀ j, u (j + m • (k' - k)) = u j := by
      intro m
      induction m with
      | zero => intro j; simp
      | succ m ih =>
        intro j
        rw [succ_nsmul, ← add_assoc, hper, ih]
    have hd0 : (k' - k).val ≠ 0 := by
      intro h
      apply hkk
      have : k' - k = 0 := Fin.ext h
      exact (sub_eq_zero.mp this).symm
    have hcop : Nat.Coprime (k' - k).val (q + 1) := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
      intro hdvd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hdvd
      have := (k' - k).2
      omega
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
    have hone : m • (k' - k) = 1 := by
      apply Fin.ext
      rw [nsmul_val, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < q + 1), mul_comm]
      exact hm
    have hconst : u 1 = u 0 := by
      have := hmul m 0
      rwa [hone, zero_add] at this
    -- the first edge is the fixed-point axiom
    have hax := clause_mem (chi (q + 1)) K (c := [neg (Atom.graph 0 [0] 1), neg (Atom.eq 1 0)])
      (by simp [chi, Sentence.clauses]) (fun _ => u 0)
    have hval : clausePoly (K := K) (chi (q + 1)) (rvN (chi (q + 1)) n) (gvN (chi (q + 1)) n)
        (fun _ => u 0) [neg (Atom.graph 0 [0] 1), neg (Atom.eq 1 0)] = F 0 := by
      simp only [clausePoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        litFactor, neg, Bool.false_eq_true, if_false]
      rw [atomVal_graph (chi (q + 1)) K hn _ 1 Nat.one_pos rfl]
      simp [atomVal, hF, xe, zero_add, hconst]
    rw [hval] at hax
    have e1 : cycM q K hn u = F 0 * ∏ i ∈ Finset.univ.erase 0, F i := by
      unfold cycM
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ 0)]
    rw [e1, mul_comm]
    have hrest : (∏ i ∈ Finset.univ.erase 0, F i).totalDegree ≤ q := by
      refine le_trans (totalDegree_finset_prod _ _) ?_
      refine le_trans (Finset.sum_le_sum fun i _ => xe_deg (q + 1) K hn _ _) ?_
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ 0),
        Finset.card_univ, Fintype.card_fin]
      omega
    have := mul_mem_NSspan_of (NSspan_mono' (xe_deg (q + 1) K hn _ _) (mem_NSspan_of_mem hax)) hrest
    exact NSspan_mono' (by omega) this

open Classical in
/-- The rotations act freely on the injective closed walks with a given monomial, so each
fibre has a multiple of `q + 1` elements. -/
theorem fiber_dvd (m : MvPolynomial ((VarSys (chi (q + 1))).Rk n) K) :
    (q + 1) ∣ (Finset.univ.filter fun u : Fin (q + 1) → Fin n =>
      Function.Injective u ∧ cycM q K hn u = m).card := by
  classical
  have hq1 : 1 ≤ q := by have := hp.out.two_le; omega
  let α := {u : Fin (q + 1) → Fin n // Function.Injective u ∧ cycM q K hn u = m}
  let G := Multiplicative (Fin (q + 1))
  let act : G → α → α := fun g x =>
    ⟨fun k => x.1 (k + Multiplicative.toAdd g),
      fun a b h => by simpa using x.2.1 h,
      by rw [cycM_rot]; exact x.2.2⟩
  letI : MulAction G α :=
    { smul := act
      one_smul := fun x => Subtype.ext (funext fun k => by
        show (act 1 x).1 k = x.1 k
        simp [act])
      mul_smul := fun g h x => Subtype.ext (funext fun k => by
        show (act (g * h) x).1 k = (act g (act h x)).1 k
        simp only [act]
        rw [toAdd_mul, add_assoc, add_comm (Multiplicative.toAdd g)]) }
  have hG : IsPGroup (q + 1) G := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fin, pow_one])
  have hmod := hG.card_modEq_card_fixedPoints α
  have hfix : Nat.card (MulAction.fixedPoints G α) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    have h1 := congrArg Subtype.val (hx (Multiplicative.ofAdd 1))
    have h2 := congrFun h1 0
    simp only [act, toAdd_ofAdd, zero_add] at h2
    have := x.2.1 (show x.1 1 = x.1 0 from by
      change (act (Multiplicative.ofAdd 1) x).1 0 = x.1 0 at h2
      simpa [act] using h2)
    exact absurd this (by
      rw [Fin.one_eq_zero_iff]; omega)
  rw [hfix] at hmod
  have hcard : Nat.card α = (Finset.univ.filter fun u : Fin (q + 1) → Fin n =>
      Function.Injective u ∧ cycM q K hn u = m).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← hcard]
  exact (Nat.modEq_zero_iff_dvd.mp hmod)

variable [CharP K (q + 1)]

open Classical in
/-- **The injective closed walks cancel** in characteristic `q + 1`. -/
theorem cyc_inj_sum :
    ∑ u ∈ Finset.univ.filter (fun u : Fin (q + 1) → Fin n => Function.Injective u),
      cycM q K hn u = 0 := by
  classical
  rw [Finset.sum_comp (fun x => x) (cycM q K hn)]
  apply Finset.sum_eq_zero
  intro m _
  obtain ⟨t, ht⟩ := fiber_dvd q K hn m
  have e : (Finset.univ.filter fun u : Fin (q + 1) → Fin n => Function.Injective u).filter
      (fun u => cycM q K hn u = m) = Finset.univ.filter fun u : Fin (q + 1) → Fin n =>
        Function.Injective u ∧ cycM q K hn u = m := by
    rw [Finset.filter_filter]
  rw [e, ht, mul_comm, mul_nsmul, ← Nat.cast_smul_eq_nsmul K (q + 1), CharP.cast_eq_zero,
    zero_smul]

include hn in
/-- **Bounded degree off the multiples of `p`** (manuscript `lem:cycles`). -/
theorem chi_nsRefutes (hpn : ¬ (q + 1) ∣ n) :
    NSRefutes ((template (chi (q + 1)) K).inst n) (q + 1) := by
  classical
  rw [nsRefutes_iff_one_mem_NSspan]
  set Γ := (template (chi (q + 1)) K).inst n
  have hT := walk_telescope (q + 1) K hn (q + 1)
  -- split the walks of length `q + 1` by their last vertex
  have hs : ∀ (x : Fin n) (y : Fin (q + 1) → Fin n),
      (Fin.snocEquiv (fun _ => Fin n)) (x, y) = Fin.snoc (α := fun _ => Fin n) y x :=
    fun _ _ => rfl
  have hsplit : (∑ w : Fin (q + 1 + 1) → Fin n, walkM (q + 1) K hn w) =
      (∑ u : Fin (q + 1) → Fin n, cycM q K hn u) +
        ∑ u : Fin (q + 1) → Fin n, ∑ j ∈ Finset.univ.erase (u 0),
          walkM (q + 1) K hn (Fin.snoc (α := fun _ => Fin n) u j) := by
    rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [hs]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (u 0)), walkM_snoc, walkM_closed]
  -- open walks are clause groundings
  have hopen : (∑ u : Fin (q + 1) → Fin n, ∑ j ∈ Finset.univ.erase (u 0),
      walkM (q + 1) K hn (Fin.snoc (α := fun _ => Fin n) u j)) ∈ NSspan Γ (q + 1) := by
    refine Submodule.sum_mem _ fun u _ => Submodule.sum_mem _ fun j hj => ?_
    have hj0 : j ≠ u 0 := Finset.ne_of_mem_erase hj
    set w := Fin.snoc (α := fun _ => Fin n) u j
    have hax := clause_mem (chi (q + 1)) K (c := cycClause (q + 1))
      (by simp [chi, Sentence.clauses]) (walkNu w)
    rw [cyc_clause_eq (q + 1) K hn w] at hax
    have hw : w (Fin.last (q + 1)) ≠ w 0 := by
      simp only [w, Fin.snoc_last]
      have : (Fin.snoc (α := fun _ => Fin n) u j : Fin (q + 1 + 1) → Fin n) 0 = u 0 := by
        simp
      rw [this]; exact hj0
    rw [if_neg hw, sub_zero, mul_one] at hax
    exact NSspan_mono' (walkM_deg (q + 1) K hn w) (mem_NSspan_of_mem hax)
  -- closed walks
  have hclosed : (∑ u : Fin (q + 1) → Fin n, cycM q K hn u) ∈ NSspan Γ (q + 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u => Function.Injective u),
      cyc_inj_sum q K hn, zero_add]
    refine Submodule.sum_mem _ fun u hu => ?_
    exact cyc_noninj q K hn u (Finset.mem_filter.mp hu).2
  have hn' : (n : MvPolynomial ((VarSys (chi (q + 1))).Rk n) K) ∈ NSspan Γ (q + 1) := by
    have := sub_mem (hsplit ▸ add_mem hclosed hopen : (∑ w : Fin (q + 1 + 1) → Fin n,
      walkM (q + 1) K hn w) ∈ NSspan Γ (q + 1)) hT
    rwa [sub_sub_cancel] at this
  have hnK : (n : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K (q + 1)]; exact hpn
  have : (1 : MvPolynomial ((VarSys (chi (q + 1))).Rk n) K) =
      (n : K)⁻¹ • (n : MvPolynomial ((VarSys (chi (q + 1))).Rk n) K) := by
    rw [← map_natCast (C : K →+* MvPolynomial _ K), smul_eq_C_mul, ← map_mul, inv_mul_cancel₀ hnK,
      map_one]
  rw [this]
  exact Submodule.smul_mem _ _ hn'

end Closed

end ClaudeUndec
