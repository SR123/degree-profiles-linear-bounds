/-
Claude, 25 Sep 2026.  Every prime characteristic, part D: base change, the classification with
square-root rates, and type agreement under (★).

For every prime `p`, every field `R` of characteristic `p` and every uniform template `T` over
`R`:
* both profiles satisfy (P) with onset `N(d) = max(n₀, 2(kd+s)+1, (kd+s)(kd+s+1)/2)` and period
  the least power of `p` above `kd+s` (`charP_periodic`);
* each profile is exactly one of T1–T4, with the square-root rates (`charP_pc_main`,
  `charP_ns_main`);
* under (★) the two profiles have the same type (`charP_common_type`).
For `p = 2` this reproduces the characteristic-two theorems of `C017Rates`.
-/
import PInduction
import C017TypeAgreement

set_option autoImplicit false
open CategoryTheory

namespace ClaudeCP
open DegreeProfilesReview.Uniform DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open DegreeProfilesReview.ConcreteM5 DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.Profiles
open SelfContainedCycle003 SelfContainedCycle004
open ClaudeWitnessTransfer ClaudeC017

/-! ### Base change -/

section BaseChange
variable {F L : Type} [Field F] [Field L] (φ : F →+* L) {p : ℕ} [Fact p.Prime]

theorem zEltP_map (a n : ℕ) (c : Fin a → F) :
    MonoidAlgebra.mapRangeRingHom (Sfin (n + p ^ a)) φ (zEltP p a n c) = zEltP p a n (φ ∘ c) := by
  simp only [zEltP, map_sum, mapRange_smul_alg, map_sub, map_one,
    MonoidAlgebra.mapRangeRingHom_single, Function.comp_apply]

theorem topWitness_map {r a n : ℕ} {c : Fin a → F} {w : MonoidAlgebra F (Sfin (n + p ^ a))}
    (hw : IsTopWitness p r a n c w) :
    IsTopWitness p r a n (φ ∘ c) (MonoidAlgebra.mapRangeRingHom (Sfin (n + p ^ a)) φ w) := by
  have h := tupleRelations_map φ hw
  rw [map_sub, map_mul, map_mul, map_pow, zEltP_map] at h
  exact h

variable [CharP F p] [CharP L p]

theorem generic_mapP {a : ℕ} {c : Fin a → F} (hc : Generic p c) : Generic p (φ ∘ c) := by
  intro g hg
  apply hc g
  apply φ.injective
  rw [map_sum, map_zero, ← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Function.comp_apply]
  congr 1
  exact congrFun (congrArg DFunLike.coe
    (Subsingleton.elim (φ.comp (ZMod.castHom (dvd_refl p) F)) (ZMod.castHom (dvd_refl p) L))) (g i)

end BaseChange

section Galois
variable (p : ℕ) [Fact p.Prime]

theorem exists_generic_galoisP (a : ℕ) (ha : a ≠ 0) :
    ∃ c : Fin a → GaloisField p a, Generic p c := by
  have hfr := GaloisField.finrank p ha
  let bF := Module.finBasisOfFinrankEq (ZMod p) (GaloisField p a) hfr
  refine ⟨fun i => bF i, ?_⟩
  intro g hg
  have hli := bF.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  apply hli g _ i
  rw [← hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, mul_comm]
  congr 1
  exact congrFun (congrArg DFunLike.coe (Subsingleton.elim (algebraMap (ZMod p) (GaloisField p a))
    (ZMod.castHom (dvd_refl p) (GaloisField p a)))) (g i)

/-- **The top-power witness hypothesis, unconditionally**, over any algebraically closed field
of characteristic `p`. -/
theorem topWitnessHypothesis_of_isAlgClosed (L : Type) [Field L] [IsAlgClosed L] [CharP L p] :
    TopWitnessHypothesis p L triW := by
  intro r a n hr hn
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain rfl : r = 0 := by simpa using hr
    refine ⟨Fin.elim0, ?_, 0, base_top_witness 0 n _⟩
    intro g _
    funext i
    exact i.elim0
  · letI : Algebra (ZMod p) L := ZMod.algebra L p
    obtain ⟨c, hc⟩ := exists_generic_galoisP p a (by omega)
    obtain ⟨w, hw⟩ := top_witness_exists a c hc r hr n hn
    let φ : GaloisField p a →+* L :=
      (IsAlgClosed.lift : GaloisField p a →ₐ[ZMod p] L).toRingHom
    exact ⟨φ ∘ c, generic_mapP φ hc, _, topWitness_map φ hw⟩

end Galois

/-! ### Rates for a profile with `p`-power periods -/

section Rates
variable {p : ℕ} [Fact p.Prime] {k s n0 : ℕ} {h : ℕ → ℕ∞}

theorem period_isPowP (d : ℕ) : ∃ j, period p k s d = p ^ j := by
  unfold period
  split
  · exact ⟨0, rfl⟩
  · exact leastPowGt_isPow (Fact.out : p.Prime).two_le _

theorem T3_sqrtP (hk : 1 ≤ k) (P : PeriodicProfile h (wOnset k s n0 triW) (period p k s))
    (h3 : IsT3 h (wOnset k s n0 triW)) :
    ∃ D, D ∈ E h (wOnset k s n0 triW) ∧ (∀ d ∈ E h (wOnset k s n0 triW), d ≤ D) ∧
      (∃ j, period p k s D = p ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p k s D) ∧ U.Nonempty ∧
        (∃ c, c < period p k s D ∧ c ∉ U) ∧
        (∀ n, wOnset k s n0 triW D ≤ n → n % period p k s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, wOnset k s n0 triW D ≤ m →
            m % period p k s D = n % period p k s D → h m = (v : ℕ∞)) ∧
        (∀ n, wOnset k s n0 triW D ≤ n → 3 ≤ n → n % period p k s D ∉ U →
          (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n) := by
  obtain ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, hUeasy, hUhard⟩ := P.T3_structure h3
  refine ⟨D, hDE, hDmax, period_isPowP D, U, hUlt, hUne, hUprop, hUeasy, ?_⟩
  intro n hn h3n hnU
  have hn0 : n0 ≤ n := by
    have h0 : wOnset k s n0 triW 0 = n0 := by unfold wOnset; rw [if_pos rfl]
    have := P.N_mono (Nat.zero_le D)
    rw [h0] at this
    exact le_trans this hn
  exact hUhard n hn hnU _ (wOnset_sqrt2_le hk hn0 h3n)

theorem T4_sqrtP (hk : 1 ≤ k) (P : PeriodicProfile h (wOnset k s n0 triW) (period p k s))
    (h4 : IsT4 h (wOnset k s n0 triW)) (B : ℕ) :
    ∃ d, B < d ∧ ∃ c, wOnset k s n0 triW d ≤ c ∧ c < wOnset k s n0 triW d + period p k s d ∧
      (∀ m, wOnset k s n0 triW d ≤ m → m % period p k s d = c % period p k s d →
        h m = (d : ℕ∞)) ∧
      Nat.sqrt (2 * c) < k * d + s + p + 1 ∧ (Nat.sqrt (2 * c) - s - p - 1) / k < d := by
  obtain ⟨d, hBd, c0, hc0, hrec⟩ := P.T4_structure h4 (max B (n0 + 4))
  set N := wOnset k s n0 triW d with hN
  set q := period p k s d with hq
  have hq0 : 0 < q := P.Q_pos d
  set c := N + (c0 - N) % q with hc
  have hsplit : c0 = c + q * ((c0 - N) / q) := by
    have := Nat.mod_add_div (c0 - N) q
    omega
  have hcmod : c % q = c0 % q := by
    rw [hsplit, Nat.add_mul_mod_self_left]
  refine ⟨d, lt_of_le_of_lt (le_max_left _ _) hBd, c, Nat.le_add_right _ _,
    Nat.add_lt_add_left (Nat.mod_lt _ hq0) _, fun m hm hmc => (hrec m hm (hmc.trans hcmod)).1, ?_⟩
  have hd4 : n0 + 4 < d := lt_of_le_of_lt (le_max_right _ _) hBd
  have hkd : d ≤ k * d := Nat.le_mul_of_pos_left d hk
  set r := k * d + s with hr
  have hNr : N = triW r := wOnset_eq_triW hk hd4
  have hqr : q ≤ p * r := period_le s (Fact.out : p.Prime).two_le hk (by omega)
  have hclt : c < triW r + p * r := by
    have : c < N + q := Nat.add_lt_add_left (Nat.mod_lt _ hq0) _
    omega
  have htri : 2 * triW r ≤ r * (r + 1) := by unfold triW; exact Nat.mul_div_le _ _
  have h2c : 2 * c < (r + p + 1) * (r + p + 1) := by nlinarith
  have hsqrt : Nat.sqrt (2 * c) < r + p + 1 := Nat.sqrt_lt.mpr h2c
  refine ⟨by omega, ?_⟩
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have : 1 ≤ k * d := by nlinarith
  rw [mul_comm d k]
  omega

/-- **The four types with square-root rates**, for a profile with `p`-power periods. -/
theorem four_types_sqrtP (hk : 1 ≤ k)
    (P : PeriodicProfile h (wOnset k s n0 triW) (period p k s)) :
    let N := wOnset k s n0 triW
    ((IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ IsT4 h N)) ∧
    (IsT1 h → ∃ B M : ℕ, ∀ n, M ≤ n → h n ≤ (B : ℕ∞)) ∧
    (IsT2 h N → ∀ n, n0 ≤ n → 3 ≤ n → (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n) ∧
    (IsT3 h N →
      ∃ D, D ∈ E h N ∧ (∀ d ∈ E h N, d ≤ D) ∧ (∃ j, period p k s D = p ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p k s D) ∧ U.Nonempty ∧
        (∃ c, c < period p k s D ∧ c ∉ U) ∧
        (∀ n, N D ≤ n → n % period p k s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, N D ≤ m →
            m % period p k s D = n % period p k s D → h m = (v : ℕ∞)) ∧
        (∀ n, N D ≤ n → 3 ≤ n → n % period p k s D ∉ U →
          (((Nat.sqrt (2 * n) - s - 1) / k : ℕ) : ℕ∞) < h n)) ∧
    (IsT4 h N → ∀ B : ℕ,
      ∃ d, B < d ∧ ∃ c, N d ≤ c ∧ c < N d + period p k s d ∧
        (∀ m, N d ≤ m → m % period p k s d = c % period p k s d → h m = (d : ℕ∞)) ∧
        Nat.sqrt (2 * c) < k * d + s + p + 1 ∧ (Nat.sqrt (2 * c) - s - p - 1) / k < d) :=
  ⟨P.exactly_one, fun h1 => h1, fun h2 _ hn h3 => T2_sqrt hk P h2 hn h3, T3_sqrtP hk P,
    T4_sqrtP hk P⟩

end Rates

/-! ### The theorems for every prime -/

section Main
variable {R : Type} [Field R] (p : ℕ) [Fact p.Prime] [CharP R p] (T : Template R)

/-- **(P) in every prime characteristic.** -/
theorem charP_periodic :
    PeriodicProfile T.pcProfile (wOnset T.k T.s T.n0 triW) (period p T.k T.s) ∧
      PeriodicProfile T.nsProfile (wOnset T.k T.s T.n0 triW) (period p T.k T.s) :=
  periodic_of_top_hypothesis T p (AlgebraicClosure R) triW_mono
    (topWitnessHypothesis_of_isAlgClosed p _)

/-- **Theorem B in characteristic `p`, PC profile.** -/
theorem charP_pc_main :
    let N := wOnset T.k T.s T.n0 triW
    let h := T.pcProfile
    ((IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ IsT4 h N)) ∧
    (IsT1 h → ∃ B M : ℕ, ∀ n, M ≤ n → h n ≤ (B : ℕ∞)) ∧
    (IsT2 h N → ∀ n, T.n0 ≤ n → 3 ≤ n →
      (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n) ∧
    (IsT3 h N →
      ∃ D, D ∈ E h N ∧ (∀ d ∈ E h N, d ≤ D) ∧ (∃ j, period p T.k T.s D = p ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p T.k T.s D) ∧ U.Nonempty ∧
        (∃ c, c < period p T.k T.s D ∧ c ∉ U) ∧
        (∀ n, N D ≤ n → n % period p T.k T.s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, N D ≤ m →
            m % period p T.k T.s D = n % period p T.k T.s D → h m = (v : ℕ∞)) ∧
        (∀ n, N D ≤ n → 3 ≤ n → n % period p T.k T.s D ∉ U →
          (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n)) ∧
    (IsT4 h N → ∀ B : ℕ,
      ∃ d, B < d ∧ ∃ c, N d ≤ c ∧ c < N d + period p T.k T.s d ∧
        (∀ m, N d ≤ m → m % period p T.k T.s d = c % period p T.k T.s d → h m = (d : ℕ∞)) ∧
        Nat.sqrt (2 * c) < T.k * d + T.s + p + 1 ∧ (Nat.sqrt (2 * c) - T.s - p - 1) / T.k < d) :=
  four_types_sqrtP T.hk (charP_periodic p T).1

/-- **Theorem B in characteristic `p`, NS profile.** -/
theorem charP_ns_main :
    let N := wOnset T.k T.s T.n0 triW
    let h := T.nsProfile
    ((IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ IsT2 h N ∧ ¬ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ IsT3 h N ∧ ¬ IsT4 h N) ∨
     (¬ IsT1 h ∧ ¬ IsT2 h N ∧ ¬ IsT3 h N ∧ IsT4 h N)) ∧
    (IsT1 h → ∃ B M : ℕ, ∀ n, M ≤ n → h n ≤ (B : ℕ∞)) ∧
    (IsT2 h N → ∀ n, T.n0 ≤ n → 3 ≤ n →
      (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n) ∧
    (IsT3 h N →
      ∃ D, D ∈ E h N ∧ (∀ d ∈ E h N, d ≤ D) ∧ (∃ j, period p T.k T.s D = p ^ j) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p T.k T.s D) ∧ U.Nonempty ∧
        (∃ c, c < period p T.k T.s D ∧ c ∉ U) ∧
        (∀ n, N D ≤ n → n % period p T.k T.s D ∈ U →
          ∃ v : ℕ, v ≤ D ∧ ∀ m, N D ≤ m →
            m % period p T.k T.s D = n % period p T.k T.s D → h m = (v : ℕ∞)) ∧
        (∀ n, N D ≤ n → 3 ≤ n → n % period p T.k T.s D ∉ U →
          (((Nat.sqrt (2 * n) - T.s - 1) / T.k : ℕ) : ℕ∞) < h n)) ∧
    (IsT4 h N → ∀ B : ℕ,
      ∃ d, B < d ∧ ∃ c, N d ≤ c ∧ c < N d + period p T.k T.s d ∧
        (∀ m, N d ≤ m → m % period p T.k T.s d = c % period p T.k T.s d → h m = (d : ℕ∞)) ∧
        Nat.sqrt (2 * c) < T.k * d + T.s + p + 1 ∧ (Nat.sqrt (2 * c) - T.s - p - 1) / T.k < d) :=
  four_types_sqrtP T.hk (charP_periodic p T).2

include p in
/-- No hypothesis needed: if no finite PC value recurs, no finite NS value recurs. -/
theorem charP_pc_T2_ns_T2 (h2 : IsT2 T.pcProfile (wOnset T.k T.s T.n0 triW)) :
    IsT2 T.nsProfile (wOnset T.k T.s T.n0 triW) := by
  unfold IsT2 at h2 ⊢
  ext d
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨n, hn, hnd⟩
  have hle : T.pcProfile n ≤ (d : ℕ∞) := hnd ▸ T.pcProfile_le_nsProfile n
  obtain ⟨x, hx, hxd⟩ := enat_exists_of_le_coe hle
  have hmem := mem_E_of_le (charP_periodic p T).1 hn hx hxd
  rw [h2] at hmem
  exact hmem

include p in
/-- **Agreement of types in characteristic `p`, under (★).** -/
theorem charP_types_agree (hC : ChainBound R T.Var) :
    let N := wOnset T.k T.s T.n0 triW
    (IsT1 T.pcProfile ↔ IsT1 T.nsProfile) ∧ (IsT2 T.pcProfile N ↔ IsT2 T.nsProfile N) ∧
    (IsT3 T.pcProfile N ↔ IsT3 T.nsProfile N) ∧ (IsT4 T.pcProfile N ↔ IsT4 T.nsProfile N) := by
  obtain ⟨F, hF, hub⟩ := upperComparison_of_chainBound T hC
  exact types_transfer (charP_periodic p T).1 (charP_periodic p T).2 hF
    T.pcProfile_le_nsProfile hub

include p in
/-- **The common type in characteristic `p`, under (★).** -/
theorem charP_common_type (hC : ChainBound R T.Var) :
    let N := wOnset T.k T.s T.n0 triW
    (IsT1 T.pcProfile ∧ IsT1 T.nsProfile) ∨ (IsT2 T.pcProfile N ∧ IsT2 T.nsProfile N) ∨
    (IsT3 T.pcProfile N ∧ IsT3 T.nsProfile N) ∨ (IsT4 T.pcProfile N ∧ IsT4 T.nsProfile N) := by
  obtain ⟨e1, e2, e3, e4⟩ := charP_types_agree p T hC
  rcases (charP_periodic p T).1.exactly_one with h | h | h | h
  · exact Or.inl ⟨h.1, e1.mp h.1⟩
  · exact Or.inr (Or.inl ⟨h.2.1, e2.mp h.2.1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.2.2.1, e3.mp h.2.2.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h.2.2.2, e4.mp h.2.2.2⟩))

include p in
/-- The recurring set is intrinsic: it is the set of finite values taken infinitely often. -/
theorem charP_E_intrinsic :
    E T.pcProfile (wOnset T.k T.s T.n0 triW) =
        {d : ℕ | ∀ M, ∃ n, M ≤ n ∧ T.pcProfile n = (d : ℕ∞)} ∧
      E T.nsProfile (wOnset T.k T.s T.n0 triW) =
        {d : ℕ | ∀ M, ∃ n, M ≤ n ∧ T.nsProfile n = (d : ℕ∞)} :=
  ⟨Set.ext fun d => (charP_periodic p T).1.mem_E_iff d,
    Set.ext fun d => (charP_periodic p T).2.mem_E_iff d⟩

end Main
end ClaudeCP
