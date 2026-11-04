/-
Claude, 27 Sep 2026.  Paper audit for `04_Manuscript/Linear_Bounds_2026-09-27`.

This file imports the three final chains (linear classification, NS–PC comparison,
undecidability) and the lim inf module `PDigits` (byte-identical to
`allprimes_lean_2026-09-25/lean/PDigits.lean`).  It proves, from the proved endpoints only,
the paper statements that are not literally one of those endpoints:

* `periodicity_any_q`, `degree_zero_stable`  (draft `thm:periodicity`, every `q = p^a > kd+s`);
* `E_eq_Rec`                                  (draft: `E(h) = rec(h)`, onset-independent);
* `T2_bound`                                  (draft `eq:linear`, ℕ-floor, `∞` included);
* `T3_full`                                   (draft T3: one fixed value `≤ D` on each easy class,
                                               linear bound on the hard classes from `N(D)` on);
* `liminf_classification`                     (draft T4 lim inf, and T1/T3; `⊤` in T2);
* `common_peaks`                              (draft `cor:common-peaks`, NS finite via comparison);
* `bhat_window`, `bhat_peaks`                 (draft `eq:bhat-window` and the peaks at `(p+1)p^a`);
* `chainBoundPerm_linear`, `chainBound_linear`, `upperComparison_linear_route`
                                              (draft `lem:chains` with the LINEAR budget,
                                               `M = 4r + q`, and the comparison obtained from it).

No hypothesis of any theorem below is a conclusion or an essential lemma: every hypothesis is a
side condition of the displayed paper statement.  The last section prints the statements and
axioms of every declaration cited in the ledger, and checks dependencies with `#uses`.
-/
import UPCDirect
import UDeps
import PDigits

set_option autoImplicit false

namespace PaperAudit
open Filter
open DegreeProfilesReview.Uniform DegreeProfilesReview.Profiles DegreeProfilesReview.SymRep
open ClaudeComparison ClaudeC017

/-! ## 1. Linear classification: consequences of `LinearFinal.linear_classification` -/

section Linear
variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] (T : Template R)

/-- The periodic profile at the linear onset, for either actual profile. -/
theorem periodic {h : ℕ → ℕ∞} (hh : h = T.pcProfile ∨ h = T.nsProfile) :
    PeriodicProfile h (onset T.k T.s T.n0) (period p T.k T.s) :=
  (LinearFinal.linear_classification p T h (by rcases hh with rfl | rfl <;> simp)).1

/-- The ℕ-floor `⌊(n-2s-1)/(2k)⌋` is admissible: its onset is at most `n` once `n ≥ n₀`. -/
theorem onset_floor_le {k s n0 n : ℕ} (hn0 : n0 ≤ n) :
    onset k s n0 ((n - 2 * s - 1) / (2 * k)) ≤ n := by
  unfold onset
  split_ifs with h0
  · exact hn0
  · have h1 : (n - 2 * s - 1) / (2 * k) * (2 * k) ≤ n - 2 * s - 1 := Nat.div_mul_le_self _ _
    have hpos : 1 ≤ (n - 2 * s - 1) / (2 * k) := Nat.one_le_iff_ne_zero.mpr h0
    have hk : 0 < 2 * k := by
      rcases Nat.eq_zero_or_pos (2 * k) with h | h
      · rw [h, Nat.div_zero] at hpos; omega
      · exact h
    have e : 2 * (k * ((n - 2 * s - 1) / (2 * k)) + s) + 1 =
        (n - 2 * s - 1) / (2 * k) * (2 * k) + 2 * s + 1 := by ring
    have h2 : (n - 2 * s - 1) / (2 * k) * (2 * k) ≥ 2 * k :=
      Nat.le_mul_of_pos_left _ hpos
    rw [e]
    generalize (n - 2 * s - 1) / (2 * k) * (2 * k) = t at h1 h2
    omega

/-- **Draft `thm:periodicity`, exact form.**  For `d ≥ 1`, `r = kd+s`, every `p`-power `q > r`
and all `n, n' ≥ n₀` with `n, n' > 2r` and `n ≡ n' (mod q)`: `h n ≤ t ↔ h n' ≤ t` for every
`t ≤ d` (the simultaneous form `eq:periodic`). -/
theorem periodicity_any_q {h : ℕ → ℕ∞} (hh : h = T.pcProfile ∨ h = T.nsProfile) {d a : ℕ}
    (hd : 1 ≤ d) (hq : T.k * d + T.s < p ^ a) {n n' : ℕ} (hn0 : T.n0 ≤ n) (hn0' : T.n0 ≤ n')
    (hn : 2 * (T.k * d + T.s) < n) (hn' : 2 * (T.k * d + T.s) < n')
    (hmod : n % p ^ a = n' % p ^ a) {t : ℕ} (ht : t ≤ d) :
    (h n ≤ (t : ℕ∞) ↔ h n' ≤ (t : ℕ∞)) := by
  have P := periodic p T hh
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hons : ∀ m, T.n0 ≤ m → 2 * (T.k * d + T.s) < m → onset T.k T.s T.n0 d ≤ m := by
    intro m h1 h2
    rw [onset_pos_level hd]
    exact max_le h1 (by omega)
  have hdvd : period p T.k T.s d ∣ p ^ a := by
    unfold period
    rw [if_neg (by omega)]
    obtain ⟨b, hb⟩ := leastPowGt_isPow hp2 (T.k * d + T.s)
    have hle := leastPowGt_le hp2 hq
    rw [hb] at hle ⊢
    exact Nat.pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp2).mp hle)
  have hmod' : n % period p T.k T.s d = n' % period p T.k T.s d :=
    Nat.ModEq.of_dvd hdvd hmod
  exact P.periodic d t ht n n' (hons n hn0 hn) (hons n' hn0' hn') hmod'

include p in
/-- Degree zero is stable beyond `n₀` (period `1`). -/
theorem degree_zero_stable {h : ℕ → ℕ∞} (hh : h = T.pcProfile ∨ h = T.nsProfile) {n n' : ℕ}
    (hn : T.n0 ≤ n) (hn' : T.n0 ≤ n') : (h n ≤ 0 ↔ h n' ≤ 0) := by
  have P := periodic p T hh
  have h0 : onset T.k T.s T.n0 0 = T.n0 := by simp [onset]
  have hQ : period p T.k T.s 0 = 1 := by simp [period]
  have := P.periodic 0 0 le_rfl n n' (by rw [h0]; exact hn) (by rw [h0]; exact hn')
    (by rw [hQ, Nat.mod_one, Nat.mod_one])
  simpa using this

include p in
/-- **`E(h) = rec(h)`**: the recurring set at the linear onset is the set of finite values taken
at infinitely many sizes (`ClaudeUndec.Rec`), so the types do not depend on the onset. -/
theorem E_eq_Rec {h : ℕ → ℕ∞} (hh : h = T.pcProfile ∨ h = T.nsProfile) :
    E h (onset T.k T.s T.n0) = ClaudeUndec.Rec h := by
  ext d
  exact (periodic p T hh).mem_E_iff d

include p in
/-- **Draft `eq:linear` in T2**, with the ℕ-floor and `∞` allowed: for every `n ≥ n₀`,
`⌊(n-2s-1)/(2k)⌋ < h n`. -/
theorem T2_bound {h : ℕ → ℕ∞} (hh : h = T.pcProfile ∨ h = T.nsProfile)
    (h2 : IsT2 h (onset T.k T.s T.n0)) {n : ℕ} (hn : T.n0 ≤ n) :
    (((n - 2 * T.s - 1) / (2 * T.k) : ℕ) : ℕ∞) < h n :=
  (periodic p T hh).T2_gt h2 (onset_floor_le hn)

/-- **Draft T3 in full.**  `D = max E`, a nonempty proper set `U` of residues modulo `Q(D)`; on
each class of `U` the profile is ONE fixed value `v ≤ D` from `N(D)` on; off `U` the linear bound
holds at every `n ≥ N(D)`. -/
theorem T3_full {h : ℕ → ℕ∞} (hh : h = T.pcProfile ∨ h = T.nsProfile)
    (h3 : IsT3 h (onset T.k T.s T.n0)) :
    ∃ D : ℕ, D ∈ E h (onset T.k T.s T.n0) ∧ (∀ d ∈ E h (onset T.k T.s T.n0), d ≤ D) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p T.k T.s D) ∧ U.Nonempty ∧
        (∃ c, c < period p T.k T.s D ∧ c ∉ U) ∧
        (∀ c ∈ U, ∃ v : ℕ, v ≤ D ∧ ∀ n, onset T.k T.s T.n0 D ≤ n →
            n % period p T.k T.s D = c → h n = (v : ℕ∞)) ∧
        (∀ n, onset T.k T.s T.n0 D ≤ n → n % period p T.k T.s D ∉ U →
            (((n - 2 * T.s - 1) / (2 * T.k) : ℕ) : ℕ∞) < h n) := by
  have P := periodic p T hh
  obtain ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, hUeasy, hUhard⟩ := P.T3_structure h3
  refine ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, ?_, ?_⟩
  · intro c hc
    set N := onset T.k T.s T.n0 D
    set Q := period p T.k T.s D
    have hQ : 0 < Q := P.Q_pos D
    have hrep : (c + Q * N) % Q = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hUlt c hc)]
    have hNle : N ≤ c + Q * N := le_add_left (Nat.le_mul_of_pos_left N hQ)
    obtain ⟨v, hvD, hv⟩ := hUeasy (c + Q * N) hNle (by rw [hrep]; exact hc)
    exact ⟨v, hvD, fun n hn hnc => hv n hn (by rw [hnc, hrep])⟩
  · intro n hn hnU
    have hn0 : T.n0 ≤ n := le_trans (n0_le_onset _ _ _ D) hn
    exact hUhard n hn hnU _ (onset_floor_le hn0)

include p in
/-- **The lim inf.**  If some finite value recurs (types T1, T3, T4) the lim inf is the least
recurring value, a finite number; in T2 it is `⊤`. -/
theorem liminf_classification {h : ℕ → ℕ∞} (hh : h = T.pcProfile ∨ h = T.nsProfile) :
    ((IsT1 h ∨ IsT3 h (onset T.k T.s T.n0) ∨ IsT4 h (onset T.k T.s T.n0)) →
      ∃ e ∈ E h (onset T.k T.s T.n0), (∀ x ∈ E h (onset T.k T.s T.n0), e ≤ x) ∧
        liminf h atTop = (e : ℕ∞)) ∧
    (IsT2 h (onset T.k T.s T.n0) → liminf h atTop = ⊤) := by
  have P := periodic p T hh
  refine ⟨fun hT => ClaudeCP.liminf_eq_min P ?_, ClaudeCP.liminf_eq_top P⟩
  rcases hT with h1 | h3 | h4
  · exact (P.bounded_E h1).2
  · exact h3.2.1
  · exact h4.nonempty

/-- **Draft `cor:common-peaks`.**  If the PC profile has type T4 there is a monotone `F` such that,
beyond every bound, some size `n` has a finite recurring PC value `d` with the linear peak
bounds, and at the same `n` the NS degree is finite, between `d` and `F d`. -/
theorem common_peaks (h4 : IsT4 T.pcProfile (onset T.k T.s T.n0)) :
    ∃ F : ℕ → ℕ, Monotone F ∧ ∀ B : ℕ, ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧
      d ∈ E T.pcProfile (onset T.k T.s T.n0) ∧ T.pcProfile n = (d : ℕ∞) ∧
      (d : ℕ∞) ≤ T.nsProfile n ∧ T.nsProfile n ≤ (F d : ℕ∞) ∧
      n ≤ (p + 2) * (T.k * d + T.s) ∧ (n : ℚ) / ((p + 2) * T.k) - T.s / T.k ≤ d := by
  obtain ⟨F, hF, hUC⟩ := ClaudeComparison.upperComparison p T
  refine ⟨F, hF, fun B => ?_⟩
  obtain ⟨n, d, hBn, hBd, hdE, hval, hsize, hrat⟩ :=
    ((LinearFinal.linear_classification p T T.pcProfile (by simp)).2.2.2.2 h4) B
  exact ⟨n, d, hBn, hBd, hdE, hval, hval ▸ T.pcProfile_le_nsProfile n, hUC n d hval, hsize, hrat⟩

include p in
/-- The NS profile is then also of type T4 (common type, linear onset). -/
theorem common_peaks_ns_T4 (h4 : IsT4 T.pcProfile (onset T.k T.s T.n0)) :
    IsT4 T.nsProfile (onset T.k T.s T.n0) :=
  ((ClaudeComparison.types_agree_linear p T).2.2.2).mp h4

end Linear

/-! ## 2. The normalized weak-bijection witness `B̂`: window and explicit peaks -/

section Bhat
open ClaudeUndec
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]

/-- **Draft `eq:bhat-window`.**  If `n = p^a u` with `p ∤ u` and `n ≥ 2p^a`, then
`p^a ≤ d_PC(B̂_n) ≤ d_NS(B̂_n) ≤ p^a + 4`. -/
theorem bhat_window {n a u : ℕ} (hu : ¬ p ∣ u) (hnu : n = p ^ a * u) (h2 : 2 * p ^ a ≤ n) :
    ((p ^ a : ℕ) : ℕ∞) ≤ (template bhat K).pcProfile n ∧
      (template bhat K).pcProfile n ≤ (template bhat K).nsProfile n ∧
      (template bhat K).nsProfile n ≤ ((p ^ a + 4 : ℕ) : ℕ∞) := by
  have hq : 0 < p ^ a := pow_pos hp.out.pos a
  have hn : 0 < n := by omega
  refine ⟨?_, (template bhat K).pcProfile_le_nsProfile n, ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨d, hd, hdle⟩ := DegreeProfilesReview.Profiles.enat_exists_of_le_coe (le_of_lt hlt)
    have hdq : d < p ^ a := by rw [hd] at hlt; exact_mod_cast hlt
    have href : DegreeProfilesReview.PC.Refutes ((template bhat K).inst n) d :=
      (DegreeProfilesReview.PC.pcDegree_le_iff _ d).mp (le_of_eq hd)
    exact bhat_pc_lower p K hn ⟨u, hnu⟩ (by omega) hdq href
  · exact (DegreeProfilesReview.NS.nsDegree_le_iff _ _).mpr (bhat_upper K hn hp.out hu hnu)

/-- **Explicit simultaneous peaks** at `n_a = (p+1)p^a`:
`n_a/(p+1) ≤ d_PC ≤ d_NS ≤ n_a/(p+1) + 4`. -/
theorem bhat_peaks (a : ℕ) :
    (((p + 1) * p ^ a / (p + 1) : ℕ) : ℕ∞) ≤ (template bhat K).pcProfile ((p + 1) * p ^ a) ∧
      (template bhat K).pcProfile ((p + 1) * p ^ a) ≤
        (template bhat K).nsProfile ((p + 1) * p ^ a) ∧
      (template bhat K).nsProfile ((p + 1) * p ^ a) ≤
        (((p + 1) * p ^ a / (p + 1) + 4 : ℕ) : ℕ∞) := by
  have hp2 := hp.out.two_le
  have hdiv : (p + 1) * p ^ a / (p + 1) = p ^ a := Nat.mul_div_cancel_left _ (by omega)
  have hu : ¬ p ∣ p + 1 := by
    intro h
    have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
  have hq : 0 < p ^ a := pow_pos hp.out.pos a
  rw [hdiv]
  refine bhat_window p K (a := a) (u := p + 1) hu (by ring) ?_
  calc 2 * p ^ a ≤ (p + 1) * p ^ a := Nat.mul_le_mul_right _ (by omega)

/-- The sizes `p^a (p(k+1)+1)` used for recurrence lie in the window. -/
theorem bhat_recurrence_sizes (a k : ℕ) :
    ((p ^ a : ℕ) : ℕ∞) ≤ (template bhat K).pcProfile (p ^ a * (p * (k + 1) + 1)) ∧
      (template bhat K).nsProfile (p ^ a * (p * (k + 1) + 1)) ≤ ((p ^ a + 4 : ℕ) : ℕ∞) := by
  have hp2 := hp.out.two_le
  have hu : ¬ p ∣ p * (k + 1) + 1 := by
    intro h
    have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p (k + 1))).mp h
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
  have hq : 0 < p ^ a := pow_pos hp.out.pos a
  have h3 : 2 ≤ p * (k + 1) + 1 := by nlinarith
  have hw := bhat_window p K (a := a) (u := p * (k + 1) + 1) hu rfl
    (calc 2 * p ^ a = p ^ a * 2 := by ring
      _ ≤ p ^ a * (p * (k + 1) + 1) := Nat.mul_le_mul_left _ h3)
  exact ⟨hw.1, hw.2.2⟩

end Bhat

/-! ## 3. The chain bound with the LINEAR exactness budget (draft `lem:chains`) -/

section Chains
open DegreeProfilesReview.ShiftedM5 DegreeProfilesReview.Shifted SelfContainedCycle003 ClaudeCP

/-- **Draft `lem:chains`, linear route, explicit bound.**  Fix `q = p^a > 2r`.  Using the linear
top-power witnesses (`LinearFinal.topWitnessHypothesis_linear`, budget `2(2r) − 1`) and repeated
deletion down to rank `≤ M = 4r + q`, every strict chain of invariant subspaces of `K[𝒰_N]`, at
every rank `N`, has at most `#𝒰_M` strict inclusions. -/
theorem chainBoundPerm_linear (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K]
    [CharP K p] (𝒰 : BasisSystem) {r : ℕ} (hU : 𝒰.Bounded r) (a : ℕ) (hs : r + r < p ^ a) :
    ∀ N (W : Fin (Nat.card (𝒰.Rk (4 * r + p ^ a)) + 2) → Submodule K (𝒰.Rk N →₀ K)),
      (∀ i, IsInv (permRep K 𝒰 N).ρ (W i)) → ¬ StrictMono W := by
  classical
  set M := 4 * r + p ^ a with hM
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W hW hmono
    by_cases hN : N ≤ M
    · letI : Fintype (𝒰.Rk N) := Fintype.ofFinite _
      apply not_strictMono_of_finrank_le _ W hmono
      rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
      exact card_rk_le 𝒰 hN
    · obtain ⟨n, rfl⟩ : ∃ n, N = n + p ^ a := ⟨N - p ^ a, by omega⟩
      have hn : 2 * (r + r) - 1 ≤ n := by omega
      obtain ⟨c, hc, w, hw⟩ :=
        LinearFinal.topWitnessHypothesis_linear p K (r + r) a n hs hn
      have hrq : r < p ^ a := by omega
      obtain ⟨W', hW', hmono'⟩ := chain_step hc hrq hU hs hw le_rfl W hW hmono
      have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
      exact ih n (by omega) W' hW' hmono'

/-- The linear-route chain bound for polynomials of degree `≤ t` over ANY field of
characteristic `p`, with the explicit length `L_t = #(monomials of degree ≤ t)_{M_t}`,
`M_t = 4kt + p^(2kt+1)`.  (Same scalar-extension argument as `chainBound_of_bounded`.) -/
theorem chainBound_linear_explicit (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p]
    (𝒰 : BasisSystem) {k : ℕ} (hk : 𝒰.Bounded k) (t n : ℕ)
    (W : Fin (Nat.card ((𝒰.mon t).Rk (4 * (k * t) + p ^ (2 * (k * t) + 1))) + 2) →
      Submodule R (MvPolynomial (𝒰.Rk n) R))
    (hWt : ∀ i, W i ≤ MvPolynomial.restrictTotalDegree (𝒰.Rk n) R t)
    (hWinv : ∀ i (g : Sfin n), ∀ f ∈ W i, MvPolynomial.rename (fun v => g • v) f ∈ W i) :
    ¬ StrictMono W := by
  classical
  have hs : k * t + k * t < p ^ (2 * (k * t) + 1) := by
    have := Nat.lt_pow_self (Fact.out : p.Prime).one_lt (n := 2 * (k * t) + 1)
    omega
  have hL := chainBoundPerm_linear p (AlgebraicClosure R) (𝒰.mon t)
    (BasisSystem.mon_bounded hk t) (2 * (k * t) + 1) hs
  intro hmono
  let W1 : Fin (Nat.card ((𝒰.mon t).Rk (4 * (k * t) + p ^ (2 * (k * t) + 1))) + 2) → Submodule R ((𝒰.mon t).Rk n →₀ R) := fun i => (W i).map (cf 𝒰 t n)
  have hW1inv : ∀ i, IsInv (Representation.ofMulAction R (Sfin n) ((𝒰.mon t).Rk n)) (W1 i) := by
    rintro i g _ ⟨f, hf, rfl⟩
    change Representation.ofMulAction R (Sfin n) ((𝒰.mon t).Rk n) g (cf 𝒰 t n f) ∈ W1 i
    rw [← cf_rename]
    exact Submodule.mem_map_of_mem (hWinv i g f hf)
  have hW1mono : StrictMono W1 := by
    intro i j hij
    refine lt_of_le_of_ne (Submodule.map_mono (hmono hij).le) fun heq => ?_
    apply not_le_of_gt (hmono hij)
    intro f hf
    have hmem : cf 𝒰 t n f ∈ W1 i := by
      change cf 𝒰 t n f ∈ W1 i
      rw [heq]
      exact Submodule.mem_map_of_mem hf
    obtain ⟨u, hu, hfu⟩ := hmem
    have hdiff : f - u ∈ MvPolynomial.restrictTotalDegree (𝒰.Rk n) R t :=
      sub_mem (hWt j hf) (hWt i hu)
    have h0 : cf 𝒰 t n (f - u) = 0 := by rw [map_sub, hfu, sub_self]
    have := cf_injOn hdiff h0
    rw [sub_eq_zero] at this
    rw [this]
    exact hu
  exact hL n (fun i => extS (W1 i)) (fun i => extS_isInv (hW1inv i))
    (fun i j hij => extS_strict (hW1mono hij))

/-- `ChainBound` from the linear route. -/
theorem chainBound_linear (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p]
    (𝒰 : BasisSystem) {k : ℕ} (hk : 𝒰.Bounded k) : ChainBound R 𝒰 :=
  fun t => ⟨_, fun n W hWt hWinv => chainBound_linear_explicit p 𝒰 hk t n W hWt hWinv⟩

/-- **Draft `thm:comparison` through the linear chain bound**: a monotone `F` with
`d_NS(n) ≤ F(d_PC(n))` at every size, obtained without the quadratic witness theorem. -/
theorem upperComparison_linear_route (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p]
    (T : Template R) :
    ∃ F : ℕ → ℕ, Monotone F ∧ UpperComparison F T.pcProfile T.nsProfile :=
  upperComparison_of_chainBound T (chainBound_linear p T.Var T.var_bounded)

end Chains

/-! ## 3b. The direct DCP route used in the exactness appendix

The returned chain `LinearFinal.exactness_linear` reaches `DCP_b(N)` through D's window induction
(Lemma D on columns, row and column peels, `HALF_b(b+2)`), using the full-board realisation only in
the window.  Since the full-board realisation holds for EVERY size, `DCP_b(N)` follows at once;
this is the route written in `exactness_appendix.tex`.  Every step below is a returned theorem. -/

section DirectDCP
open Finset

/-- **Rook form of `DCP_b(N)` on the full board, every `b`, `N`** (FORCE + realisation). -/
theorem dcpr_full (K : Type) [Field K] (b N : ℕ) : ClaudeDCP.DCPR (Fin N) K b N := by
  intro R C hR hC F hF
  have hRu : R = univ := Finset.eq_univ_of_card R (by rw [hR, Fintype.card_fin])
  have hCu : C = univ := Finset.eq_univ_of_card C (by rw [hC, Fintype.card_fin])
  subst hRu hCu
  exact BRealise.real_of_forceExists (RForce.forceExists K N) b F hF

/-- **Top-power witnesses with budget `2r − 1`, direct route**: FORCE + realisation give
`DCP_b` at every `N`, and B's layer induction (Theorem A) gives the witnesses. -/
theorem topWitnessHypothesis_direct (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [IsAlgClosed L]
    [CharP L p] : ClaudeCP.TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  BExact.topWitnessHypothesis_of_dcp' p L fun b N hb hN =>
    ClaudeDCP.dcpHypB_of_dcpr hb (by omega) (dcpr_full L b N)

/-- **Exactness of the actual deletion functor with budget `2r − 1`, direct route.** -/
theorem exactness_direct (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [IsAlgClosed L]
    [CharP L p] : ClaudeLinear.ExactnessHypothesis p L (fun r => 2 * r - 1) :=
  ClaudeLinear.exactness_of_top (topWitnessHypothesis_direct p L)

end DirectDCP

/-! ## 4. Non-vacuity: concrete instances -/

section Instances
open ClaudeUndec

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

-- B̂ over F_3 at n = 4·3² = 36: degrees in [9, 13] for both systems.
example : ((9 : ℕ) : ℕ∞) ≤ (template bhat (ZMod 3)).pcProfile 36 ∧
    (template bhat (ZMod 3)).pcProfile 36 ≤ (template bhat (ZMod 3)).nsProfile 36 ∧
    (template bhat (ZMod 3)).nsProfile 36 ≤ ((13 : ℕ) : ℕ∞) := by
  have := bhat_peaks 3 (ZMod 3) 2
  norm_num at this
  exact this

-- The T3 witness ψ₃ over F_2: T3 structure for its NS profile, in the linear-onset form.
example : ∃ D : ℕ, D ∈ E (template (psi3 2) (ZMod 2)).nsProfile
      (onset (template (psi3 2) (ZMod 2)).k (template (psi3 2) (ZMod 2)).s
        (template (psi3 2) (ZMod 2)).n0) ∧ True := by
  have h3 : NSType (template (psi3 2) (ZMod 2)) 3 := (wit_type 2 (ZMod 2)) 3 (by simp)
  obtain ⟨D, hD, -⟩ := T3_full 2 (template (psi3 2) (ZMod 2)) (Or.inr rfl) h3
  exact ⟨D, hD, trivial⟩

-- The T4 witness B̂ over F_2: common finite peaks for NS and PC.
example : ∃ F : ℕ → ℕ, Monotone F ∧ ∀ B : ℕ, ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧
    (template bhat (ZMod 2)).pcProfile n = (d : ℕ∞) ∧
    (template bhat (ZMod 2)).nsProfile n ≤ (F d : ℕ∞) := by
  have h4 : PCType (template bhat (ZMod 2)) 4 := (wit_pc_type 2 (ZMod 2)) 4 (by simp)
  obtain ⟨F, hF, hP⟩ := common_peaks 2 (template bhat (ZMod 2)) h4
  exact ⟨F, hF, fun B => by
    obtain ⟨n, d, h1, h2, -, h4', -, h6, -⟩ := hP B
    exact ⟨n, d, h1, h2, h4', h6⟩⟩

-- The T4 witness B̂ over F_2: finite lim inf.
example : ∃ e : ℕ, liminf (template bhat (ZMod 2)).nsProfile atTop = (e : ℕ∞) := by
  have h4 : NSType (template bhat (ZMod 2)) 4 := (wit_type 2 (ZMod 2)) 4 (by simp)
  obtain ⟨e, -, -, he⟩ :=
    (liminf_classification 2 (template bhat (ZMod 2)) (Or.inr rfl)).1 (Or.inr (Or.inr h4))
  exact ⟨e, he⟩

-- The T2 witness η over F_2: the linear bound at every n ≥ n₀, from the general theorem.
example (n : ℕ) (hn : (template eta (ZMod 2)).n0 ≤ n) :
    (((n - 2 * (template eta (ZMod 2)).s - 1) / (2 * (template eta (ZMod 2)).k) : ℕ) : ℕ∞) <
      (template eta (ZMod 2)).pcProfile n := by
  have h2 : PCType (template eta (ZMod 2)) 2 := (wit_pc_type 2 (ZMod 2)) 2 (by simp)
  exact T2_bound 2 (template eta (ZMod 2)) (Or.inl rfl) h2 hn

end Instances

end PaperAudit

/-! ## 5. Statements, axioms and dependencies of every ledger declaration -/

-- New paper-audit corollaries
#check @PaperAudit.periodicity_any_q
#check @PaperAudit.degree_zero_stable
#check @PaperAudit.E_eq_Rec
#check @PaperAudit.T2_bound
#check @PaperAudit.T3_full
#check @PaperAudit.liminf_classification
#check @PaperAudit.common_peaks
#check @PaperAudit.common_peaks_ns_T4
#check @PaperAudit.bhat_window
#check @PaperAudit.bhat_peaks
#check @PaperAudit.bhat_recurrence_sizes
#check @PaperAudit.chainBoundPerm_linear
#check @PaperAudit.chainBound_linear_explicit
#check @PaperAudit.upperComparison_linear_route
#check @PaperAudit.dcpr_full
#check @PaperAudit.topWitnessHypothesis_direct
#check @PaperAudit.exactness_direct
#print axioms PaperAudit.periodicity_any_q
#print axioms PaperAudit.degree_zero_stable
#print axioms PaperAudit.E_eq_Rec
#print axioms PaperAudit.T2_bound
#print axioms PaperAudit.T3_full
#print axioms PaperAudit.liminf_classification
#print axioms PaperAudit.common_peaks
#print axioms PaperAudit.common_peaks_ns_T4
#print axioms PaperAudit.bhat_window
#print axioms PaperAudit.bhat_peaks
#print axioms PaperAudit.bhat_recurrence_sizes
#print axioms PaperAudit.chainBoundPerm_linear
#print axioms PaperAudit.chainBound_linear_explicit
#print axioms PaperAudit.upperComparison_linear_route
#print axioms PaperAudit.dcpr_full
#print axioms PaperAudit.topWitnessHypothesis_direct
#print axioms PaperAudit.exactness_direct

-- Definitions the statements rest on
#print DegreeProfilesReview.Uniform.Template
#print DegreeProfilesReview.Uniform.BasisSystem
#print DegreeProfilesReview.Uniform.Template.pcProfile
#print DegreeProfilesReview.Uniform.Template.nsProfile
#print DegreeProfilesReview.Profiles.PeriodicProfile
#print DegreeProfilesReview.Profiles.onset
#print DegreeProfilesReview.Profiles.period
#print DegreeProfilesReview.Profiles.leastPowGt
#print DegreeProfilesReview.Profiles.EventuallyBounded
#print DegreeProfilesReview.Profiles.UpperComparison
#print ClaudeLinear.ExactnessHypothesis
#print ClaudeLinear.ShiftedExact
#print ClaudeCP.TopWitnessHypothesis
#print ClaudeCP.IsTopWitness
#print ClaudeCP.zEltP
#print SelfContainedCycle003.TupleRelations
#print SelfContainedCycle003.CanonicalClass
#print DegreeProfilesReview.Shifted.Generic
#print DegreeProfilesReview.ShiftedM5.Ψhat
#print DegreeProfilesReview.Deletion.M5w
#print ClaudeC017.ChainBound

-- Linear chain
#check @LinearFinal.linear_classification
#check @LinearFinal.exactness_linear
#check @LinearFinal.topWitnessHypothesis_linear
#check @SelfContainedCycle004.canonicalM5w
#check @DegreeProfilesReview.FieldDescent.pcDegree_map
#check @DegreeProfilesReview.FieldDescent.nsDegree_map
#check @DegreeProfilesReview.Uniform.Template.pcProfile_le_nsProfile
#check @DegreeProfilesReview.Profiles.period_le
#check @DegreeProfilesReview.Profiles.PeriodicProfile.exactly_one
#check @DegreeProfilesReview.Profiles.PeriodicProfile.T3_structure
#check @ClaudeCP.liminf_eq_min
#check @ClaudeCP.liminf_eq_top
#check @SelfContainedCycle084.topProjector_annihilates
#check @SelfContainedCycle084.topProjector_idempotent
#print axioms LinearFinal.linear_classification
#print axioms LinearFinal.exactness_linear
#print axioms SelfContainedCycle004.canonicalM5w
#print axioms DegreeProfilesReview.FieldDescent.pcDegree_map
#print axioms DegreeProfilesReview.FieldDescent.nsDegree_map
#print axioms ClaudeCP.liminf_eq_min

-- Comparison chain
#check @ClaudeComparison.comparison
#check @ClaudeComparison.upperComparison
#check @ClaudeComparison.types_agree_linear
#check @ClaudeComparison.common_type_linear
#check @ClaudeComparison.detect
#check @ClaudeComparison.delImg_strict
#check @ClaudeComparison.chainBoundPerm
#print axioms ClaudeComparison.comparison
#print axioms ClaudeComparison.types_agree_linear
#print axioms ClaudeComparison.common_type_linear
#print axioms ClaudeComparison.detect

-- Examples and matching obstruction
#check @SelfContainedCycle058.no_PCRefutes_rectangle
#check @SelfContainedCycle072.G_both_linear
#check @ClaudeUndec.psi1_nsRefutes
#check @ClaudeUndec.eta_lower
#check @ClaudeUndec.eta_pc_lower
#check @ClaudeUndec.chi_nsRefutes
#check @ClaudeUndec.chi_model
#check @ClaudeUndec.psi3_eq_eta
#check @ClaudeUndec.psi3_pc_eq_eta
#check @ClaudeUndec.bhat_upper
#check @ClaudeUndec.bhat_lower
#check @ClaudeUndec.bhat_pc_lower
#check @ClaudeUndec.bhat_le_five
#check @ClaudeUndec.bhat_pc_le_five
#check @ClaudeUndec.wit_type
#check @ClaudeUndec.wit_pc_type
#print axioms SelfContainedCycle058.no_PCRefutes_rectangle
#print axioms SelfContainedCycle072.G_both_linear
#print axioms ClaudeUndec.bhat_upper
#print axioms ClaudeUndec.bhat_pc_lower
#print axioms ClaudeUndec.wit_type
#print axioms ClaudeUndec.wit_pc_type

-- Compiler, switch, certificate, join, reduction
#check @ClaudeUndec.hasRoot_iff
#check @ClaudeUndec.templateParams_primrec
#check @ClaudeUndec.switch_i
#check @ClaudeUndec.no_large_model
#check @ClaudeUndec.theta_nsRefutes
#check @ClaudeUndec.theta_eventually_bounded
#check @ClaudeUndec.nsRefutes_of_local
#check @ClaudeUndec.haltBound
#check @ClaudeUndec.thM
#check @ClaudeUndec.nsDegree_conj_eq_left
#check @ClaudeUndec.pcDegree_conj_eq_left
#check @ClaudeUndec.nsDegree_join_ge
#check @ClaudeUndec.nsDegree_join_le
#check @ClaudeUndec.pcDegree_join_ge
#check @ClaudeUndec.pcDegree_join_le
#check @ClaudeUndec.iType_sandwich
#check @ClaudeUndec.eval_dom_iff_halts
#check @ClaudeUndec.red2_promised
#check @ClaudeUndec.red2_primrec
#check @ComputablePred.halting_problem
#check @ClaudeUndec.undecidable_disjoint_NS
#check @ClaudeUndec.undecidable_disjoint_PC_direct
#check @ClaudeUndec.undecidable_pair_NS
#check @ClaudeUndec.undecidable_pair_PC_direct
#check @ClaudeUndec.undecidable_union_NS
#check @ClaudeUndec.undecidable_union_PC_direct
#print axioms ClaudeUndec.hasRoot_iff
#print axioms ClaudeUndec.nsRefutes_of_local
#print axioms ClaudeUndec.theta_nsRefutes
#print axioms ClaudeUndec.undecidable_disjoint_NS
#print axioms ClaudeUndec.undecidable_disjoint_PC_direct
#print axioms ComputablePred.halting_problem

-- Dependencies (transitive closure of constants): what the new corollaries rest on
#uses PaperAudit.T3_full LinearFinal.linear_classification
#uses PaperAudit.T3_full ClaudeComparison.upperComparison
#uses PaperAudit.liminf_classification ClaudeCP.liminf_eq_min
#uses PaperAudit.common_peaks ClaudeComparison.upperComparison
#uses PaperAudit.bhat_window SelfContainedCycle058.no_PCRefutes_rectangle
#uses PaperAudit.bhat_window ClaudeComparison.upperComparison
#uses PaperAudit.upperComparison_linear_route LinearFinal.topWitnessHypothesis_linear
#uses PaperAudit.upperComparison_linear_route ClaudeCP.topWitnessHypothesis_of_isAlgClosed
#uses ClaudeComparison.comparison ClaudeCP.topWitnessHypothesis_of_isAlgClosed
#uses LinearFinal.linear_classification RForce.forceExists
#uses LinearFinal.linear_classification SelfContainedCycle084.topProjector_annihilates
#uses LinearFinal.linear_classification ClaudeCP.topWitnessHypothesis_of_isAlgClosed
#uses PaperAudit.exactness_direct ClaudeDCP.half_succ_succ
#uses PaperAudit.exactness_direct ClaudeDCP.col_peel
#uses PaperAudit.exactness_direct ClaudeDCP.colSplit
#uses PaperAudit.exactness_direct BExact.piRel_spec
#uses PaperAudit.exactness_direct BExact.cone_spec
#uses PaperAudit.exactness_direct BExact.blockSection_spec
#uses PaperAudit.exactness_direct BExact.layer_step
#uses PaperAudit.exactness_direct BExact.P2_of_transpose
#uses PaperAudit.exactness_direct ClaudeCP.top_preserves_finiteLimits
#uses PaperAudit.exactness_direct SelfContainedCycle084.topProjector_annihilates
#uses PaperAudit.exactness_direct RForce.gp
#uses PaperAudit.exactness_direct BLemmaL.lemmaL_solve_gen
#uses PaperAudit.exactness_direct BExact.prop6PatHyp_of_generic
#uses PaperAudit.exactness_direct ClaudeCP.topWitnessHypothesis_of_isAlgClosed
#uses LinearFinal.exactness_linear ClaudeDCP.half_succ_succ
#check @ClaudeLinear.exactness_of_top
#check @ClaudeLinear.periodic_of_exactness
#check @ClaudeLinear.linear_of_exactness
#check @ClaudeCP.top_map_exact
#check @ClaudeCP.topProjectionEquiv
#check @ClaudeCP.topElt_relations
#check @SelfContainedCycle013.template_pc_step_exact
#check @SelfContainedCycle013.template_ns_step_exact
#check @SelfContainedCycle013.unit_simple
#check @BExact.topWitnessHypothesis_of_dcp'
#check @BExact.prop6PatHyp_of_generic
#check @BExact.lemmaD
#check @ClaudeDCP.dcpHypB_of_dcpr
#check @BRealise.realisationFromForce
#check @RForce.forceExists
#check @RForce.gp
#check @BLemmaL.lemmaL_solve_gen

-- Declarations cited in exactness_appendix.tex (each must exist)
#check @BLemmaL.lex_lt_of_agree
#check @BRealise.realisation_of_force
#check @BExact.piRel_spec
#check @BExact.cone_spec
#check @BExact.blockSection_spec
#check @BExact.nilSection_spec
#check @BExact.thm5_filt
#check @BExact.P1_concrete
#check @BExact.Tsoc_concrete
#check @BExact.P2_of_transpose
#check @BExact.Ttop_of_transpose
#check @BExact.layer_step
#check @BExact.prop6Hyp_of_pat
#check @ClaudeCP.tuple_pure
#check @DegreeProfilesReview.Shifted.mem_range_pow_of_degreeData
#check @DegreeProfilesReview.Shifted.degreeData
#check @DegreeProfilesReview.ShiftedM5.δ'
#check @DegreeProfilesReview.ShiftedM5.δ'_mat
#check @DegreeProfilesReview.ShiftedM5.κ'
#check @DegreeProfilesReview.ShiftedM5.δ'_prod
#check @SelfContainedCycle084.topProjector_on_kernel
#check @SelfContainedCycle084.kernel_residual_in_range
#check @ClaudeDCP.zb_Frk
#check @ClaudeDCP.sum_row_realFn
#check @ClaudeDCP.zb_realFn
#check @RForce.zb_contract
#check @RForce.lexFirst_of_corner
