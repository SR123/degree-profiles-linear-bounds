/-
Uniform consequences, Claude return 002 (5 October 2026).  Part 3: the indexed target profiles
and the four-case quantitative endpoint.

For a template `T` over a field `R` of prime characteristic `p` and a bounded-support indexed
target `G`:

* `pcProfile n = ⨆_{b ∈ B_n} tpcDegree (T.inst n) (G_{b,n})`: the largest of the ACTUAL least
  ordinary-PC derivation degrees of the targets at size `n` (`⊤` if one is not derivable);
  `pcProfile n ≤ d ↔ AllPC n d`;
* `nsProfile n = ⨆_{b ∈ B_n} tnsDegree (T.inst n) (G_{b,n})`, likewise for total-product NS;
* for ONE fixed global orbit (`G.orbit o`), the profile at every rank `n ≥ t` is the least degree
  of ANY representative (`orbit_pcProfile_eq_rep`, `orbit_nsProfile_eq_rep`);
* threshold periodicity with the safe parameters `k' = 2k`, `s' = s + t` and starting rank
  `n_I = max(n₀, 1, k·DG + t)`: onset `max(n_I, 2(2kd + s + t) + 1)`, period the least `p`-power
  above `2kd + s + t`; zero stability;
* (P), exactly one of T1–T4, and the linear bounds with `k' = 2k`, `s' = s + t`, for BOTH
  profiles; the PC bounds come from the indexed PC transfer, not from the NS comparison;
* T2 in the extended order (value `⊤` allowed): `h(n) > ⌊(n − 2(s+t) − 1)/(4k)⌋` for every
  `n ≥ n_I`;
* the full T3 split: `D = max E`, nonempty proper set `U` of easy residues modulo `Q(D)`, ONE
  value `v ≤ D` on each easy class from `N(D)` on, the linear bound on the hard classes;
* arbitrarily large FINITE T4 peaks `h(n) = d` with `n ≤ (p+2)(2kd + s + t)`;
* the lim inf: least recurring value (finite) in T1, T3, T4; `⊤` in T2;
* the uniform comparison `PC ≤ NS ≤ F ∘ PC` from the whole-consequence inclusion, the common
  type, and common finite T4 peaks.

Exact equality of the PC and NS degrees and equality of their recurring sets are NOT claimed.
Values below the onset are unconstrained (finitely many exceptional sizes).
-/
import UCIndexedTransfer

set_option autoImplicit false

open MvPolynomial Filter

namespace UniformConsequence.Indexed

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.Profiles
open UniformConsequence

/-! ### Generic statements for a periodic profile -/

section Generic

variable {p k s n0 : ℕ} {h : ℕ → ℕ∞}

/-- The ℕ-floor `⌊(n-2s-1)/(2k)⌋` is admissible: its onset is at most `n` once `n ≥ n₀`. -/
theorem onset_floor_le' {n : ℕ} (hn0 : n0 ≤ n) :
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
    generalize (n - 2 * s - 1) / (2 * k) * (2 * k) = u at h1 h2
    omega

/-- **T2 in the extended order** for any periodic profile: every value at `n ≥ n₀` (including
`⊤`) exceeds `⌊(n-2s-1)/(2k)⌋`. -/
theorem T2_floor (P : PeriodicProfile h (onset k s n0) (period p k s))
    (h2 : IsT2 h (onset k s n0)) {n : ℕ} (hn : n0 ≤ n) :
    (((n - 2 * s - 1) / (2 * k) : ℕ) : ℕ∞) < h n :=
  P.T2_gt h2 (onset_floor_le' hn)

/-- **The full T3 split** for any periodic profile. -/
theorem T3_split (P : PeriodicProfile h (onset k s n0) (period p k s))
    (h3 : IsT3 h (onset k s n0)) :
    ∃ D : ℕ, D ∈ E h (onset k s n0) ∧ (∀ d ∈ E h (onset k s n0), d ≤ D) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p k s D) ∧ U.Nonempty ∧
        (∃ c, c < period p k s D ∧ c ∉ U) ∧
        (∀ c ∈ U, ∃ v : ℕ, v ≤ D ∧ ∀ n, onset k s n0 D ≤ n →
            n % period p k s D = c → h n = (v : ℕ∞)) ∧
        (∀ n, onset k s n0 D ≤ n → n % period p k s D ∉ U →
            (((n - 2 * s - 1) / (2 * k) : ℕ) : ℕ∞) < h n) := by
  obtain ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, hUeasy, hUhard⟩ := P.T3_structure h3
  refine ⟨D, hDE, hDmax, U, hUlt, hUne, hUprop, ?_, ?_⟩
  · intro c hc
    set N := onset k s n0 D
    set Q := period p k s D
    have hQ : 0 < Q := P.Q_pos D
    have hrep : (c + Q * N) % Q = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hUlt c hc)]
    have hNle : N ≤ c + Q * N := le_add_left (Nat.le_mul_of_pos_left N hQ)
    obtain ⟨v, hvD, hv⟩ := hUeasy (c + Q * N) hNle (by rw [hrep]; exact hc)
    exact ⟨v, hvD, fun n hn hnc => hv n hn (by rw [hnc, hrep])⟩
  · intro n hn hnU
    have hn0 : n0 ≤ n := le_trans (n0_le_onset _ _ _ D) hn
    exact hUhard n hn hnU _ (onset_floor_le' hn0)

/-- **The lim inf** for any periodic profile. -/
theorem liminf_of_periodic (P : PeriodicProfile h (onset k s n0) (period p k s)) :
    ((IsT1 h ∨ IsT3 h (onset k s n0) ∨ IsT4 h (onset k s n0)) →
      ∃ e ∈ E h (onset k s n0), (∀ x ∈ E h (onset k s n0), e ≤ x) ∧
        liminf h atTop = (e : ℕ∞)) ∧
    (IsT2 h (onset k s n0) → liminf h atTop = ⊤) := by
  refine ⟨fun hT => ClaudeCP.liminf_eq_min P ?_, ClaudeCP.liminf_eq_top P⟩
  rcases hT with h1 | h3 | h4
  · exact (P.bounded_E h1).2
  · exact h3.2.1
  · exact h4.nonempty

end Generic

/-! ### The indexed target profiles -/

theorem one_le_twoK {R : Type} [Field R] (T : Template R) : 1 ≤ 2 * T.k := by
  have := T.hk; omega

namespace ITarget

variable {R : Type} [Field R] {T : Template R} (G : ITarget T)

/-- **The ordinary-PC indexed target profile**: the largest actual least PC derivation degree of
the targets at size `n`. -/
noncomputable def pcProfile (n : ℕ) : ℕ∞ := ⨆ b : G.B.Rk n, tpcDegree (T.inst n) (G.poly n b)

/-- **The total-product NS indexed target profile.** -/
noncomputable def nsProfile (n : ℕ) : ℕ∞ := ⨆ b : G.B.Rk n, tnsDegree (T.inst n) (G.poly n b)

/-- The fixed starting rank `n_I = max(n₀, max 1 (k·DG + t))`. -/
noncomputable def nI : ℕ := max T.n0 G.aux.n0

theorem one_le_nI : 1 ≤ G.nI := le_trans (le_max_left 1 _) (le_max_right T.n0 _)

theorem pcProfile_le_iff (n d : ℕ) : G.pcProfile n ≤ (d : ℕ∞) ↔ G.AllPC n d := by
  unfold pcProfile AllPC
  rw [iSup_le_iff]
  exact forall_congr' fun b => tpcDegree_le_iff_mem _ _ _

theorem nsProfile_le_iff (n d : ℕ) : G.nsProfile n ≤ (d : ℕ∞) ↔ G.AllNS n d := by
  unfold nsProfile AllNS
  rw [iSup_le_iff]
  exact forall_congr' fun b => tnsDegree_le_iff_mem _ _ _

theorem pcProfile_le_nsProfile (n : ℕ) : G.pcProfile n ≤ G.nsProfile n :=
  iSup_mono fun _ => tpcDegree_le_tnsDegree _ _

/-- **Degree floor.**  Beyond `max 1 (k·DG + t)` neither profile is below `maxDeg`. -/
theorem maxDeg_le_pcProfile {n : ℕ} (hn : G.aux.n0 ≤ n) : (G.maxDeg : ℕ∞) ≤ G.pcProfile n := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hx, -⟩ := enat_exists_of_le_coe (le_of_lt hlt)
  rw [hx, Nat.cast_lt] at hlt
  exact (G.not_all_of_lt hn hlt).1 ((G.pcProfile_le_iff n x).mp (le_of_eq hx))

theorem maxDeg_le_nsProfile {n : ℕ} (hn : G.aux.n0 ≤ n) : (G.maxDeg : ℕ∞) ≤ G.nsProfile n :=
  le_trans (G.maxDeg_le_pcProfile hn) (G.pcProfile_le_nsProfile n)

/-- **One fixed orbit: the profile is the least degree of any representative.** -/
theorem orbit_pcProfile_eq_rep (o : G.B.Obj) {n : ℕ} {b0 : G.B.Rk n} (hb0 : G.InOrbit o b0) :
    (G.orbit o).pcProfile n = tpcDegree (T.inst n) (G.poly n b0) :=
  enat_eq_of_forall_le_iff fun d => by
    rw [pcProfile_le_iff, tpcDegree_le_iff_mem, G.rep_iff_orbit_pc o hb0]

theorem orbit_nsProfile_eq_rep (o : G.B.Obj) {n : ℕ} {b0 : G.B.Rk n} (hb0 : G.InOrbit o b0) :
    (G.orbit o).nsProfile n = tnsDegree (T.inst n) (G.poly n b0) :=
  enat_eq_of_forall_le_iff fun d => by
    rw [nsProfile_le_iff, tnsDegree_le_iff_mem, G.rep_iff_orbit_ns o hb0]

/-- **Several orbits.**  The aggregate profile is the supremum of the orbit profiles. -/
theorem pcProfile_eq_iSup_orbit (n : ℕ) :
    G.pcProfile n = ⨆ o : G.B.Obj, (G.orbit o).pcProfile n :=
  enat_eq_of_forall_le_iff fun d => by
    rw [pcProfile_le_iff, iSup_le_iff, allPC_iff_forall_orbit]
    exact forall_congr' fun o => (pcProfile_le_iff _ n d).symm

theorem nsProfile_eq_iSup_orbit (n : ℕ) :
    G.nsProfile n = ⨆ o : G.B.Obj, (G.orbit o).nsProfile n :=
  enat_eq_of_forall_le_iff fun d => by
    rw [nsProfile_le_iff, iSup_le_iff, allNS_iff_forall_orbit]
    exact forall_congr' fun o => (nsProfile_le_iff _ n d).symm

/-! #### Threshold periodicity with linear onset -/

variable (p : ℕ) [Fact p.Prime] [CharP R p]

/-- **One deletion step for the indexed profiles.** -/
theorem profile_step {d a n : ℕ} (hn : G.nI ≤ n) (hW : 2 * G.supp d - 1 ≤ n)
    (hq : G.supp d < p ^ a) :
    (G.pcProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ G.pcProfile n ≤ (d : ℕ∞)) ∧
    (G.nsProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ G.nsProfile n ≤ (d : ℕ∞)) := by
  rw [pcProfile_le_iff, pcProfile_le_iff, nsProfile_le_iff, nsProfile_le_iff]
  exact indexed_transfer p G (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)
    hW hq

theorem thresholdPeriodic_pc : ThresholdPeriodic p (2 * T.k) (T.s + G.t) G.nI G.pcProfile := by
  intro u _ a ha n m hn hm h2n h2m hc
  have h2n' : 2 * G.supp u < n := h2n
  have h2m' : 2 * G.supp u < m := h2m
  refine congr_of_step (Pr := fun x => G.pcProfile x ≤ (u : ℕ∞)) (q := p ^ a)
    (B := max G.nI (2 * G.supp u + 1)) ?_ (max_le hn h2n') (max_le hm h2m') hc
  intro x hx
  exact (G.profile_step p (le_trans (le_max_left _ _) hx)
    (by have := le_max_right G.nI (2 * G.supp u + 1); omega) ha).1

theorem thresholdPeriodic_ns : ThresholdPeriodic p (2 * T.k) (T.s + G.t) G.nI G.nsProfile := by
  intro u _ a ha n m hn hm h2n h2m hc
  have h2n' : 2 * G.supp u < n := h2n
  have h2m' : 2 * G.supp u < m := h2m
  refine congr_of_step (Pr := fun x => G.nsProfile x ≤ (u : ℕ∞)) (q := p ^ a)
    (B := max G.nI (2 * G.supp u + 1)) ?_ (max_le hn h2n') (max_le hm h2m') hc
  intro x hx
  exact (G.profile_step p (le_trans (le_max_left _ _) hx)
    (by have := le_max_right G.nI (2 * G.supp u + 1); omega) ha).2

omit [Fact p.Prime] [CharP R p] in
theorem zeroStable_pc : ZeroStable G.nI G.pcProfile := by
  intro n m hn hm
  rw [pcProfile_le_iff, pcProfile_le_iff,
    G.allPC_zero_iff (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn),
    G.allPC_zero_iff (le_trans (le_max_left _ _) hm) (le_trans (le_max_right _ _) hm)]

omit [Fact p.Prime] [CharP R p] in
theorem zeroStable_ns : ZeroStable G.nI G.nsProfile := by
  intro n m hn hm
  rw [nsProfile_le_iff, nsProfile_le_iff,
    G.allNS_zero_iff (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn),
    G.allNS_zero_iff (le_trans (le_max_left _ _) hm) (le_trans (le_max_right _ _) hm)]

/-- **(P) for the indexed PC profile**: onset `max(n_I, 2(2kd + s + t) + 1)`, period the least
`p`-power above `2kd + s + t`. -/
theorem periodic_pc :
    PeriodicProfile G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI)
      (period p (2 * T.k) (T.s + G.t)) :=
  template_periodicProfile (Fact.out : p.Prime).two_le (one_le_twoK T) G.one_le_nI
    (G.thresholdPeriodic_pc p) G.zeroStable_pc

theorem periodic_ns :
    PeriodicProfile G.nsProfile (onset (2 * T.k) (T.s + G.t) G.nI)
      (period p (2 * T.k) (T.s + G.t)) :=
  template_periodicProfile (Fact.out : p.Prime).two_le (one_le_twoK T) G.one_le_nI
    (G.thresholdPeriodic_ns p) G.zeroStable_ns

/-! #### Four types, linear bounds, T2, T3, lim inf -/

/-- **Four exclusive and exhaustive types with the linear bounds, indexed PC profile**, with
`k' = 2k`, `s' = s + t`.  Obtained from the indexed PC transfer itself. -/
theorem linearBounds_pc : LinearBoundsFor p (2 * T.k) (T.s + G.t) G.nI G.pcProfile :=
  linearBoundsFor_of_periodic (Fact.out : p.Prime).two_le (one_le_twoK T) (G.periodic_pc p)

theorem linearBounds_ns : LinearBoundsFor p (2 * T.k) (T.s + G.t) G.nI G.nsProfile :=
  linearBoundsFor_of_periodic (Fact.out : p.Prime).two_le (one_le_twoK T) (G.periodic_ns p)

include p in
/-- **T2 in the extended order**: `⌊(n − 2(s+t) − 1)/(4k)⌋ < h(n)` for every `n ≥ n_I`, the value
`⊤` included.  For either indexed profile. -/
theorem T2_bound {h : ℕ → ℕ∞} (hh : h = G.pcProfile ∨ h = G.nsProfile)
    (h2 : IsT2 h (onset (2 * T.k) (T.s + G.t) G.nI)) {n : ℕ} (hn : G.nI ≤ n) :
    (((n - 2 * (T.s + G.t) - 1) / (2 * (2 * T.k)) : ℕ) : ℕ∞) < h n := by
  rcases hh with rfl | rfl
  · exact T2_floor (G.periodic_pc p) h2 hn
  · exact T2_floor (G.periodic_ns p) h2 hn

include p in
/-- **The full T3 split** for either indexed profile. -/
theorem T3_full {h : ℕ → ℕ∞} (hh : h = G.pcProfile ∨ h = G.nsProfile)
    (h3 : IsT3 h (onset (2 * T.k) (T.s + G.t) G.nI)) :
    ∃ D : ℕ, D ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI) ∧
      (∀ d ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI), d ≤ D) ∧
      ∃ U : Set ℕ, (∀ c ∈ U, c < period p (2 * T.k) (T.s + G.t) D) ∧ U.Nonempty ∧
        (∃ c, c < period p (2 * T.k) (T.s + G.t) D ∧ c ∉ U) ∧
        (∀ c ∈ U, ∃ v : ℕ, v ≤ D ∧ ∀ n, onset (2 * T.k) (T.s + G.t) G.nI D ≤ n →
            n % period p (2 * T.k) (T.s + G.t) D = c → h n = (v : ℕ∞)) ∧
        (∀ n, onset (2 * T.k) (T.s + G.t) G.nI D ≤ n →
            n % period p (2 * T.k) (T.s + G.t) D ∉ U →
            (((n - 2 * (T.s + G.t) - 1) / (2 * (2 * T.k)) : ℕ) : ℕ∞) < h n) := by
  rcases hh with rfl | rfl
  · exact T3_split (G.periodic_pc p) h3
  · exact T3_split (G.periodic_ns p) h3

include p in
/-- **The lim inf** for either indexed profile. -/
theorem liminf_classification {h : ℕ → ℕ∞} (hh : h = G.pcProfile ∨ h = G.nsProfile) :
    ((IsT1 h ∨ IsT3 h (onset (2 * T.k) (T.s + G.t) G.nI) ∨
        IsT4 h (onset (2 * T.k) (T.s + G.t) G.nI)) →
      ∃ e ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI),
        (∀ x ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI), e ≤ x) ∧ liminf h atTop = (e : ℕ∞)) ∧
    (IsT2 h (onset (2 * T.k) (T.s + G.t) G.nI) → liminf h atTop = ⊤) := by
  rcases hh with rfl | rfl
  · exact liminf_of_periodic (G.periodic_pc p)
  · exact liminf_of_periodic (G.periodic_ns p)

/-! #### Comparison and the common type -/

include p in
/-- **Uniform upper comparison for indexed targets**: `PC ≤ NS ≤ F ∘ PC` with `F` monotone and
independent of `n`, from the WHOLE-consequence inclusion `Vinf(T_n, t) ≤ NSspan(T_n, F t)`. -/
theorem upperComparison :
    ∃ F : ℕ → ℕ, Monotone F ∧ (∀ u, u ≤ F u) ∧ UpperComparison F G.pcProfile G.nsProfile := by
  obtain ⟨F, hF, hFt, hinc⟩ := uniform_inclusion p T
  refine ⟨F, hF, hFt, fun n x hx => ?_⟩
  rw [nsProfile_le_iff]
  intro b
  exact hinc n x (((G.pcProfile_le_iff n x).mp (le_of_eq hx)) b)

include p in
/-- **The NS and ordinary-PC indexed profiles have the same type.**  (Exact degrees and
recurring level sets are NOT asserted to agree.) -/
theorem types_agree :
    (IsT1 G.pcProfile ↔ IsT1 G.nsProfile) ∧
    (IsT2 G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI) ↔
      IsT2 G.nsProfile (onset (2 * T.k) (T.s + G.t) G.nI)) ∧
    (IsT3 G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI) ↔
      IsT3 G.nsProfile (onset (2 * T.k) (T.s + G.t) G.nI)) ∧
    (IsT4 G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI) ↔
      IsT4 G.nsProfile (onset (2 * T.k) (T.s + G.t) G.nI)) := by
  obtain ⟨F, hF, -, hub⟩ := G.upperComparison p
  exact types_transfer (G.periodic_pc p) (G.periodic_ns p) hF G.pcProfile_le_nsProfile hub

/-- **Common finite T4 peaks.** -/
theorem common_peaks (h4 : IsT4 G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI)) :
    ∃ F : ℕ → ℕ, Monotone F ∧ ∀ B : ℕ, ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧
      d ∈ E G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI) ∧ G.pcProfile n = (d : ℕ∞) ∧
      (d : ℕ∞) ≤ G.nsProfile n ∧ G.nsProfile n ≤ (F d : ℕ∞) ∧
      n ≤ (p + 2) * (2 * T.k * d + (T.s + G.t)) ∧
      (n : ℚ) / ((p + 2) * (2 * T.k : ℕ)) - ((T.s + G.t : ℕ) : ℚ) / (2 * T.k : ℕ) ≤ d := by
  obtain ⟨F, hF, -, hub⟩ := G.upperComparison p
  refine ⟨F, hF, fun B => ?_⟩
  obtain ⟨n, d, hBn, hBd, hdE, hval, hsize, hrat⟩ := (G.linearBounds_pc p).T4_bound h4 B
  exact ⟨n, d, hBn, hBd, hdE, hval, hval ▸ G.pcProfile_le_nsProfile n, hub n d hval, hsize, hrat⟩

end ITarget

/-! ### The combined endpoint -/

section Endpoint

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] {T : Template R}

/-- **Indexed-target endpoint.**  For every uniform template over a field of characteristic `p`
and every bounded-support indexed target `G` (all targets indexed by `B_n`; for one fixed orbit
apply it to `G.orbit o`), with `k' = 2k`, `s' = s + t`, `n_I = max(n₀, 1, k·DG + t)`:
1. two-way transfer `n ↦ n + p^a` for every degree `d`, with `p^a > 2kd + s + t` and
   `n ≥ max(n_I, 2(2kd+s+t) − 1)`, for ordinary PC derivations and total-product NS identities;
2. for both profiles: (P), exactly one of T1–T4, the linear T2 bound, the T3 hard-residue bound,
   arbitrarily large finite T4 peaks (`LinearBoundsFor`);
3. the degree floor `maxDeg ≤ h(n)` beyond `max 1 (k·DG + t)`;
4. `PC ≤ NS ≤ F ∘ PC` uniformly, and the common type;
5. the lim inf: least recurring value in T1, T3, T4, `⊤` in T2;
6. T2 in the extended order and the full T3 split, for both profiles. -/
theorem indexed_target_endpoint (G : ITarget T) :
    (∀ d a n : ℕ, T.n0 ≤ n → G.aux.n0 ≤ n → 2 * G.supp d - 1 ≤ n → G.supp d < p ^ a →
      ((∀ b, Derives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a) b)) ↔
          ∀ b, Derives (T.inst n) d (G.poly n b)) ∧
      ((∀ b, NSDerives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a) b)) ↔
          ∀ b, NSDerives (T.inst n) d (G.poly n b))) ∧
    LinearBoundsFor p (2 * T.k) (T.s + G.t) G.nI G.pcProfile ∧
    LinearBoundsFor p (2 * T.k) (T.s + G.t) G.nI G.nsProfile ∧
    (∀ n, G.aux.n0 ≤ n → (G.maxDeg : ℕ∞) ≤ G.pcProfile n ∧ (G.maxDeg : ℕ∞) ≤ G.nsProfile n) ∧
    (∀ n, G.pcProfile n ≤ G.nsProfile n) ∧
    (∃ F : ℕ → ℕ, Monotone F ∧ UpperComparison F G.pcProfile G.nsProfile) ∧
    ((IsT1 G.pcProfile ↔ IsT1 G.nsProfile) ∧
      (IsT2 G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI) ↔
        IsT2 G.nsProfile (onset (2 * T.k) (T.s + G.t) G.nI)) ∧
      (IsT3 G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI) ↔
        IsT3 G.nsProfile (onset (2 * T.k) (T.s + G.t) G.nI)) ∧
      (IsT4 G.pcProfile (onset (2 * T.k) (T.s + G.t) G.nI) ↔
        IsT4 G.nsProfile (onset (2 * T.k) (T.s + G.t) G.nI))) ∧
    (∀ h ∈ ({G.pcProfile, G.nsProfile} : Set (ℕ → ℕ∞)),
      ((IsT1 h ∨ IsT3 h (onset (2 * T.k) (T.s + G.t) G.nI) ∨
          IsT4 h (onset (2 * T.k) (T.s + G.t) G.nI)) →
        ∃ e ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI),
          (∀ x ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI), e ≤ x) ∧ liminf h atTop = (e : ℕ∞)) ∧
      (IsT2 h (onset (2 * T.k) (T.s + G.t) G.nI) → liminf h atTop = ⊤)) ∧
    (∀ h ∈ ({G.pcProfile, G.nsProfile} : Set (ℕ → ℕ∞)),
      IsT2 h (onset (2 * T.k) (T.s + G.t) G.nI) → ∀ n, G.nI ≤ n →
        (((n - 2 * (T.s + G.t) - 1) / (2 * (2 * T.k)) : ℕ) : ℕ∞) < h n) ∧
    (∀ h ∈ ({G.pcProfile, G.nsProfile} : Set (ℕ → ℕ∞)),
      IsT3 h (onset (2 * T.k) (T.s + G.t) G.nI) →
      ∃ D : ℕ, D ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI) ∧
        (∀ d ∈ E h (onset (2 * T.k) (T.s + G.t) G.nI), d ≤ D) ∧
        ∃ U : Set ℕ, (∀ c ∈ U, c < period p (2 * T.k) (T.s + G.t) D) ∧ U.Nonempty ∧
          (∃ c, c < period p (2 * T.k) (T.s + G.t) D ∧ c ∉ U) ∧
          (∀ c ∈ U, ∃ v : ℕ, v ≤ D ∧ ∀ n, onset (2 * T.k) (T.s + G.t) G.nI D ≤ n →
              n % period p (2 * T.k) (T.s + G.t) D = c → h n = (v : ℕ∞)) ∧
          (∀ n, onset (2 * T.k) (T.s + G.t) G.nI D ≤ n →
              n % period p (2 * T.k) (T.s + G.t) D ∉ U →
              (((n - 2 * (T.s + G.t) - 1) / (2 * (2 * T.k)) : ℕ) : ℕ∞) < h n)) := by
  have hmem : ∀ h ∈ ({G.pcProfile, G.nsProfile} : Set (ℕ → ℕ∞)),
      h = G.pcProfile ∨ h = G.nsProfile := by
    intro h hh
    rcases hh with rfl | hh
    · exact Or.inl rfl
    · rw [Set.mem_singleton_iff] at hh; exact Or.inr hh
  refine ⟨fun d a n hn0 hna hW hq => indexed_transfer_derivations p G hn0 hna hW hq,
    G.linearBounds_pc p, G.linearBounds_ns p,
    fun n hn => ⟨G.maxDeg_le_pcProfile hn, G.maxDeg_le_nsProfile hn⟩,
    G.pcProfile_le_nsProfile, ?_, G.types_agree p,
    fun h hh => G.liminf_classification p (hmem h hh),
    fun h hh h2 n hn => G.T2_bound p (hmem h hh) h2 hn,
    fun h hh h3 => G.T3_full p (hmem h hh) h3⟩
  obtain ⟨F, hF, -, hub⟩ := G.upperComparison p
  exact ⟨F, hF, hub⟩

/-- **One fixed global orbit.**  The orbit profile is the least degree of any representative at
every rank `n ≥ t`, and it satisfies the whole endpoint (applied to `G.orbit o`). -/
theorem orbit_endpoint (G : ITarget T) (o : G.B.Obj) :
    (∀ n, G.t ≤ n → ∃ b0 : G.B.Rk n, G.InOrbit o b0) ∧
    (∀ n (b0 : G.B.Rk n), G.InOrbit o b0 →
      (G.orbit o).pcProfile n = tpcDegree (T.inst n) (G.poly n b0) ∧
      (G.orbit o).nsProfile n = tnsDegree (T.inst n) (G.poly n b0)) ∧
    LinearBoundsFor p (2 * T.k) (T.s + G.t) (G.orbit o).nI (G.orbit o).pcProfile ∧
    LinearBoundsFor p (2 * T.k) (T.s + G.t) (G.orbit o).nI (G.orbit o).nsProfile ∧
    ((IsT1 (G.orbit o).pcProfile ↔ IsT1 (G.orbit o).nsProfile) ∧
      (IsT2 (G.orbit o).pcProfile (onset (2 * T.k) (T.s + G.t) (G.orbit o).nI) ↔
        IsT2 (G.orbit o).nsProfile (onset (2 * T.k) (T.s + G.t) (G.orbit o).nI)) ∧
      (IsT3 (G.orbit o).pcProfile (onset (2 * T.k) (T.s + G.t) (G.orbit o).nI) ↔
        IsT3 (G.orbit o).nsProfile (onset (2 * T.k) (T.s + G.t) (G.orbit o).nI)) ∧
      (IsT4 (G.orbit o).pcProfile (onset (2 * T.k) (T.s + G.t) (G.orbit o).nI) ↔
        IsT4 (G.orbit o).nsProfile (onset (2 * T.k) (T.s + G.t) (G.orbit o).nI))) :=
  ⟨fun _ hn => G.exists_rep o hn,
    fun _ _ hb0 => ⟨G.orbit_pcProfile_eq_rep o hb0, G.orbit_nsProfile_eq_rep o hb0⟩,
    (G.orbit o).linearBounds_pc p, (G.orbit o).linearBounds_ns p, (G.orbit o).types_agree p⟩

end Endpoint

end UniformConsequence.Indexed
