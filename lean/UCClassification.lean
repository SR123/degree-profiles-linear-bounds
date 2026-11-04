/-
Uniform consequences, Claude return 001 (5 October 2026).  Part 3: the target degree profiles,
their periodicity with linear onset, the four types with the linear bounds, the finite lim inf,
the uniform NS–PC inclusion for EVERY bounded-degree consequence, and the common type.

For a template `T` over a field `R` of prime characteristic `p` and a fully invariant target `G`:

* `pcProfile n = tpcDegree (T.inst n) (G.poly n)`: least degree of an ordinary PC derivation from
  the actual instance ending in the actual polynomial `G_n` (`⊤` if none);
* `nsProfile n = tnsDegree (T.inst n) (G.poly n)`: least total-product degree of an NS identity
  `G_n = ∑ a_f f` (`⊤` if none).

The onset is Stage 5's `onset k s n⋆` with `n⋆ = max(n₀, nG)`; the period is the least `p`-power
above `kd + s`.  Everything is unconditional: the only exactness input is
`LinearFinal.exactness_linear`, and the chain bound is `ClaudeComparison.chainBound`.
-/
import UCTransfer
import CompFinal
import PDigits

set_option autoImplicit false

open MvPolynomial Filter

namespace UniformConsequence

open DegreeProfilesReview DegreeProfilesReview.Uniform DegreeProfilesReview.Uniform.BasisSystem
open DegreeProfilesReview.PC DegreeProfilesReview.NS DegreeProfilesReview.Profiles
open DegreeProfilesReview.SymRep

/-! ### The uniform NS–PC inclusion for the whole consequence space -/

section Inclusion

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] (T : Template R)

include p in
/-- **Uniform inclusion `C_t(n) ⊆ I_{F(t)}(n)`.**  There is a monotone `F`, independent of the
universe size, such that for every `n` and `t` the whole degree-`t` PC closure of the instance
(every polynomial with a degree-`t` ordinary PC derivation) lies in the image of the degree-`F t`
NS certificate map.  No target symmetry is used. -/
theorem uniform_inclusion :
    ∃ F : ℕ → ℕ, Monotone F ∧ (∀ t, t ≤ F t) ∧
      ∀ n t, Vinf (T.inst n) t ≤ NSspan (T.inst n) (F t) := by
  choose L hL using ClaudeComparison.chainBound p T
  refine ⟨fun x => x + ∑ s ∈ Finset.range (x + 1), L s, ?_, fun x => Nat.le_add_right _ _, ?_⟩
  · intro x y hxy
    have : ∑ s ∈ Finset.range (x + 1), L s ≤ ∑ s ∈ Finset.range (y + 1), L s :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    simp only
    omega
  · intro n t
    have hchain := hL t n (fun i : Fin (L t + 2) =>
        NSspan (T.inst n) (t + i) ⊓ restrictTotalDegree (T.Var.Rk n) R t)
      (fun _ => inf_le_right) (by
        intro i g f hf
        obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hf
        refine Submodule.mem_inf.mpr ⟨ClaudeC017.rename_mem_NSspan T g h1, ?_⟩
        rw [mem_restrictTotalDegree] at h2 ⊢
        exact le_trans (totalDegree_rename_le _ f) h2)
    have hex : ∃ u, u ≤ L t ∧
        NSspan (T.inst n) (t + u + 1) ⊓ restrictTotalDegree (T.Var.Rk n) R t =
          NSspan (T.inst n) (t + u) ⊓ restrictTotalDegree (T.Var.Rk n) R t := by
      by_contra hno
      push_neg at hno
      apply hchain
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      simp only [Fin.coe_castSucc, Fin.val_succ]
      refine lt_of_le_of_ne (inf_le_inf_right _ (ClaudeC017.NSspan_mono (by omega))) ?_
      intro heq
      exact hno i (by omega) (by rw [← add_assoc] at heq; exact heq.symm)
    obtain ⟨u, hu, heq⟩ := hex
    intro f hf
    have h2 := ClaudeC017.Vinf_le_of_stable (T.inst n) (by omega : t ≤ t + u) heq hf
    have hLt : L t ≤ ∑ s ∈ Finset.range (t + 1), L s :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    exact ClaudeC017.NSspan_mono (by simp only; omega) (Submodule.mem_inf.mp h2).1

include p in
/-- The inclusion stated for the actual proof systems: every polynomial with a degree-`t`
ordinary PC derivation from `T.inst n` has a total-product degree-`F t` NS identity. -/
theorem uniform_derivation_comparison :
    ∃ F : ℕ → ℕ, Monotone F ∧ (∀ t, t ≤ F t) ∧
      ∀ n t (g : MvPolynomial (T.Var.Rk n) R), Derives (T.inst n) t g →
        NSDerives (T.inst n) (F t) g := by
  obtain ⟨F, hF, hFt, hinc⟩ := uniform_inclusion p T
  refine ⟨F, hF, hFt, fun n t g hg => ?_⟩
  rw [nsDerives_iff_mem_NSspan]
  exact hinc n t (derives_iff_mem_Vinf.mp hg)

end Inclusion

namespace Target

variable {R : Type} [Field R] {T : Template R} (G : Target T)

/-! ### The target profiles -/

/-- **The ordinary-PC target profile.** -/
noncomputable def pcProfile (n : ℕ) : ℕ∞ := tpcDegree (T.inst n) (G.poly n)

/-- **The total-product NS target profile.** -/
noncomputable def nsProfile (n : ℕ) : ℕ∞ := tnsDegree (T.inst n) (G.poly n)

/-- The fixed starting rank `n⋆ = max(n₀, nG)`. -/
noncomputable def nstar : ℕ := max T.n0 G.nG

theorem one_le_nG : 1 ≤ G.nG := le_max_left _ _

theorem one_le_nstar : 1 ≤ G.nstar := le_trans G.one_le_nG (le_max_right _ _)

theorem pcProfile_le_iff (n d : ℕ) : G.pcProfile n ≤ (d : ℕ∞) ↔ G.poly n ∈ Vinf (T.inst n) d :=
  tpcDegree_le_iff_mem _ _ _

theorem nsProfile_le_iff (n d : ℕ) :
    G.nsProfile n ≤ (d : ℕ∞) ↔ G.poly n ∈ NSspan (T.inst n) d :=
  tnsDegree_le_iff_mem _ _ _

theorem pcProfile_le_nsProfile (n : ℕ) : G.pcProfile n ≤ G.nsProfile n :=
  tpcDegree_le_tnsDegree _ _

/-- The target degree is a fixed floor: beyond `nG` neither profile is below `deg G`. -/
theorem deg_le_pcProfile {n : ℕ} (hn : G.nG ≤ n) : (G.deg : ℕ∞) ≤ G.pcProfile n := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hx, -⟩ : ∃ x : ℕ, G.pcProfile n = x ∧ True := by
    induction h : G.pcProfile n using ENat.recTopCoe with
    | top => rw [h] at hlt; exact absurd hlt (not_lt.mpr le_top)
    | coe x => exact ⟨x, rfl, trivial⟩
  rw [hx, Nat.cast_lt] at hlt
  have hmem := (G.pcProfile_le_iff n x).mp (le_of_eq hx)
  exact (G.not_mem_of_lt hn hlt (T.inst n)).1 hmem

theorem deg_le_nsProfile {n : ℕ} (hn : G.nG ≤ n) : (G.deg : ℕ∞) ≤ G.nsProfile n :=
  le_trans (G.deg_le_pcProfile hn) (G.pcProfile_le_nsProfile n)

/-- The zero target has both profiles identically zero. -/
theorem profiles_of_γ_zero (h0 : ∀ m, G.γ m = 0) (n : ℕ) :
    G.pcProfile n = 0 ∧ G.nsProfile n = 0 := by
  have hpoly : G.poly n = 0 := by
    apply MvPolynomial.ext
    intro m
    rw [coeff_poly, h0, MvPolynomial.coeff_zero]
  unfold pcProfile nsProfile
  rw [hpoly]
  exact ⟨tpcDegree_zero _, tnsDegree_zero _⟩

/-! ### Threshold periodicity with linear onset -/

variable (p : ℕ) [Fact p.Prime] [CharP R p]

/-- **One deletion step for the target profiles** (any `d`, `q = p^a > kd+s`,
`n ≥ max(n₀, nG, 2(kd+s) - 1)`). -/
theorem profile_step {d a n : ℕ} (hn : G.nstar ≤ n) (hW : 2 * (T.k * d + T.s) - 1 ≤ n)
    (hrq : T.k * d + T.s < p ^ a) :
    (G.pcProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ G.pcProfile n ≤ (d : ℕ∞)) ∧
    (G.nsProfile (n + p ^ a) ≤ (d : ℕ∞) ↔ G.nsProfile n ≤ (d : ℕ∞)) := by
  rw [pcProfile_le_iff, pcProfile_le_iff, nsProfile_le_iff, nsProfile_le_iff]
  exact target_transfer p G (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)
    hW hrq

theorem thresholdPeriodic_pc : ThresholdPeriodic p T.k T.s G.nstar G.pcProfile := by
  intro t _ a ha n m hn hm h2n h2m hc
  refine congr_of_step (Pr := fun x => G.pcProfile x ≤ (t : ℕ∞)) (q := p ^ a)
    (B := max G.nstar (2 * (T.k * t + T.s) + 1)) ?_ (max_le hn h2n) (max_le hm h2m) hc
  intro x hx
  exact (G.profile_step p (le_trans (le_max_left _ _) hx)
    (by have := le_max_right G.nstar (2 * (T.k * t + T.s) + 1); omega) ha).1

theorem thresholdPeriodic_ns : ThresholdPeriodic p T.k T.s G.nstar G.nsProfile := by
  intro t _ a ha n m hn hm h2n h2m hc
  refine congr_of_step (Pr := fun x => G.nsProfile x ≤ (t : ℕ∞)) (q := p ^ a)
    (B := max G.nstar (2 * (T.k * t + T.s) + 1)) ?_ (max_le hn h2n) (max_le hm h2m) hc
  intro x hx
  exact (G.profile_step p (le_trans (le_max_left _ _) hx)
    (by have := le_max_right G.nstar (2 * (T.k * t + T.s) + 1); omega) ha).2

omit [Fact p.Prime] [CharP R p] in
theorem zeroStable_pc : ZeroStable G.nstar G.pcProfile := by
  intro n m hn hm
  rw [pcProfile_le_iff, pcProfile_le_iff,
    G.pc_zero_iff (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn),
    G.pc_zero_iff (le_trans (le_max_left _ _) hm) (le_trans (le_max_right _ _) hm)]

omit [Fact p.Prime] [CharP R p] in
theorem zeroStable_ns : ZeroStable G.nstar G.nsProfile := by
  intro n m hn hm
  rw [nsProfile_le_iff, nsProfile_le_iff,
    G.ns_zero_iff (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn),
    G.ns_zero_iff (le_trans (le_max_left _ _) hm) (le_trans (le_max_right _ _) hm)]

/-- **(P) for the PC target profile**, onset `max(n⋆, 2(kd+s)+1)`, period the least `p`-power
above `kd + s`. -/
theorem periodic_pc :
    PeriodicProfile G.pcProfile (onset T.k T.s G.nstar) (period p T.k T.s) :=
  template_periodicProfile (Fact.out : p.Prime).two_le T.hk G.one_le_nstar
    (G.thresholdPeriodic_pc p) G.zeroStable_pc

theorem periodic_ns :
    PeriodicProfile G.nsProfile (onset T.k T.s G.nstar) (period p T.k T.s) :=
  template_periodicProfile (Fact.out : p.Prime).two_le T.hk G.one_le_nstar
    (G.thresholdPeriodic_ns p) G.zeroStable_ns

/-! ### The four types, the linear bounds and the lim inf -/

/-- **Four exclusive and exhaustive types with the linear bounds, PC target profile.**
`LinearBoundsFor` packages: (P); exactly one of T1–T4; in T2, `h(n) > ⌊(n-2s-1)/(2k)⌋` for every
`n ≥ n⋆` (the value `⊤` is allowed); in T3, the same bound on the hard residue classes modulo
the period beyond the onset; in T4, arbitrarily large FINITE peaks `h(n) = d`, `d` recurring,
with `n ≤ (p+2)(kd+s)`. -/
theorem linearBounds_pc : LinearBoundsFor p T.k T.s G.nstar G.pcProfile :=
  linearBoundsFor_of_periodic (Fact.out : p.Prime).two_le T.hk (G.periodic_pc p)

theorem linearBounds_ns : LinearBoundsFor p T.k T.s G.nstar G.nsProfile :=
  linearBoundsFor_of_periodic (Fact.out : p.Prime).two_le T.hk (G.periodic_ns p)

include p in
/-- **The lim inf.**  If some finite value recurs (T1, T3, T4) the lim inf is the least recurring
value, a finite number; in T2 it is `⊤`.  For either target profile. -/
theorem liminf_classification {h : ℕ → ℕ∞} (hh : h = G.pcProfile ∨ h = G.nsProfile) :
    ((IsT1 h ∨ IsT3 h (onset T.k T.s G.nstar) ∨ IsT4 h (onset T.k T.s G.nstar)) →
      ∃ e ∈ E h (onset T.k T.s G.nstar), (∀ x ∈ E h (onset T.k T.s G.nstar), e ≤ x) ∧
        liminf h atTop = (e : ℕ∞)) ∧
    (IsT2 h (onset T.k T.s G.nstar) → liminf h atTop = ⊤) := by
  have P : PeriodicProfile h (onset T.k T.s G.nstar) (period p T.k T.s) := by
    rcases hh with rfl | rfl
    · exact G.periodic_pc p
    · exact G.periodic_ns p
  refine ⟨fun hT => ClaudeCP.liminf_eq_min P ?_, ClaudeCP.liminf_eq_top P⟩
  rcases hT with h1 | h3 | h4
  · exact (P.bounded_E h1).2
  · exact h3.2.1
  · exact h4.nonempty

/-! ### Comparison and the common type -/

include p in
/-- **Uniform upper comparison for the target**: `PC ≤ NS ≤ F ∘ PC`, with `F` monotone and
independent of `n` (and `F ∞ = ∞`). -/
theorem upperComparison :
    ∃ F : ℕ → ℕ, Monotone F ∧ (∀ t, t ≤ F t) ∧ UpperComparison F G.pcProfile G.nsProfile := by
  obtain ⟨F, hF, hFt, hinc⟩ := uniform_inclusion p T
  refine ⟨F, hF, hFt, fun n x hx => ?_⟩
  rw [nsProfile_le_iff]
  exact hinc n x ((G.pcProfile_le_iff n x).mp (le_of_eq hx))

include p in
/-- **The NS and ordinary-PC target profiles have the same type.**  (Exact degrees and recurring
level sets are NOT asserted to agree.) -/
theorem types_agree :
    (IsT1 G.pcProfile ↔ IsT1 G.nsProfile) ∧
    (IsT2 G.pcProfile (onset T.k T.s G.nstar) ↔ IsT2 G.nsProfile (onset T.k T.s G.nstar)) ∧
    (IsT3 G.pcProfile (onset T.k T.s G.nstar) ↔ IsT3 G.nsProfile (onset T.k T.s G.nstar)) ∧
    (IsT4 G.pcProfile (onset T.k T.s G.nstar) ↔ IsT4 G.nsProfile (onset T.k T.s G.nstar)) := by
  obtain ⟨F, hF, -, hub⟩ := G.upperComparison p
  exact types_transfer (G.periodic_pc p) (G.periodic_ns p) hF G.pcProfile_le_nsProfile hub

/-- **Common finite T4 peaks.**  In type T4 there is a monotone `F` such that beyond every bound
some size `n` carries a finite recurring PC value `d` with the linear peak bounds, and at the same
size the NS degree is finite and lies between `d` and `F d`. -/
theorem common_peaks (h4 : IsT4 G.pcProfile (onset T.k T.s G.nstar)) :
    ∃ F : ℕ → ℕ, Monotone F ∧ ∀ B : ℕ, ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧
      d ∈ E G.pcProfile (onset T.k T.s G.nstar) ∧ G.pcProfile n = (d : ℕ∞) ∧
      (d : ℕ∞) ≤ G.nsProfile n ∧ G.nsProfile n ≤ (F d : ℕ∞) ∧
      n ≤ (p + 2) * (T.k * d + T.s) ∧ (n : ℚ) / ((p + 2) * T.k) - T.s / T.k ≤ d := by
  obtain ⟨F, hF, -, hub⟩ := G.upperComparison p
  refine ⟨F, hF, fun B => ?_⟩
  obtain ⟨n, d, hBn, hBd, hdE, hval, hsize, hrat⟩ := (G.linearBounds_pc p).T4_bound h4 B
  exact ⟨n, d, hBn, hBd, hdE, hval, hval ▸ G.pcProfile_le_nsProfile n, hub n d hval, hsize, hrat⟩

end Target

/-! ### The combined endpoint -/

section Endpoint

variable (p : ℕ) [Fact p.Prime] {R : Type} [Field R] [CharP R p] {T : Template R}

/-- **Invariant-target endpoint.**  For every uniform template over a field of prime
characteristic `p` and every fully invariant uniform target `G`:
1. two-way target transfer `n ↦ n + p^a` for every degree `d`, with `p^a > kd + s` and
   `n ≥ max(n₀, nG, 2(kd+s) - 1)`, for ordinary PC derivations and total-product NS identities;
2. for both target profiles: (P) with onset `max(n⋆, 2(kd+s)+1)`, exactly one of T1–T4, the
   linear T2 bound, the T3 hard-residue bound and arbitrarily large finite T4 peaks;
3. the target degree floor;
4. `PC ≤ NS ≤ F ∘ PC` uniformly, and the common type;
5. the lim inf: the least recurring value (finite) in T1, T3 and T4, and `⊤` in T2. -/
theorem invariant_target_endpoint (G : Target T) :
    (∀ d a n : ℕ, T.n0 ≤ n → G.nG ≤ n → 2 * (T.k * d + T.s) - 1 ≤ n →
      T.k * d + T.s < p ^ a →
      (Derives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a)) ↔ Derives (T.inst n) d (G.poly n)) ∧
      (NSDerives (T.inst (n + p ^ a)) d (G.poly (n + p ^ a)) ↔
        NSDerives (T.inst n) d (G.poly n))) ∧
    LinearBoundsFor p T.k T.s G.nstar G.pcProfile ∧
    LinearBoundsFor p T.k T.s G.nstar G.nsProfile ∧
    (∀ n, G.nG ≤ n → (G.deg : ℕ∞) ≤ G.pcProfile n ∧ (G.deg : ℕ∞) ≤ G.nsProfile n) ∧
    (∀ n, G.pcProfile n ≤ G.nsProfile n) ∧
    (∃ F : ℕ → ℕ, Monotone F ∧ UpperComparison F G.pcProfile G.nsProfile) ∧
    ((IsT1 G.pcProfile ↔ IsT1 G.nsProfile) ∧
      (IsT2 G.pcProfile (onset T.k T.s G.nstar) ↔ IsT2 G.nsProfile (onset T.k T.s G.nstar)) ∧
      (IsT3 G.pcProfile (onset T.k T.s G.nstar) ↔ IsT3 G.nsProfile (onset T.k T.s G.nstar)) ∧
      (IsT4 G.pcProfile (onset T.k T.s G.nstar) ↔ IsT4 G.nsProfile (onset T.k T.s G.nstar))) ∧
    (∀ h ∈ ({G.pcProfile, G.nsProfile} : Set (ℕ → ℕ∞)),
      ((IsT1 h ∨ IsT3 h (onset T.k T.s G.nstar) ∨ IsT4 h (onset T.k T.s G.nstar)) →
        ∃ e ∈ E h (onset T.k T.s G.nstar), (∀ x ∈ E h (onset T.k T.s G.nstar), e ≤ x) ∧
          liminf h atTop = (e : ℕ∞)) ∧
      (IsT2 h (onset T.k T.s G.nstar) → liminf h atTop = ⊤)) := by
  refine ⟨fun d a n hn0 hnG hW hrq => target_transfer_derivations p G hn0 hnG hW hrq,
    G.linearBounds_pc p, G.linearBounds_ns p,
    fun n hn => ⟨G.deg_le_pcProfile hn, G.deg_le_nsProfile hn⟩,
    G.pcProfile_le_nsProfile, ?_, G.types_agree p, ?_⟩
  · obtain ⟨F, hF, -, hub⟩ := G.upperComparison p
    exact ⟨F, hF, hub⟩
  · intro h hh
    apply G.liminf_classification p
    rcases hh with rfl | hh
    · exact Or.inl rfl
    · rw [Set.mem_singleton_iff] at hh; exact Or.inr hh

end Endpoint

end UniformConsequence
