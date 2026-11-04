/-
Stage 2, step 7: manuscript `lem:types` (transferring the four types), with its FULL comparison
hypothesis

      g n ≤ h n ≤ F (g n),     F : ℕ → ℕ nondecreasing, F ∞ = ∞,

for two profiles satisfying hypothesis (P), possibly with different onsets and periods.

* `types_transfer`            — the lemma.
* `lower_comparison_insufficient` — `g ≤ h` ALONE does not give agreement of types
                                 (`g ≡ 0` is of type (i), `h ≡ ∞` of type (ii)).
* `Template.types_agree`      — application to the actual PC and NS profiles of a uniform
                                 template.  The size-independent upper comparison
                                 `NS ≤ F(PC)` is an explicit hypothesis; it is NOT proved here.
-/
import DegreeProfilesReview.TemplatePeriodicity

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace DegreeProfilesReview.Profiles

variable {g h : ℕ → ℕ∞} {Ng Qg Nh Qh : ℕ → ℕ}

/-- The upper comparison `h ≤ F ∘ g` with `F ∞ = ∞`: wherever `g` is finite, `h ≤ F (g n)`. -/
def UpperComparison (F : ℕ → ℕ) (g h : ℕ → ℕ∞) : Prop :=
  ∀ n (x : ℕ), g n = (x : ℕ∞) → h n ≤ ((F x : ℕ) : ℕ∞)

/-- Beyond any bound there is a size in a given residue class. -/
theorem exists_large_in_class (c M : ℕ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ m, M ≤ m ∧ c ≤ m ∧ m % Q = c % Q :=
  ⟨c + M * Q, le_trans (Nat.le_mul_of_pos_right M hQ) (Nat.le_add_left _ _),
    Nat.le_add_right _ _, Nat.add_mul_mod_self_right c M Q⟩

/-- A recurring level of `g` produces a recurring level of `h` between `d` and `F d`. -/
theorem recurring_up (Pg : PeriodicProfile g Ng Qg) (Ph : PeriodicProfile h Nh Qh)
    {F : ℕ → ℕ} (hle : ∀ n, g n ≤ h n) (hub : UpperComparison F g h) {d : ℕ}
    (hd : d ∈ E g Ng) : ∃ v, v ∈ E h Nh ∧ d ≤ v ∧ v ≤ F d := by
  obtain ⟨c, hc, _, hrec⟩ := Pg.recurs hd
  obtain ⟨m, hmM, hmc, hmod⟩ := exists_large_in_class c (Nh (F d)) (Pg.Q_pos d)
  have hgm : g m = (d : ℕ∞) := hrec m (le_trans hc hmc) hmod
  have hhm : h m ≤ ((F d : ℕ) : ℕ∞) := hub m d hgm
  obtain ⟨v, hv, hvF⟩ := enat_exists_of_le_coe hhm
  refine ⟨v, mem_E_of_le Ph hmM hv hvF, ?_, hvF⟩
  have := hle m
  rw [hgm, hv] at this
  exact_mod_cast this

/-- A recurring level `d` of `h` produces a recurring level `x ≤ d` of `g` with `d ≤ F x`. -/
theorem recurring_down (Pg : PeriodicProfile g Ng Qg) (Ph : PeriodicProfile h Nh Qh)
    {F : ℕ → ℕ} (hle : ∀ n, g n ≤ h n) (hub : UpperComparison F g h) {d : ℕ}
    (hd : d ∈ E h Nh) : ∃ x, x ∈ E g Ng ∧ x ≤ d ∧ d ≤ F x := by
  obtain ⟨c, hc, _, hrec⟩ := Ph.recurs hd
  obtain ⟨m, hmM, hmc, hmod⟩ := exists_large_in_class c (Ng d) (Ph.Q_pos d)
  have hhm : h m = (d : ℕ∞) := hrec m (le_trans hc hmc) hmod
  have hgm : g m ≤ (d : ℕ∞) := hhm ▸ hle m
  obtain ⟨x, hx, hxd⟩ := enat_exists_of_le_coe hgm
  refine ⟨x, mem_E_of_le Pg hmM hx hxd, hxd, ?_⟩
  have := hub m x hx
  rw [hhm] at this
  exact_mod_cast this

/-- **Manuscript `lem:types`.**  Under (P) for both profiles and the two-sided comparison
`g ≤ h ≤ F ∘ g` with `F` nondecreasing, each of the four types holds for `g` iff it holds
for `h`. -/
theorem types_transfer (Pg : PeriodicProfile g Ng Qg) (Ph : PeriodicProfile h Nh Qh)
    {F : ℕ → ℕ} (hF : Monotone F) (hle : ∀ n, g n ≤ h n) (hub : UpperComparison F g h) :
    (IsT1 g ↔ IsT1 h) ∧ (IsT2 g Ng ↔ IsT2 h Nh) ∧ (IsT3 g Ng ↔ IsT3 h Nh) ∧
      (IsT4 g Ng ↔ IsT4 h Nh) := by
  -- eventual boundedness
  have hB : EventuallyBounded g ↔ EventuallyBounded h := by
    constructor
    · rintro ⟨B, M, hBM⟩
      refine ⟨F B, M, fun n hn => ?_⟩
      obtain ⟨x, hx, hxB⟩ := enat_exists_of_le_coe (hBM n hn)
      exact le_trans (hub n x hx) (by exact_mod_cast hF hxB)
    · rintro ⟨B, M, hBM⟩
      exact ⟨B, M, fun n hn => le_trans (hle n) (hBM n hn)⟩
  -- emptiness of the recurring set
  have hE : E g Ng = ∅ ↔ E h Nh = ∅ := by
    constructor
    · intro h0
      by_contra hne
      obtain ⟨d, hd⟩ := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨x, hx, _, _⟩ := recurring_down Pg Ph hle hub hd
      rw [h0] at hx
      exact hx
    · intro h0
      by_contra hne
      obtain ⟨d, hd⟩ := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨v, hv, _, _⟩ := recurring_up Pg Ph hle hub hd
      rw [h0] at hv
      exact hv
  -- infinitude of the recurring set
  have hI : (E g Ng).Infinite ↔ (E h Nh).Infinite := by
    constructor
    · intro hinf
      apply Set.infinite_of_forall_exists_gt
      intro B
      obtain ⟨d, hd, hBd⟩ := hinf.exists_gt B
      obtain ⟨v, hv, hdv, _⟩ := recurring_up Pg Ph hle hub hd
      exact ⟨v, hv, lt_of_lt_of_le hBd hdv⟩
    · intro hinf
      apply Set.infinite_of_forall_exists_gt
      intro B
      obtain ⟨d, hd, hBd⟩ := hinf.exists_gt (F B)
      obtain ⟨x, hx, _, hdF⟩ := recurring_down Pg Ph hle hub hd
      refine ⟨x, hx, ?_⟩
      by_contra hxB
      rw [not_lt] at hxB
      have := hF hxB
      omega
  refine ⟨hB, hE, ?_, hI⟩
  unfold IsT3
  rw [← Set.not_infinite, ← Set.not_infinite, hI, Set.nonempty_iff_ne_empty,
    Set.nonempty_iff_ne_empty, Ne, Ne, hE, hB]

/-- `g ≤ h` alone is NOT enough: `g ≡ 0` and `h ≡ ∞` both satisfy (P) and `g ≤ h`, but `g` is
of type (i) while `h` is of type (ii) and not of type (i). -/
theorem lower_comparison_insufficient :
    ∃ g h : ℕ → ℕ∞, (∀ n, g n ≤ h n) ∧
      PeriodicProfile g (fun d => d + 1) (fun _ => 1) ∧
      PeriodicProfile h (fun d => d + 1) (fun _ => 1) ∧
      IsT1 g ∧ ¬ IsT1 h ∧ IsT2 h (fun d => d + 1) := by
  refine ⟨fun _ => 0, fun _ => ⊤, fun _ => bot_le, ?_, ?_, ⟨0, 0, fun _ _ => le_refl _⟩, ?_,
    regression_top _⟩
  · exact ⟨fun a b hab => Nat.succ_le_succ hab, fun _ => le_refl _, fun _ => Nat.one_pos,
      fun _ _ _ _ _ _ _ _ => Iff.rfl⟩
  · exact ⟨fun a b hab => Nat.succ_le_succ hab, fun _ => le_refl _, fun _ => Nat.one_pos,
      fun _ _ _ _ _ _ _ _ => Iff.rfl⟩
  · rintro ⟨B, M, hBM⟩
    have := hBM M (le_refl M)
    simp at this

end DegreeProfilesReview.Profiles

namespace DegreeProfilesReview.Uniform

open DegreeProfilesReview.Profiles

/-- **Agreement of types for the actual profiles of a uniform template.**  Inputs: M1–M5
(`DeletionHypothesis`) AND the size-independent upper comparison `NS ≤ F(PC)` (external; for
first-order translations the manuscript takes it from Krajíček's Theorem 5.5). -/
theorem Template.types_agree {R : Type} [Field R] (T : Template R) {p : ℕ} (hp : 2 ≤ p)
    (K : Type) [Field K] [Algebra R K]
    (H : DeletionHypothesis.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0)
    {F : ℕ → ℕ} (hF : Monotone F)
    (hub : UpperComparison F (fun n => PC.pcDegree (T.inst n))
      (fun n => NS.nsDegree (T.inst n))) :
    (IsT1 (fun n => PC.pcDegree (T.inst n)) ↔ IsT1 (fun n => NS.nsDegree (T.inst n))) ∧
    (IsT2 (fun n => PC.pcDegree (T.inst n)) (onset T.k T.s T.n0) ↔
      IsT2 (fun n => NS.nsDegree (T.inst n)) (onset T.k T.s T.n0)) ∧
    (IsT3 (fun n => PC.pcDegree (T.inst n)) (onset T.k T.s T.n0) ↔
      IsT3 (fun n => NS.nsDegree (T.inst n)) (onset T.k T.s T.n0)) ∧
    (IsT4 (fun n => PC.pcDegree (T.inst n)) (onset T.k T.s T.n0) ↔
      IsT4 (fun n => NS.nsDegree (T.inst n)) (onset T.k T.s T.n0)) :=
  types_transfer (periodicProfile_pc T hp K H) (periodicProfile_ns T hp K H) hF
    T.pcProfile_le_nsProfile hub

end DegreeProfilesReview.Uniform
