/-
Claude, 27 Sep 2026.  Undecidability, part E3: the counting certificate for bijection systems.

Let `x_{rc}` (`r ∈ ρ`, `c ∈ κ`) be polynomials of degree `≤ 1` such that, modulo NS derivations,
every row sum and every column sum is `1` (in degree `e`) and every row collision
`x_{rc} x_{rc'}` and column collision `x_{rc} x_{r'c}` vanishes (in degree `2`).  Then

    C(|ρ|, k) - C(|κ|, k)   has an NS derivation of degree `k + e`.

Proof.  `e_k(R) = Σ_{|S|=k} Π_{r∈S} R_r` is `C(|ρ|, k)` modulo the row sums.  Expanding the
products, `e_k(R)` is the sum of the monomials of all partial functions `π : ρ ⇀ κ` with `k`-element
domain; those that are not injective contain a column collision.  Symmetrically for the columns,
and the injective partial functions in the two directions correspond by inversion, with equal
monomials.
-/
import UNSTools
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open MvPolynomial DegreeProfilesReview.NS

section Counting
variable {σ K : Type} [Field K] (Γ : Set (MvPolynomial σ K))

/-! ### Products of elements that are `1` modulo the span -/

theorem prod_sub_one_mem {ι : Type} (y : ι → MvPolynomial σ K) {e : ℕ}
    (hy : ∀ i, y i - 1 ∈ NSspan Γ e) (hyd : ∀ i, (y i).totalDegree ≤ 1) [DecidableEq ι]
    (S : Finset ι) : (∏ i ∈ S, y i) - 1 ∈ NSspan Γ (e + S.card) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have e1 : y a * ∏ i ∈ S, y i - 1 = y a * ((∏ i ∈ S, y i) - 1) + (y a - 1) := by ring
    rw [e1]
    refine add_mem ?_ (NSspan_mono' (by omega) (hy a))
    have := mul_mem_NSspan_of ih (hyd a)
    exact NSspan_mono' (by omega) this

theorem esum_sub_mem {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → MvPolynomial σ K) {e : ℕ}
    (hy : ∀ i, y i - 1 ∈ NSspan Γ e) (hyd : ∀ i, (y i).totalDegree ≤ 1) (k : ℕ) :
    (∑ S ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ S, y i) -
      ((Fintype.card ι).choose k : MvPolynomial σ K) ∈ NSspan Γ (e + k) := by
  have e1 : ((Fintype.card ι).choose k : MvPolynomial σ K) =
      ∑ _S ∈ Finset.powersetCard k (Finset.univ : Finset ι), (1 : MvPolynomial σ K) := by
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_one]
  rw [e1, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun S hS => ?_
  have := prod_sub_one_mem Γ y hy hyd S
  rwa [(Finset.mem_powersetCard.mp hS).2] at this

/-! ### Partial functions -/

variable {ρ κ : Type} [Fintype ρ] [Fintype κ] [DecidableEq ρ] [DecidableEq κ]

/-- The entry selected by a value of a partial function. -/
noncomputable def optVal (x : ρ → κ → MvPolynomial σ K) (r : ρ) : Option κ → MvPolynomial σ K
  | none => 1
  | some c => x r c

/-- The monomial of a partial function. -/
noncomputable def pmono (x : ρ → κ → MvPolynomial σ K) (π : ρ → Option κ) : MvPolynomial σ K :=
  ∏ r, optVal x r (π r)

/-- The domain of a partial function. -/
def pdom (π : ρ → Option κ) : Finset ρ := Finset.univ.filter fun r => π r ≠ none

/-- Injective on the domain. -/
def PInj (π : ρ → Option κ) : Prop := ∀ r r', π r ≠ none → π r = π r' → r = r'

theorem optVal_deg (x : ρ → κ → MvPolynomial σ K) (hdeg : ∀ r c, (x r c).totalDegree ≤ 1)
    (r : ρ) (o : Option κ) : (optVal x r o).totalDegree ≤ if o = none then 0 else 1 := by
  cases o with
  | none => simp [optVal]
  | some c => simpa [optVal] using hdeg r c

theorem pmono_deg (x : ρ → κ → MvPolynomial σ K) (hdeg : ∀ r c, (x r c).totalDegree ≤ 1)
    (π : ρ → Option κ) : (pmono x π).totalDegree ≤ (pdom π).card := by
  unfold pmono pdom
  refine le_trans (totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum fun r _ => optVal_deg x hdeg r (π r)) ?_
  rw [Finset.card_filter]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : π r = none <;> simp [h]

/-- The product of row sums over `S` expands into partial functions with domain `S`. -/
theorem prod_rowsum (x : ρ → κ → MvPolynomial σ K) (S : Finset ρ) :
    ∏ r ∈ S, (∑ c, x r c) = ∑ π ∈ Finset.univ.filter (fun π : ρ → Option κ => pdom π = S),
      pmono x π := by
  let T : ρ → Finset (Option κ) := fun r => if r ∈ S then Finset.univ.image some else {none}
  have h1 : ∏ r ∈ S, (∑ c, x r c) = ∏ r, ∑ o ∈ T r, optVal x r o := by
    have : ∀ r, ∑ o ∈ T r, optVal x r o = if r ∈ S then ∑ c, x r c else 1 := by
      intro r
      by_cases hr : r ∈ S
      · simp only [T, if_pos hr]
        rw [Finset.sum_image (fun a _ b _ h => Option.some.inj h)]
        rfl
      · simp [T, hr, optVal]
    simp_rw [this]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have h3 : Fintype.piFinset T = Finset.univ.filter (fun π : ρ → Option κ => pdom π = S) := by
    ext π
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and, T]
    constructor
    · intro h
      ext r
      simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and]
      have := h r
      by_cases hr : r ∈ S
      · rw [if_pos hr] at this
        obtain ⟨c, -, hc⟩ := Finset.mem_image.mp this
        simp [hr, ← hc]
      · rw [if_neg hr] at this
        simp [hr, Finset.mem_singleton.mp this]
    · intro h r
      have hr' : r ∈ S ↔ π r ≠ none := by
        rw [← h]; simp [pdom]
      by_cases hr : r ∈ S
      · rw [if_pos hr]
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hr'.mp hr)
        exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc.symm⟩
      · rw [if_neg hr]
        have : π r = none := by
          by_contra h'; exact hr (hr'.mpr h')
        simp [this]
  rw [h1, Finset.prod_univ_sum, h3]
  rfl

/-- The `k`-th elementary symmetric function of the row sums is the sum over partial functions
with `k`-element domain. -/
theorem esum_rows (x : ρ → κ → MvPolynomial σ K) (k : ℕ) :
    ∑ S ∈ Finset.powersetCard k Finset.univ, ∏ r ∈ S, (∑ c, x r c) =
      ∑ π ∈ Finset.univ.filter (fun π : ρ → Option κ => (pdom π).card = k), pmono x π := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := pdom) (t := Finset.powersetCard k Finset.univ)
    (fun π hπ => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (Finset.mem_filter.mp hπ).2⟩)]
  apply Finset.sum_congr rfl
  intro S hS
  rw [prod_rowsum]
  congr 1
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact ⟨by rw [h]; exact (Finset.mem_powersetCard.mp hS).2, h⟩
  · intro h; exact h.2

/-- A partial function that is not injective has a monomial containing a column collision. -/
theorem noninj_mem (x : ρ → κ → MvPolynomial σ K) (hdeg : ∀ r c, (x r c).totalDegree ≤ 1)
    (hcc : ∀ r r' c, r ≠ r' → x r c * x r' c ∈ NSspan Γ 2) (π : ρ → Option κ)
    (hπ : ¬ PInj π) : pmono x π ∈ NSspan Γ (pdom π).card := by
  unfold PInj at hπ
  push_neg at hπ
  obtain ⟨r, r', hr, he, hne⟩ := hπ
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hr
  have hc' : π r' = some c := by rw [← he, hc]
  let π' : ρ → Option κ := Function.update (Function.update π r none) r' none
  have hsplit : pmono x π = (x r c * x r' c) * pmono x π' := by
    have hr'mem : r' ∈ Finset.univ.erase r := Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ r'⟩
    have hA : ∀ g : ρ → MvPolynomial σ K, ∏ i, g i =
        g r * (g r' * ∏ i ∈ (Finset.univ.erase r).erase r', g i) := by
      intro g
      rw [Finset.mul_prod_erase _ _ hr'mem, Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    unfold pmono
    rw [hA (fun i => optVal x i (π i)), hA (fun i => optVal x i (π' i))]
    have hπ'r : π' r = none := by
      simp [π', Function.update_apply, hne]
    have hπ'r' : π' r' = none := by simp [π']
    simp only [hπ'r, hπ'r', hc, hc', optVal, one_mul]
    rw [mul_assoc]
    congr 2
    apply Finset.prod_congr rfl
    intro i hi
    have h1 : i ≠ r' := (Finset.mem_erase.mp hi).1
    have h2 : i ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [π', Function.update_apply, h1, h2]
  have hdom : (pdom π').card + 2 = (pdom π).card := by
    have hsub : pdom π' = ((pdom π).erase r).erase r' := by
      ext i
      simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, π',
        Function.update_apply]
      by_cases h1 : i = r' <;> by_cases h2 : i = r <;> simp_all
    rw [hsub, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
    · have : 2 ≤ (pdom π).card := by
        have hsub2 : ({r, r'} : Finset ρ) ⊆ pdom π := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl <;> simp [pdom, hc, hc']
        have := Finset.card_le_card hsub2
        rwa [Finset.card_pair hne] at this
      omega
    · simp [pdom, hc]
    · simp [pdom, hc', hne.symm]
  rw [hsplit, mul_comm]
  have := mul_mem_NSspan_of (hcc r r' c hne) (pmono_deg x hdeg π')
  exact NSspan_mono' (by omega) this

/-! ### Inversion of injective partial functions -/

theorem get_eq_of_eq_some {α : Type} {o : Option α} {h : o.isSome} {c : α} (e : o = some c) :
    o.get h = c :=
  Option.some_injective _ (by rw [Option.some_get]; exact e)

open Classical in
/-- The inverse partial function. -/
noncomputable def pinv (π : ρ → Option κ) (c : κ) : Option ρ :=
  if h : ∃ r, π r = some c then some h.choose else none

theorem pinv_spec {π : ρ → Option κ} (hπ : PInj π) (c : κ) (r : ρ) :
    pinv π c = some r ↔ π r = some c := by
  classical
  unfold pinv
  constructor
  · intro h
    split_ifs at h with h'
    · rw [← Option.some.inj h]; exact h'.choose_spec
  · intro h
    have h' : ∃ r, π r = some c := ⟨r, h⟩
    rw [dif_pos h']
    congr 1
    exact hπ _ _ (by rw [h'.choose_spec]; simp) (by rw [h'.choose_spec, h])

theorem pinv_pinj {π : ρ → Option κ} (hπ : PInj π) : PInj (pinv π) := by
  intro c c' hc he
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hc
  have h1 := (pinv_spec hπ c r).mp hr
  have h2 := (pinv_spec hπ c' r).mp (by rw [← he, hr])
  rw [h1] at h2
  exact Option.some.inj h2

theorem pinv_pinv {π : ρ → Option κ} (hπ : PInj π) : pinv (pinv π) = π := by
  funext r
  apply Option.ext
  intro c
  rw [pinv_spec (pinv_pinj hπ), pinv_spec hπ]

theorem pinv_get_spec {π : ρ → Option κ} (hπ : PInj π) (c : κ) (hs : (pinv π c).isSome) :
    π ((pinv π c).get hs) = some c := (pinv_spec hπ c _).mp (Option.some_get hs).symm

theorem get_pinv_spec {π : ρ → Option κ} (hπ : PInj π) (r : ρ) (hs : (π r).isSome) :
    pinv π ((π r).get hs) = some r := (pinv_spec hπ _ r).mpr (Option.some_get hs).symm

theorem pdom_pinv_card {π : ρ → Option κ} (hπ : PInj π) : (pdom (pinv π)).card = (pdom π).card := by
  refine Finset.card_bij' (fun c hc => ((pinv π c).get (Option.isSome_iff_ne_none.mpr
      (Finset.mem_filter.mp hc).2)))
    (fun r hr => (π r).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hr).2))
    ?_ ?_ ?_ ?_
  · intro c hc
    have := pinv_get_spec hπ c (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hc).2)
    simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]; simp
  · intro r hr
    have := get_pinv_spec hπ r (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hr).2)
    simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]; simp
  · intro c hc
    exact get_eq_of_eq_some (pinv_get_spec hπ c _)
  · intro r hr
    exact get_eq_of_eq_some (get_pinv_spec hπ r _)

/-- The monomial of the inverse, read column by column, is the same. -/
theorem pmono_pinv (x : ρ → κ → MvPolynomial σ K) {π : ρ → Option κ} (hπ : PInj π) :
    pmono (fun c r => x r c) (pinv π) = pmono x π := by
  unfold pmono
  have hL : ∏ c, optVal (fun c r => x r c) c (pinv π c) =
      ∏ c ∈ pdom (pinv π), optVal (fun c r => x r c) c (pinv π c) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro c _ hc
    simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hc
    rw [hc]; rfl
  have hR : ∏ r, optVal x r (π r) = ∏ r ∈ pdom π, optVal x r (π r) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro r _ hr
    simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hr
    rw [hr]; rfl
  rw [hL, hR]
  refine Finset.prod_bij' (fun c hc => ((pinv π c).get (Option.isSome_iff_ne_none.mpr
      (Finset.mem_filter.mp hc).2)))
    (fun r hr => (π r).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hr).2))
    ?_ ?_ ?_ ?_ ?_
  · intro c hc
    have := pinv_get_spec hπ c (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hc).2)
    simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]; simp
  · intro r hr
    have := get_pinv_spec hπ r (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hr).2)
    simp only [pdom, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [this]; simp
  · intro c hc
    exact get_eq_of_eq_some (pinv_get_spec hπ c _)
  · intro r hr
    exact get_eq_of_eq_some (get_pinv_spec hπ r _)
  · intro c hc
    have h1 := pinv_get_spec hπ c (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hc).2)
    have h2 : pinv π c = some ((pinv π c).get (Option.isSome_iff_ne_none.mpr
        (Finset.mem_filter.mp hc).2)) := (Option.some_get _).symm
    conv_lhs => rw [h2]
    rw [h1]
    rfl

/-! ### The counting certificate -/

/-- **Counting in two ways.** -/
theorem counting (x : ρ → κ → MvPolynomial σ K) {e : ℕ} (k : ℕ)
    (hdeg : ∀ r c, (x r c).totalDegree ≤ 1)
    (hrc : ∀ r c c', c ≠ c' → x r c * x r c' ∈ NSspan Γ 2)
    (hcc : ∀ r r' c, r ≠ r' → x r c * x r' c ∈ NSspan Γ 2)
    (hrs : ∀ r, (∑ c, x r c) - 1 ∈ NSspan Γ e)
    (hcs : ∀ c, (∑ r, x r c) - 1 ∈ NSspan Γ e) :
    ((Fintype.card ρ).choose k : MvPolynomial σ K) - ((Fintype.card κ).choose k : MvPolynomial σ K)
      ∈ NSspan Γ (k + e) := by
  classical
  let xT : κ → ρ → MvPolynomial σ K := fun c r => x r c
  have hRd : ∀ r, (∑ c, x r c).totalDegree ≤ 1 := fun r =>
    le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun c _ => hdeg r c)
  have hCd : ∀ c, (∑ r, x r c).totalDegree ≤ 1 := fun c =>
    le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun r _ => hdeg r c)
  have hA := esum_sub_mem Γ (fun r => ∑ c, x r c) hrs hRd k
  have hB := esum_sub_mem Γ (fun c => ∑ r, x r c) hcs hCd k
  rw [esum_rows] at hA
  rw [esum_rows xT] at hB
  -- split off the non-injective partial functions
  set P := Finset.univ.filter (fun π : ρ → Option κ => (pdom π).card = k)
  set Q := Finset.univ.filter (fun τ : κ → Option ρ => (pdom τ).card = k)
  have hPn : ∑ π ∈ P.filter (fun π => ¬ PInj π), pmono x π ∈ NSspan Γ k := by
    refine Submodule.sum_mem _ fun π hπ => ?_
    obtain ⟨hπP, hni⟩ := Finset.mem_filter.mp hπ
    have := noninj_mem Γ x hdeg hcc π hni
    rwa [(Finset.mem_filter.mp hπP).2] at this
  have hQn : ∑ τ ∈ Q.filter (fun τ => ¬ PInj τ), pmono xT τ ∈ NSspan Γ k := by
    refine Submodule.sum_mem _ fun τ hτ => ?_
    obtain ⟨hτQ, hni⟩ := Finset.mem_filter.mp hτ
    have := noninj_mem Γ xT (fun c r => hdeg r c) (fun c c' r h => hrc r c c' h) τ hni
    rwa [(Finset.mem_filter.mp hτQ).2] at this
  -- the injective ones agree
  have hinj : ∑ π ∈ P.filter PInj, pmono x π = ∑ τ ∈ Q.filter PInj, pmono xT τ := by
    refine Finset.sum_bij' (fun π _ => pinv π) (fun τ _ => pinv τ) ?_ ?_ ?_ ?_ ?_
    · intro π hπ
      obtain ⟨hπP, hπi⟩ := Finset.mem_filter.mp hπ
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, pinv_pinj hπi⟩
      rw [pdom_pinv_card hπi]; exact (Finset.mem_filter.mp hπP).2
    · intro τ hτ
      obtain ⟨hτQ, hτi⟩ := Finset.mem_filter.mp hτ
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, pinv_pinj hτi⟩
      rw [pdom_pinv_card hτi]; exact (Finset.mem_filter.mp hτQ).2
    · intro π hπ; exact pinv_pinv (Finset.mem_filter.mp hπ).2
    · intro τ hτ; exact pinv_pinv (Finset.mem_filter.mp hτ).2
    · intro π hπ; exact (pmono_pinv x (Finset.mem_filter.mp hπ).2).symm
  rw [← Finset.sum_filter_add_sum_filter_not P PInj] at hA
  rw [← Finset.sum_filter_add_sum_filter_not Q PInj] at hB
  have e1 : ((Fintype.card ρ).choose k : MvPolynomial σ K) - ((Fintype.card κ).choose k) =
      -((∑ π ∈ P.filter PInj, pmono x π + ∑ π ∈ P.filter (fun π => ¬ PInj π), pmono x π) -
        ((Fintype.card ρ).choose k : MvPolynomial σ K)) +
      ((∑ τ ∈ Q.filter PInj, pmono xT τ + ∑ τ ∈ Q.filter (fun τ => ¬ PInj τ), pmono xT τ) -
        ((Fintype.card κ).choose k : MvPolynomial σ K)) +
      (∑ π ∈ P.filter (fun π => ¬ PInj π), pmono x π -
        ∑ τ ∈ Q.filter (fun τ => ¬ PInj τ), pmono xT τ) := by
    rw [hinj]; ring
  rw [e1]
  refine add_mem (add_mem (neg_mem (NSspan_mono' (by omega) hA)) (NSspan_mono' (by omega) hB))
    (sub_mem (NSspan_mono' (by omega) hPn) (NSspan_mono' (by omega) hQn))

end Counting

end ClaudeUndec
