/-
Agent B, round 5 (26 Sep 2026).  Referee R's **Lemma L** (R_referee/work/REFEREE_REPORT_D.md §5.2)
in Lean, on Agent D's rook definitions (`DCPRook.lean`, copied verbatim from D_bdm/lean).

Statement (any commutative ring for independence, any field for the rank bound): for every
`c`, the rook functions `ρ ↦ chi w ρ` (on the `c`-rooks of the full board `α × α`) of the
permutations `w` with an increasing subsequence of length `|α| - c` are linearly independent.
Hence the space of realisable functions at level `c`
(the range of `realMap c : K^{S_α} → K^{c-rooks}`, i.e. the row space of `W_c`) has dimension
`≥ #{w : LIS(w) ≥ |α| - c}`.

Proof (a variant of R's; lexicographic order instead of inversion number): for such `w` fix an
increasing set `I_w` of columns, `|I_w| = |α| - c`, and put `ρ_w = {(w y, y) : y ∉ I_w}`.
If `ρ_w ⊆ graph w'` and `w' ≠ w`, then `w'` agrees with `w` off `I_w`, and at the first column
`y₁` where they differ, `w' y₁ = w y₂` for some `y₂ ∈ I_w` with `y₂ > y₁`, so `w y₁ < w' y₁`:
`w <_lex w'`.  So the minor on rows `{w}` and columns `{ρ_w}` is unitriangular for the
lexicographic order of the value sequences, and a maximal element of a would-be dependency
gives a contradiction.

Main results:
* `linearIndependent_of_triangular` (abstract unitriangular criterion);
* `rookOff`, `rookOff_onBoard`, `card_rookOff`, `chi_rookOff_self`, `agree_of_chi_rookOff`;
* `lex_lt_of_agree` (the increasing filling is the strict lexicographic minimum of its coset);
* **`lemmaL_linearIndependent`**, **`lemmaL_card_le_finrank`**, **`lemmaL`** (LIS form),
  **`lemmaL_finset`** (count as a `Finset.card`);
* **`lemmaL_solve`** (over any commutative ring): prescribed values on the rooks `ρ_w` are realised
  by an element of `K[S_α]` supported on the permutations with `LIS ≥ |α| - c` (unitriangular
  system, `det = 1`); `exists_mulVec_eq_of_upperTriangular` is the abstract form;
* **`lemmaL_linearIndependent_gen`**, **`lemmaL_solve_gen`**: the same for ANY injective family of
  permutations `v i` with ANY increasing sets `I i` of size `|α| - c` (e.g. R's lex-first LIS, which
  FORCE needs); the `GoodPerm` versions use an arbitrary (`Classical.choose`) selection.
-/
import DCPRook
import Mathlib.Order.PiLex
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BLemmaL

open Finset ClaudeDCP

/-! ### An abstract unitriangular criterion -/

section Triangular

variable {K : Type*} [CommRing K] {ι X β : Type*} [LinearOrder β]

/-- A family `v i : X → K` with points `x i` such that `v i (x i) = 1` and `v j (x i) ≠ 0` forces
`j = i` or `key i < key j` is linearly independent. -/
theorem linearIndependent_of_triangular (v : ι → X → K) (x : ι → X) (key : ι → β)
    (hdiag : ∀ i, v i (x i) = 1)
    (hlow : ∀ i j, v j (x i) ≠ 0 → j = i ∨ key i < key j) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hne
  have hne' : (s.filter (fun j => g j ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hne⟩⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ key hne'
  have hmg : g m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hms : m ∈ s := (Finset.mem_filter.mp hm).1
  have h0 := congrFun hsum (x m)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  rw [Finset.sum_eq_single m] at h0
  · rw [hdiag, mul_one] at h0
    exact hmg h0
  · intro j hj hjm
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have hjs' : j ∈ s.filter (fun j => g j ≠ 0) := Finset.mem_filter.mpr ⟨hj, hgj⟩
      by_cases hv : v j (x m) = 0
      · rw [hv, mul_zero]
      · rcases hlow m j hv with h | h
        · exact absurd h hjm
        · exact absurd (hmax j hjs') (not_le.mpr h)
  · intro hm'
    exact absurd hms hm'

end Triangular

/-! ### The rook of a permutation off an increasing set -/

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- `w` is increasing on the column set `I`. -/
def IncOn (w : Equiv.Perm α) (I : Finset α) : Prop :=
  ∀ y ∈ I, ∀ y' ∈ I, y < y' → w y < w y'

theorem IncOn.mono {w : Equiv.Perm α} {I J : Finset α} (h : IncOn w I) (hJ : J ⊆ I) :
    IncOn w J :=
  fun y hy y' hy' hlt => h y (hJ hy) y' (hJ hy') hlt

/-- `ρ_w = {(w y, y) : y ∉ I}`: the part of the graph of `w` off the columns `I`. -/
def rookOff (w : Equiv.Perm α) (I : Finset α) : Finset (α × α) :=
  (univ \ I).image (fun y => (w y, y))

theorem mem_rookOff {w : Equiv.Perm α} {I : Finset α} {p : α × α} :
    p ∈ rookOff w I ↔ p.2 ∉ I ∧ p.1 = w p.2 := by
  unfold rookOff
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(Finset.mem_sdiff.mp hy).2, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.2, Finset.mem_sdiff.mpr ⟨mem_univ _, h1⟩, Prod.ext h2.symm rfl⟩

theorem rookOff_isRook (w : Equiv.Perm α) (I : Finset α) : IsRook (rookOff w I) := by
  intro p hp q hq hpq
  obtain ⟨-, hp2⟩ := mem_rookOff.mp hp
  obtain ⟨-, hq2⟩ := mem_rookOff.mp hq
  rcases hpq with h | h
  · have h2 : p.2 = q.2 := w.injective (hp2.symm.trans (h.trans hq2))
    exact Prod.ext h h2
  · exact Prod.ext (by rw [hp2, hq2, h]) h

theorem rookOff_onBoard (w : Equiv.Perm α) (I : Finset α) :
    OnBoard (univ : Finset α) univ (rookOff w I) :=
  ⟨rookOff_isRook w I, fun _ _ => Finset.mem_product.mpr ⟨mem_univ _, mem_univ _⟩⟩

theorem card_rookOff (w : Equiv.Perm α) (I : Finset α) :
    (rookOff w I).card = Fintype.card α - I.card := by
  unfold rookOff
  rw [Finset.card_image_of_injective _ (fun y y' h => (Prod.mk.inj h).2),
    Finset.card_univ_diff]

variable {K : Type*} [CommRing K]

theorem chi_rookOff_self (w : Equiv.Perm α) (I : Finset α) :
    chi (K := K) w (rookOff w I) = 1 := by
  unfold chi
  rw [if_pos]
  intro p hp
  exact (mem_rookOff.mp hp).2.symm

theorem agree_of_chi_rookOff {w w' : Equiv.Perm α} {I : Finset α}
    (h : chi (K := K) w' (rookOff w I) ≠ 0) : ∀ y ∉ I, w' y = w y := by
  intro y hy
  unfold chi at h
  by_cases hc : ∀ p ∈ rookOff w I, w' p.2 = p.1
  · exact hc (w y, y) (mem_rookOff.mpr ⟨hy, rfl⟩)
  · rw [if_neg hc] at h
    exact absurd rfl h

/-- **The increasing filling is the strict lexicographic minimum**: if `w` is increasing on `I`
and `w'` agrees with `w` off `I`, then `w = w'` or `w <_lex w'` (value sequences compared
lexicographically along the columns). -/
theorem lex_lt_of_agree {w w' : Equiv.Perm α} {I : Finset α} (hinc : IncOn w I)
    (hag : ∀ y ∉ I, w' y = w y) (hne : w' ≠ w) :
    toLex (⇑w : α → α) < toLex (⇑w' : α → α) := by
  have hD : (univ.filter (fun y => w' y ≠ w y)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hne (Equiv.ext fun y => not_not.mp (h (mem_univ y)))
  set y1 := (univ.filter (fun y => w' y ≠ w y)).min' hD with hy1def
  have hy1 : w' y1 ≠ w y1 := (Finset.mem_filter.mp (Finset.min'_mem _ hD)).2
  have hbelow : ∀ y, y < y1 → w' y = w y := by
    intro y hy
    by_contra h
    exact absurd (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨mem_univ _, h⟩)) (not_le.mpr hy)
  have hy1I : y1 ∈ I := by
    by_contra h
    exact hy1 (hag y1 h)
  set y2 := w.symm (w' y1) with hy2def
  have hwy2 : w y2 = w' y1 := by simp [hy2def]
  have hy2ne : y2 ≠ y1 := fun h => hy1 (by rw [← hwy2, h])
  have hy2I : y2 ∈ I := by
    by_contra h
    exact hy2ne (w'.injective ((hag y2 h).trans hwy2))
  have hy2gt : y1 < y2 := by
    rcases lt_or_gt_of_ne hy2ne with h | h
    · exact absurd (w'.injective ((hbelow y2 h).trans hwy2)) hy2ne
    · exact h
  refine ⟨y1, fun j hj => (hbelow j hj).symm, ?_⟩
  show w y1 < w' y1
  rw [← hwy2]
  exact hinc y1 hy1I y2 hy2I hy2gt

/-! ### Lemma L -/

variable (α) in
/-- The `c`-rooks of the full board `α × α`. -/
def CRook (c : ℕ) : Type _ :=
  {ρ : Finset (α × α) // OnBoard (univ : Finset α) univ ρ ∧ ρ.card = c}

instance (c : ℕ) : Finite (CRook α c) := by
  unfold CRook
  infer_instance

variable (α) in
/-- The permutations with an increasing set of columns of size `|α| - c`, i.e. (for `c ≤ |α|`)
`LIS(w) ≥ |α| - c`. -/
def GoodPerm (c : ℕ) : Type _ :=
  {w : Equiv.Perm α // ∃ I : Finset α, IncOn w I ∧ I.card + c = Fintype.card α}

instance (c : ℕ) : Finite (GoodPerm α c) := by
  unfold GoodPerm
  infer_instance

/-- The chosen increasing set of a good permutation. -/
noncomputable def GoodPerm.inc {c : ℕ} (w : GoodPerm α c) : Finset α := Classical.choose w.2

theorem GoodPerm.inc_spec {c : ℕ} (w : GoodPerm α c) :
    IncOn w.1 w.inc ∧ w.inc.card + c = Fintype.card α :=
  Classical.choose_spec w.2

/-- The chosen `c`-rook `ρ_w` of a good permutation. -/
noncomputable def GoodPerm.rook {c : ℕ} (w : GoodPerm α c) : CRook α c :=
  ⟨rookOff w.1 w.inc, rookOff_onBoard _ _, by
    rw [card_rookOff]
    have := w.inc_spec.2
    omega⟩

/-- **Lemma L (independence form)**: over any commutative ring, the rook functions of the
permutations with `LIS ≥ |α| - c`, restricted to the `c`-rooks, are linearly independent. -/
theorem lemmaL_linearIndependent (c : ℕ) :
    LinearIndependent K (fun w : GoodPerm α c => fun ρ : CRook α c => chi (K := K) w.1 ρ.1) := by
  refine linearIndependent_of_triangular _ (fun w => w.rook) (fun w => toLex (⇑w.1 : α → α))
    (fun w => chi_rookOff_self w.1 w.inc) ?_
  intro i j hij
  by_cases hji : j.1 = i.1
  · exact Or.inl (Subtype.ext hji)
  · exact Or.inr (lex_lt_of_agree i.inc_spec.1 (agree_of_chi_rookOff hij) hji)

variable (K) in
/-- The realisation map `K^{S_α} → K^{c-rooks}`, `a ↦ (ρ ↦ realFn a ρ)`; its matrix is `W_c` and
its range is the space `R_c` of realisable functions at level `c`. -/
def realMap (c : ℕ) : (Equiv.Perm α → K) →ₗ[K] (CRook α c → K) where
  toFun a ρ := realFn a ρ.1
  map_add' a b := by
    funext ρ
    exact realFn_add a b ρ.1
  map_smul' r a := by
    funext ρ
    simp only [realFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem realMap_single (c : ℕ) (w : Equiv.Perm α) (ρ : CRook α c) :
    realMap K c (Pi.single w 1) ρ = chi (K := K) w ρ.1 := by
  classical
  show realFn (Pi.single w 1) ρ.1 = chi w ρ.1
  unfold realFn
  rw [Finset.sum_eq_single w]
  · rw [Pi.single_eq_same, one_mul]
  · intro w' _ hw'
    rw [Pi.single_eq_of_ne hw', zero_mul]
  · intro h
    exact absurd (mem_univ w) h

section Field

variable {F : Type*} [Field F]

/-- **Lemma L (rank form)**: `rank W_c = dim R_c ≥ #{w : LIS(w) ≥ |α| - c}` over any field. -/
theorem lemmaL_card_le_finrank (c : ℕ) :
    Nat.card (GoodPerm α c) ≤ Module.finrank F (LinearMap.range (realMap F (α := α) c)) := by
  have : Fintype (GoodPerm α c) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  let v : GoodPerm α c → LinearMap.range (realMap F (α := α) c) := fun w =>
    ⟨fun ρ => chi (K := F) w.1 ρ.1, ⟨Pi.single w.1 1, funext fun ρ => realMap_single c w.1 ρ⟩⟩
  have hv : LinearIndependent F v := by
    refine LinearIndependent.of_comp (LinearMap.range (realMap F (α := α) c)).subtype ?_
    exact lemmaL_linearIndependent (K := F) c
  exact hv.fintype_card_le_finrank

/-- **Lemma L, LIS form** (R's statement): for `c ≤ |α|`,
`#{w ∈ S_α : LIS(w) ≥ |α| - c} ≤ rank W_c`, where `LIS(w) ≥ m` means that `w` is increasing on
some set of `m` columns. -/
theorem lemmaL (c : ℕ) (hc : c ≤ Fintype.card α) :
    Nat.card {w : Equiv.Perm α // ∃ I : Finset α, IncOn w I ∧ Fintype.card α - c ≤ I.card} ≤
      Module.finrank F (LinearMap.range (realMap F (α := α) c)) := by
  refine le_trans (le_of_eq ?_) (lemmaL_card_le_finrank (F := F) c)
  unfold GoodPerm
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  constructor
  · rintro ⟨I, hI, hcard⟩
    obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hcard
    exact ⟨J, hI.mono hJI, by omega⟩
  · rintro ⟨I, hI, hcard⟩
    exact ⟨I, hI, by omega⟩

open Classical in
/-- The same count as a `Finset.card` over `S_α`. -/
theorem lemmaL_finset (c : ℕ) (hc : c ≤ Fintype.card α) :
    (univ.filter (fun w : Equiv.Perm α =>
        ∃ I : Finset α, IncOn w I ∧ Fintype.card α - c ≤ I.card)).card ≤
      Module.finrank F (LinearMap.range (realMap F (α := α) c)) := by
  refine le_trans (le_of_eq ?_) (lemmaL (F := F) c hc)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Field

/-! ### Solving the unitriangular system over any commutative ring -/

section Solve

/-- A unitriangular matrix over a commutative ring is invertible, so `M a = g` is solvable. -/
theorem exists_mulVec_eq_of_upperTriangular {ι : Type*} [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι K) (hT : M.BlockTriangular id) (hd : ∀ i, M i i = 1) (g : ι → K) :
    ∃ a : ι → K, M.mulVec a = g := by
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular hT]
    simp [hd]
  have hu : IsUnit M.det := by
    rw [hdet]
    exact isUnit_one
  refine ⟨M⁻¹.mulVec g, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]

/-- The key `w ↦ toLex ⇑w` is injective on good permutations. -/
theorem goodKey_injective (c : ℕ) :
    Function.Injective (fun w : GoodPerm α c => toLex (⇑w.1 : α → α)) := by
  intro w w' h
  apply Subtype.ext
  apply Equiv.ext
  intro y
  exact congrFun (toLex.injective h) y

/-- **Lemma L, solvability form** (any commutative ring): every assignment of values to the
rooks `ρ_w` (`w` with `LIS(w) ≥ |α| - c`) is the restriction of the rook function of an element
of `K[S_α]` supported on such permutations. -/
theorem lemmaL_solve (c : ℕ) (g : GoodPerm α c → K) :
    ∃ a : Equiv.Perm α → K,
      (∀ w, a w ≠ 0 → ∃ I : Finset α, IncOn w I ∧ I.card + c = Fintype.card α) ∧
      ∀ w : GoodPerm α c, realFn a (w.rook).1 = g w := by
  classical
  letI : Fintype (GoodPerm α c) := Fintype.ofFinite _
  letI : LinearOrder (GoodPerm α c) :=
    LinearOrder.lift' (fun w : GoodPerm α c => toLex (⇑w.1 : α → α)) (goodKey_injective c)
  let M : Matrix (GoodPerm α c) (GoodPerm α c) K := fun w w' => chi (K := K) w'.1 (w.rook).1
  have hT : M.BlockTriangular id := by
    intro i j hji
    by_contra hne
    by_cases hij : j.1 = i.1
    · exact lt_irrefl _ ((Subtype.ext hij : j = i) ▸ hji)
    · have h1 := lex_lt_of_agree i.inc_spec.1 (agree_of_chi_rookOff hne) hij
      exact lt_asymm h1 hji
  have hd : ∀ i, M i i = 1 := fun i => chi_rookOff_self i.1 i.inc
  obtain ⟨a', ha'⟩ := exists_mulVec_eq_of_upperTriangular M hT hd g
  refine ⟨fun w => ∑ w' ∈ univ.filter (fun w' : GoodPerm α c => w'.1 = w), a' w', ?_, ?_⟩
  · intro w hw
    obtain ⟨w', hw', -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have := (Finset.mem_filter.mp hw').2
    rw [← this]
    exact w'.2
  · intro w
    have key : realFn (fun w => ∑ w' ∈ univ.filter (fun w' : GoodPerm α c => w'.1 = w), a' w')
        (w.rook).1 = ∑ w' : GoodPerm α c, a' w' * chi (K := K) w'.1 (w.rook).1 := by
      unfold realFn
      simp_rw [Finset.sum_mul]
      rw [← Finset.sum_fiberwise univ (fun w' : GoodPerm α c => w'.1)
        (fun w' => a' w' * chi (K := K) w'.1 (w.rook).1)]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w' hw' => ?_
      rw [(Finset.mem_filter.mp hw').2]
    rw [key, ← ha']
    simp only [Matrix.mulVec, dotProduct, M]
    exact Finset.sum_congr rfl fun w' _ => mul_comm _ _

end Solve

/-! ### Arbitrary injective families and arbitrary choices of the increasing sets -/

section General

variable {ι : Type*} (c : ℕ) (v : ι → Equiv.Perm α) (I : ι → Finset α)

/-- The `c`-rook `ρ_i = {(v i y, y) : y ∉ I i}` of a family member. -/
def famRook (hI : ∀ i, (I i).card + c = Fintype.card α) (i : ι) : CRook α c :=
  ⟨rookOff (v i) (I i), rookOff_onBoard _ _, by
    rw [card_rookOff]
    have := hI i
    omega⟩

variable {c v I}

theorem famKey_injective (hv : Function.Injective v) :
    Function.Injective (fun i : ι => toLex (⇑(v i) : α → α)) := by
  intro i j h
  apply hv
  apply Equiv.ext
  intro y
  exact congrFun (toLex.injective h) y

/-- **Lemma L for an arbitrary family** (any commutative ring): if the `v i` are distinct and
`v i` is increasing on `I i`, `|I i| + c = |α|`, the rook functions of the `v i` on the `c`-rooks
are linearly independent. -/
theorem lemmaL_linearIndependent_gen (hv : Function.Injective v) (hinc : ∀ i, IncOn (v i) (I i))
    (hI : ∀ i, (I i).card + c = Fintype.card α) :
    LinearIndependent K (fun i : ι => fun ρ : CRook α c => chi (K := K) (v i) ρ.1) := by
  refine linearIndependent_of_triangular _ (famRook c v I hI) (fun i => toLex (⇑(v i) : α → α))
    (fun i => chi_rookOff_self (v i) (I i)) ?_
  intro i j hij
  by_cases hji : v j = v i
  · exact Or.inl (hv hji)
  · exact Or.inr (lex_lt_of_agree (hinc i) (agree_of_chi_rookOff hij) hji)

/-- **Lemma L, solvability for an arbitrary family** (any commutative ring): any values on the
rooks `ρ_i` are realised by an element of `K[S_α]` supported on the family. -/
theorem lemmaL_solve_gen [Finite ι] (hv : Function.Injective v) (hinc : ∀ i, IncOn (v i) (I i))
    (g : ι → K) :
    ∃ a : Equiv.Perm α → K, (∀ w, a w ≠ 0 → ∃ i, v i = w) ∧
      ∀ i, realFn a (rookOff (v i) (I i)) = g i := by
  classical
  letI : Fintype ι := Fintype.ofFinite _
  letI : LinearOrder ι := LinearOrder.lift' (fun i : ι => toLex (⇑(v i) : α → α))
    (famKey_injective hv)
  let M : Matrix ι ι K := fun i j => chi (K := K) (v j) (rookOff (v i) (I i))
  have hT : M.BlockTriangular id := by
    intro i j hji
    by_contra hne
    by_cases hij : v j = v i
    · exact lt_irrefl _ ((hv hij : j = i) ▸ hji)
    · have h1 := lex_lt_of_agree (hinc i) (agree_of_chi_rookOff hne) hij
      exact lt_asymm h1 hji
  have hd : ∀ i, M i i = 1 := fun i => chi_rookOff_self (v i) (I i)
  obtain ⟨a', ha'⟩ := exists_mulVec_eq_of_upperTriangular M hT hd g
  refine ⟨fun w => ∑ j ∈ univ.filter (fun j : ι => v j = w), a' j, ?_, ?_⟩
  · intro w hw
    obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  · intro i
    have key : realFn (fun w => ∑ j ∈ univ.filter (fun j : ι => v j = w), a' j)
        (rookOff (v i) (I i)) = ∑ j : ι, a' j * chi (K := K) (v j) (rookOff (v i) (I i)) := by
      unfold realFn
      simp_rw [Finset.sum_mul]
      rw [← Finset.sum_fiberwise univ (fun j : ι => v j)
        (fun j => a' j * chi (K := K) (v j) (rookOff (v i) (I i)))]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.mp hj).2]
    rw [key, ← ha']
    simp only [Matrix.mulVec, dotProduct, M]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end General

end BLemmaL
