/-
Agent B, round 3 (26 Sep 2026).  Lemma D of `work/TPRIME_PROOF.md` (partition of unity over
labels), in a relative form that also gives the cone lemma (Lemma 3) and Cor. C.

Representation.  Rows form a finite type `ι`, labels a finite type `α`.  A partial tuple is a
map `t : ι → Option α`; `t j = none` means that row `j` is absent.  All the modules
`P_S(L) = R[Inj(S, L)]` for `S ⊆ ι`, `L ⊆ α` live inside the single `R`-module
`Fn R ι α = (ι → Option α) → R`, as the functions supported on the partial tuples with domain
exactly `S`, values in `L` and no repeated label (`Good S L`).  The operators are uniform:

* `part i x f t = [t i = none] f (t with row i := x)`   (the `x`-part in row `i`),
* `put i x w t = [t i = x] w (t with row i removed)`    (insert label `x` in row `i`),
* `del i = Σ_x part i x`                                  (marginal over row `i`),
* `rowAct σ f t = f (t ∘ σ)`                              (row permutations, `S_ι`).

`Soc Rr S L` = functions in `P_S(L)` all of whose marginals in the rows of `Rr` vanish
(`Soc_R^J(L)` of the paper with `R = Rr`, `J = S \ Rr`; `Soc_c(L)` is `Rr = S`).

Main results (no hypotheses beyond the stated cardinality bounds; `R` any commutative ring):
* `piRel_spec` (Lemma D, relative form): for `Rr ⊆ S`, `|Rr| + |S| + 1 ≤ |L|` and any fuel
  `m ≥ |S|`, the maps `piRel C m Rr L x` send `Soc Rr S L` into `Soc Rr S (L \ x)` for `x ∈ L`
  and sum to the identity on `Soc Rr S L`.
* `piRel_rowAct`: `rowAct σ ∘ piRel C m Rr L x = piRel C m (σ Rr) L x ∘ rowAct σ` for EVERY
  row permutation `σ` (no support hypothesis), so the maps are `S_Rr × S_J`-linear.
* `lemmaD`: the statement of Lemma D as an existence theorem.
* `corC` (Cor. C), `cone_spec` (Lemma 3, cone lemma) and their equivariance lemmas.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset

variable (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι]
  (α : Type) [Fintype α] [DecidableEq α]

/-- Functions on partial tuples. -/
abbrev Fn := (ι → Option α) → R

variable {R ι α}

/-! ### The operators -/

/-- The `x`-part in row `i`. -/
def part (i : ι) (x : α) : Module.End R (Fn R ι α) where
  toFun f t := if t i = none then f (update t i (some x)) else 0
  map_add' f g := by
    funext t
    by_cases h : t i = none <;> simp [h]
  map_smul' c f := by
    funext t
    by_cases h : t i = none <;> simp [h]

/-- Insert label `x` in row `i`. -/
def put (i : ι) (x : α) : Module.End R (Fn R ι α) where
  toFun w t := if t i = some x then w (update t i none) else 0
  map_add' f g := by
    funext t
    by_cases h : t i = some x <;> simp [h]
  map_smul' c f := by
    funext t
    by_cases h : t i = some x <;> simp [h]

/-- The marginal over row `i` (unsigned deletion). -/
def del (i : ι) : Module.End R (Fn R ι α) := ∑ x, part i x

/-- Row permutations. -/
def rowAct (σ : Equiv.Perm ι) : Module.End R (Fn R ι α) where
  toFun f t := f (t ∘ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem part_apply (i : ι) (x : α) (f : Fn R ι α) (t : ι → Option α) :
    part i x f t = if t i = none then f (update t i (some x)) else 0 := rfl

theorem put_apply (i : ι) (x : α) (w : Fn R ι α) (t : ι → Option α) :
    put i x w t = if t i = some x then w (update t i none) else 0 := rfl

theorem rowAct_apply (σ : Equiv.Perm ι) (f : Fn R ι α) (t : ι → Option α) :
    rowAct σ f t = f (t ∘ σ) := rfl

theorem del_apply (i : ι) (f : Fn R ι α) (t : ι → Option α) :
    del i f t = ∑ x, part i x f t := by
  rw [del, LinearMap.sum_apply, Finset.sum_apply]

theorem mul_apply' (A B : Module.End R (Fn R ι α)) (f : Fn R ι α) : (A * B) f = A (B f) := rfl

/-! ### Commutation rules -/

theorem part_part_comm {i j : ι} (h : i ≠ j) (x y : α) :
    part i x * part j y = (part j y * part i x : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro f
  funext t
  simp only [mul_apply', part_apply]
  rw [update_of_ne h.symm, update_of_ne h]
  by_cases hi : t i = none <;> by_cases hj : t j = none <;> simp [hi, hj, update_comm h]

theorem part_put_comm {i j : ι} (h : j ≠ i) (x y : α) :
    part j x * put i y = (put i y * part j x : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro f
  funext t
  simp only [mul_apply', part_apply, put_apply]
  rw [update_of_ne h.symm, update_of_ne h]
  by_cases hi : t i = some y <;> by_cases hj : t j = none <;> simp [hi, hj, update_comm h]

theorem del_put_comm {i j : ι} (h : j ≠ i) (y : α) :
    del j * put i y = (put i y * del j : Module.End R (Fn R ι α)) := by
  simp only [del, Finset.sum_mul, Finset.mul_sum, part_put_comm h]

theorem del_part_comm {i j : ι} (h : j ≠ i) (y : α) :
    del j * part i y = (part i y * del j : Module.End R (Fn R ι α)) := by
  simp only [del, Finset.sum_mul, Finset.mul_sum, part_part_comm h]

theorem del_comm (i j : ι) : del i * del j = (del j * del i : Module.End R (Fn R ι α)) := by
  by_cases h : i = j
  · rw [h]
  · simp only [del, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    exact part_part_comm (R := R) h _ _

theorem part_put_self_apply (i : ι) (x y : α) (w : Fn R ι α) (t : ι → Option α) :
    part i x (put i y w) t = if t i = none ∧ x = y then w t else 0 := by
  simp only [part_apply, put_apply, update_self, Option.some.injEq, update_idem]
  by_cases hi : t i = none
  · have : update t i none = t := by rw [← hi]; exact update_eq_self i t
    by_cases hxy : x = y <;> simp [hi, hxy, this]
  · simp [hi]

theorem del_put_self_apply (i : ι) (y : α) (w : Fn R ι α) (t : ι → Option α) :
    del i (put i y w) t = if t i = none then w t else 0 := by
  rw [del_apply]
  simp only [part_put_self_apply]
  by_cases hi : t i = none <;> simp [hi]

/-! ### Row permutations -/

theorem rowAct_part (σ : Equiv.Perm ι) (i : ι) (x : α) :
    rowAct σ * part i x = (part (σ i) x * rowAct σ : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro f
  funext t
  simp only [mul_apply', part_apply, rowAct_apply, comp_apply]
  rw [update_comp_equiv t σ (σ i) (some x), Equiv.symm_apply_apply]

theorem rowAct_put (σ : Equiv.Perm ι) (i : ι) (x : α) :
    rowAct σ * put i x = (put (σ i) x * rowAct σ : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro f
  funext t
  simp only [mul_apply', put_apply, rowAct_apply, comp_apply]
  rw [update_comp_equiv t σ (σ i) none, Equiv.symm_apply_apply]

theorem rowAct_del (σ : Equiv.Perm ι) (i : ι) :
    rowAct σ * del i = (del (σ i) * rowAct σ : Module.End R (Fn R ι α)) := by
  simp only [del, Finset.sum_mul, Finset.mul_sum, rowAct_part]

/-! ### Supports -/

/-- `t` is an injective partial tuple with domain `S` and labels in `L`. -/
structure Good (S : Finset ι) (L : Finset α) (t : ι → Option α) : Prop where
  dom : ∀ j, t j ≠ none ↔ j ∈ S
  val : ∀ j y, t j = some y → y ∈ L
  inj : ∀ j k y, t j = some y → t k = some y → j = k

/-- `P_S(L)`. -/
def P (S : Finset ι) (L : Finset α) : Submodule R (Fn R ι α) where
  carrier := {f | ∀ t, f t ≠ 0 → Good S L t}
  add_mem' {f g} hf hg t h := by
    by_cases h1 : f t = 0
    · exact hg t (by simpa [h1] using h)
    · exact hf t h1
  zero_mem' t h := absurd rfl h
  smul_mem' c f hf t h := hf t (by
    intro h0
    apply h
    show c * f t = 0
    rw [h0, mul_zero])

theorem mem_P {S : Finset ι} {L : Finset α} {f : Fn R ι α} :
    f ∈ P S L ↔ ∀ t, f t ≠ 0 → Good S L t := Iff.rfl

theorem P_mono {S : Finset ι} {L₁ L₂ : Finset α} (h : L₁ ⊆ L₂) :
    P S L₁ ≤ (P S L₂ : Submodule R (Fn R ι α)) := fun f hf t ht => by
  obtain ⟨h1, h2, h3⟩ := hf t ht
  exact ⟨h1, fun j y hy => h (h2 j y hy), h3⟩

theorem Good.none_of_not_mem {S : Finset ι} {L : Finset α} {t : ι → Option α} (g : Good S L t)
    {i : ι} (hi : i ∉ S) : t i = none := by
  by_contra h
  exact hi ((g.dom i).mp h)

theorem Good.part {S : Finset ι} {L : Finset α} {t : ι → Option α} {i : ι} {x : α}
    (g : Good S L (update t i (some x))) (hi : t i = none) : Good (S.erase i) (L.erase x) t := by
  refine ⟨fun j => ?_, fun j y hy => ?_, fun j k y hj hk => ?_⟩
  · by_cases hji : j = i
    · subst hji
      simp [hi]
    · rw [Finset.mem_erase, ← g.dom j, update_of_ne hji]
      simp [hji]
  · have hji : j ≠ i := by rintro rfl; simp [hi] at hy
    have hy' : update t i (some x) j = some y := by rw [update_of_ne hji]; exact hy
    refine Finset.mem_erase.mpr ⟨?_, g.val j y hy'⟩
    rintro rfl
    exact hji (g.inj j i y hy' (update_self i _ t))
  · have hji : j ≠ i := by rintro rfl; simp [hi] at hj
    have hki : k ≠ i := by rintro rfl; simp [hi] at hk
    exact g.inj j k y (by rw [update_of_ne hji]; exact hj) (by rw [update_of_ne hki]; exact hk)

theorem Good.put {S : Finset ι} {L : Finset α} {t : ι → Option α} {i : ι} {x : α}
    (g : Good S L (update t i none)) (hi : t i = some x) (hx : x ∉ L) :
    Good (insert i S) (insert x L) t := by
  have hiS : i ∉ S := by
    rw [← g.dom i]
    simp
  refine ⟨fun j => ?_, fun j y hy => ?_, fun j k y hj hk => ?_⟩
  · by_cases hji : j = i
    · subst hji
      simp [hi]
    · rw [Finset.mem_insert, ← g.dom j, update_of_ne hji]
      simp [hji]
  · by_cases hji : j = i
    · subst hji
      rw [hi] at hy
      cases hy
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (g.val j y (by rw [update_of_ne hji]; exact hy))
  · by_cases hji : j = i <;> by_cases hki : k = i
    · rw [hji, hki]
    · subst hji
      rw [hi] at hj
      cases hj
      exact absurd (g.val k x (by rw [update_of_ne hki]; exact hk)) hx
    · subst hki
      rw [hi] at hk
      cases hk
      exact absurd (g.val j x (by rw [update_of_ne hji]; exact hj)) hx
    · exact g.inj j k y (by rw [update_of_ne hji]; exact hj) (by rw [update_of_ne hki]; exact hk)

theorem part_mem_P {S : Finset ι} {L : Finset α} {f : Fn R ι α} (hf : f ∈ P S L) (i : ι)
    (x : α) : part i x f ∈ P (S.erase i) (L.erase x) := by
  intro t ht
  rw [part_apply] at ht
  by_cases hi : t i = none
  · rw [if_pos hi] at ht
    exact (hf _ ht).part hi
  · rw [if_neg hi] at ht
    exact absurd rfl ht

theorem part_eq_zero_of_not_mem_S {S : Finset ι} {L : Finset α} {f : Fn R ι α}
    (hf : f ∈ P S L) {i : ι} (hi : i ∉ S) (x : α) : part i x f = 0 := by
  funext t
  rw [part_apply]
  split_ifs with h
  · by_contra h0
    have g := hf _ h0
    have := (g.dom i).mp (by rw [update_self]; simp)
    exact hi this
  · rfl

theorem part_eq_zero_of_not_mem_L {S : Finset ι} {L : Finset α} {f : Fn R ι α}
    (hf : f ∈ P S L) (i : ι) {x : α} (hx : x ∉ L) : part i x f = 0 := by
  funext t
  rw [part_apply]
  split_ifs with h
  · by_contra h0
    exact hx ((hf _ h0).val i x (update_self i _ t))
  · rfl

theorem put_mem_P {S : Finset ι} {L : Finset α} {w : Fn R ι α} (hw : w ∈ P S L) (i : ι)
    {x : α} (hx : x ∉ L) : put i x w ∈ P (insert i S) (insert x L) := by
  intro t ht
  rw [put_apply] at ht
  by_cases hi : t i = some x
  · rw [if_pos hi] at ht
    exact (hw _ ht).put hi hx
  · rw [if_neg hi] at ht
    exact absurd rfl ht

theorem eq_of_P_not_mem {S : Finset ι} {L : Finset α} {w : Fn R ι α} (hw : w ∈ P S L)
    {i : ι} (hi : i ∉ S) (t : ι → Option α) : (if t i = none then w t else 0) = w t := by
  split_ifs with h
  · rfl
  · by_contra h0
    exact h ((hw t (Ne.symm h0)).none_of_not_mem hi)

theorem del_put_self {S : Finset ι} {L : Finset α} {w : Fn R ι α} (hw : w ∈ P S L)
    {i : ι} (hi : i ∉ S) (y : α) : del i (put i y w) = w := by
  funext t
  rw [del_put_self_apply, eq_of_P_not_mem hw hi]

theorem part_put_same {S : Finset ι} {L : Finset α} {w : Fn R ι α} (hw : w ∈ P S L)
    {i : ι} (hi : i ∉ S) (x : α) : part i x (put i x w) = w := by
  funext t
  rw [part_put_self_apply]
  simp only [and_true]
  exact eq_of_P_not_mem hw hi t

theorem part_put_ne_label {i : ι} {x y : α} (hxy : x ≠ y) (w : Fn R ι α) :
    part i x (put i y w) = 0 := by
  funext t
  rw [part_put_self_apply]
  simp [hxy]

/-- The `d`-parts of `put i d w`. -/
theorem part_put_d {S : Finset ι} {L : Finset α} {w : Fn R ι α} (hw : w ∈ P S L)
    {i : ι} (hi : i ∉ S) {d : α} (hd : d ∉ L) (j : ι) :
    part j d (put i d w) = if j = i then w else 0 := by
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, part_put_same hw hi]
  · rw [if_neg hji, ← mul_apply', part_put_comm hji, mul_apply',
      part_eq_zero_of_not_mem_L hw j hd, map_zero]

theorem part_put_other {S : Finset ι} {L : Finset α} {w : Fn R ι α} (hw : w ∈ P S L)
    {i : ι} {d x : α} (hd : d ∉ L) (hx : d ≠ x) (j : ι) : part j d (put i x w) = 0 := by
  by_cases hji : j = i
  · subst hji
    exact part_put_ne_label hx w
  · rw [← mul_apply', part_put_comm hji, mul_apply', part_eq_zero_of_not_mem_L hw j hd,
      map_zero]

theorem mem_P_erase {S : Finset ι} {L : Finset α} {f : Fn R ι α} (hf : f ∈ P S L) {d : α}
    (h : ∀ j, part j d f = 0) : f ∈ P S (L.erase d) := by
  intro t ht
  have g := hf t ht
  refine ⟨g.dom, fun j y hy => Finset.mem_erase.mpr ⟨?_, g.val j y hy⟩, g.inj⟩
  rintro rfl
  have h1 := congrFun (h j) (update t j none)
  rw [part_apply, if_pos (update_self j none t), update_idem] at h1
  have : update t j (some y) = t := by rw [← hy]; exact update_eq_self j t
  rw [this] at h1
  exact ht h1

/-! ### Relative socles -/

/-- `Soc_Rr^S(L)`: functions in `P_S(L)` whose marginals in the rows of `Rr` vanish. -/
def Soc (Rr S : Finset ι) (L : Finset α) : Submodule R (Fn R ι α) where
  carrier := {f | f ∈ P S L ∧ ∀ i ∈ Rr, del i f = 0}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun i hi => by rw [map_add, hf.2 i hi, hg.2 i hi,
    add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun i _ => map_zero _⟩
  smul_mem' c f hf := ⟨(P S L).smul_mem c hf.1, fun i hi => by rw [map_smul, hf.2 i hi, smul_zero]⟩

theorem mem_Soc {Rr S : Finset ι} {L : Finset α} {f : Fn R ι α} :
    f ∈ Soc Rr S L ↔ f ∈ P S L ∧ ∀ i ∈ Rr, del i f = 0 := Iff.rfl

theorem Soc_mono {Rr S : Finset ι} {L₁ L₂ : Finset α} (h : L₁ ⊆ L₂) :
    Soc Rr S L₁ ≤ (Soc Rr S L₂ : Submodule R (Fn R ι α)) :=
  fun _ hf => ⟨P_mono h hf.1, hf.2⟩

theorem part_mem_Soc {Rr S : Finset ι} {L : Finset α} {f : Fn R ι α} (hf : f ∈ Soc Rr S L)
    (i : ι) (x : α) : part i x f ∈ Soc (Rr.erase i) (S.erase i) (L.erase x) := by
  refine ⟨part_mem_P hf.1 i x, fun j hj => ?_⟩
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [← mul_apply', del_part_comm hji, mul_apply', hf.2 j (Finset.mem_erase.mp hj).2, map_zero]

/-- Inserting a label in a free row. -/
theorem put_mem_Soc {Rr S : Finset ι} {L : Finset α} {w : Fn R ι α} (hw : w ∈ Soc Rr S L)
    {i : ι} (hiR : i ∉ Rr) {x : α} (hx : x ∉ L) :
    put i x w ∈ Soc Rr (insert i S) (insert x L) := by
  refine ⟨put_mem_P hw.1 i hx, fun j hj => ?_⟩
  have hji : j ≠ i := by rintro rfl; exact hiR hj
  rw [← mul_apply', del_put_comm hji, mul_apply', hw.2 j hj, map_zero]

theorem mem_Soc_erase {Rr S : Finset ι} {L : Finset α} {f : Fn R ι α} (hf : f ∈ Soc Rr S L)
    {d : α} (h : ∀ j, part j d f = 0) : f ∈ Soc Rr S (L.erase d) :=
  ⟨mem_P_erase hf.1 h, hf.2⟩

/-! ### The correction map `F_{i,d}` -/

/-- `F_{i,d}(w) = (w with d in row i) - Σ_{x ∈ L} (π_x w with x in row i)`. -/
def corr (π : α → Module.End R (Fn R ι α)) (L : Finset α) (i : ι) (d : α) :
    Module.End R (Fn R ι α) :=
  put i d - ∑ x ∈ L, put i x * π x

/-- A family `π` is a partition of unity for `Soc Rr S L`. -/
def IsPartition (π : α → Module.End R (Fn R ι α)) (Rr S : Finset ι) (L : Finset α) : Prop :=
  (∀ y ∈ Soc Rr S L, ∀ x ∈ L, π x y ∈ Soc Rr S (L.erase x)) ∧
    ∀ y ∈ Soc Rr S L, ∑ x ∈ L, π x y = y

theorem corr_apply (π : α → Module.End R (Fn R ι α)) (L : Finset α) (i : ι) (d : α)
    (w : Fn R ι α) : corr π L i d w = put i d w - ∑ x ∈ L, put i x (π x w) := by
  rw [corr, LinearMap.sub_apply, LinearMap.sum_apply]
  rfl

/-- The correction lemma (Cor. C and the step of Lemma D): `F_{i,d}(w)` is a cycle in all rows
of `insert i Rr`, and its `d`-parts are `w` in row `i` and `0` elsewhere. -/
theorem corr_spec {π : α → Module.End R (Fn R ι α)} {Rr S : Finset ι} {L : Finset α}
    (hπ : IsPartition π Rr S L) {i : ι} (hi : i ∉ S) {d : α} (hd : d ∉ L) {w : Fn R ι α}
    (hw : w ∈ Soc Rr S L) :
    corr π L i d w ∈ Soc (insert i Rr) (insert i S) (insert d L) ∧
      ∀ j, part j d (corr π L i d w) = if j = i then w else 0 := by
  have hπw : ∀ x ∈ L, π x w ∈ Soc Rr S (L.erase x) := fun x hx => hπ.1 w hw x hx
  have hdx : ∀ x ∈ L, d ≠ x := fun x hx h => hd (h ▸ hx)
  rw [corr_apply]
  refine ⟨⟨?_, fun j hj => ?_⟩, fun j => ?_⟩
  · refine sub_mem (put_mem_P hw.1 i hd) (sum_mem fun x hx => ?_)
    have h1 := put_mem_P (hπw x hx).1 i (Finset.notMem_erase x L)
    rw [Finset.insert_erase hx] at h1
    exact P_mono (Finset.subset_insert d L) h1
  · rw [map_sub, map_sum]
    by_cases hji : j = i
    · subst hji
      rw [del_put_self hw.1 hi, Finset.sum_congr rfl fun x hx => del_put_self (hπw x hx).1 hi x,
        hπ.2 w hw, sub_self]
    · have hjR : j ∈ Rr := (Finset.mem_insert.mp hj).resolve_left hji
      rw [← mul_apply', del_put_comm hji, mul_apply', hw.2 j hjR, map_zero, zero_sub,
        neg_eq_zero]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [← mul_apply', del_put_comm hji, mul_apply', (hπw x hx).2 j hjR, map_zero]
  · rw [map_sub, map_sum, part_put_d hw.1 hi hd j,
      Finset.sum_eq_zero fun x hx => part_put_other (hπw x hx).1
        (fun h => hd (Finset.mem_of_mem_erase h)) (hdx x hx) j, sub_zero]

theorem rowAct_corr (σ : Equiv.Perm ι) {π π' : α → Module.End R (Fn R ι α)}
    (h : ∀ x, rowAct σ * π x = π' x * rowAct σ) (L : Finset α) (i : ι) (d : α) :
    rowAct σ * corr π L i d = corr π' L (σ i) d * rowAct σ := by
  simp only [corr, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, rowAct_put]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, rowAct_put, mul_assoc, h x, ← mul_assoc]

/-! ### The recursion -/

/-- A choice of one label in every nonempty finite set of labels. -/
structure Chooser (α : Type) where
  ch : Finset α → α
  mem : ∀ L : Finset α, L.Nonempty → ch L ∈ L

/-- The operator acting in row `i` in one step: the correction map for cycle rows, plain
insertion of `d` for free rows. -/
def rowOp (Pm : Finset ι → Finset α → α → Module.End R (Fn R ι α)) (Rr : Finset ι)
    (L' : Finset α) (d x : α) (i : ι) : Module.End R (Fn R ι α) :=
  if i ∈ Rr then corr (Pm (Rr.erase i) (L'.erase x)) (L'.erase x) i d else put i d

/-- `π_x` for `x ≠ d`, built from the level-below maps `Pm`. -/
def stepAux (Pm : Finset ι → Finset α → α → Module.End R (Fn R ι α)) (Rr : Finset ι)
    (L' : Finset α) (d x : α) : Module.End R (Fn R ι α) :=
  ∑ i, rowOp Pm Rr L' d x i * Pm (Rr.erase i) L' x * part i d

/-- One step of the recursion. -/
def stepFn (Pm : Finset ι → Finset α → α → Module.End R (Fn R ι α)) (d : α) (Rr : Finset ι)
    (L : Finset α) (x : α) : Module.End R (Fn R ι α) :=
  if x = d then 1 - ∑ x' ∈ L.erase d, stepAux Pm Rr (L.erase d) d x'
  else stepAux Pm Rr (L.erase d) d x

/-- The maps of Lemma D (relative form); `m` is the number of rows. -/
noncomputable def piRel (C : Chooser α) : ℕ → Finset ι → Finset α → α → Module.End R (Fn R ι α)
  | 0, _, L, x => if x = C.ch L then 1 else 0
  | m + 1, Rr, L, x => stepFn (piRel C m) (C.ch L) Rr L x

theorem piRel_zero (C : Chooser α) (Rr : Finset ι) (L : Finset α) (x : α) :
    piRel (R := R) C 0 Rr L x = if x = C.ch L then 1 else 0 := rfl

theorem piRel_succ (C : Chooser α) (m : ℕ) (Rr : Finset ι) (L : Finset α) (x : α) :
    piRel (R := R) C (m + 1) Rr L x = stepFn (piRel C m) (C.ch L) Rr L x := rfl

theorem stepAux_apply (Pm : Finset ι → Finset α → α → Module.End R (Fn R ι α)) (Rr : Finset ι)
    (L' : Finset α) (d x : α) (y : Fn R ι α) :
    stepAux Pm Rr L' d x y = ∑ i, rowOp Pm Rr L' d x i (Pm (Rr.erase i) L' x (part i d y)) := by
  rw [stepAux, LinearMap.sum_apply]
  rfl

/-! ### Equivariance under row permutations -/

theorem rowAct_rowOp (σ : Equiv.Perm ι) {Pm Pm' : Finset ι → Finset α → α → Module.End R (Fn R ι α)}
    (h : ∀ Rr L x, rowAct σ * Pm Rr L x = Pm' (Rr.map σ.toEmbedding) L x * rowAct σ)
    (Rr : Finset ι) (L' : Finset α) (d x : α) (i : ι) :
    rowAct σ * rowOp Pm Rr L' d x i = rowOp Pm' (Rr.map σ.toEmbedding) L' d x (σ i) * rowAct σ := by
  unfold rowOp
  by_cases hi : i ∈ Rr
  · have hi' : σ i ∈ Rr.map σ.toEmbedding := Finset.mem_map_of_mem _ hi
    rw [if_pos hi, if_pos hi']
    have := Finset.map_erase σ.toEmbedding Rr i
    simp only [Equiv.toEmbedding_apply] at this
    rw [← this]
    exact rowAct_corr σ (fun x' => h _ _ x') _ i d
  · have hi' : σ i ∉ Rr.map σ.toEmbedding := by
      rw [Finset.mem_map_equiv]
      simpa using hi
    rw [if_neg hi, if_neg hi']
    exact rowAct_put σ i d

theorem rowAct_stepAux (σ : Equiv.Perm ι)
    {Pm Pm' : Finset ι → Finset α → α → Module.End R (Fn R ι α)}
    (h : ∀ Rr L x, rowAct σ * Pm Rr L x = Pm' (Rr.map σ.toEmbedding) L x * rowAct σ)
    (Rr : Finset ι) (L' : Finset α) (d x : α) :
    rowAct σ * stepAux Pm Rr L' d x = stepAux Pm' (Rr.map σ.toEmbedding) L' d x * rowAct σ := by
  unfold stepAux
  rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := Finset.map_erase σ.toEmbedding Rr i
  simp only [Equiv.toEmbedding_apply] at hm
  rw [← mul_assoc, ← mul_assoc, rowAct_rowOp σ h, mul_assoc _ (rowAct σ), h, ← hm,
    mul_assoc, mul_assoc, mul_assoc, rowAct_part]
  simp only [mul_assoc]

/-- The maps of Lemma D commute with ALL row permutations (transporting the cycle rows). -/
theorem piRel_rowAct (C : Chooser α) (σ : Equiv.Perm ι) (m : ℕ) :
    ∀ (Rr : Finset ι) (L : Finset α) (x : α),
      rowAct σ * piRel (R := R) C m Rr L x = piRel C m (Rr.map σ.toEmbedding) L x * rowAct σ := by
  induction m with
  | zero =>
    intro Rr L x
    rw [piRel_zero, piRel_zero]
    split_ifs <;> simp
  | succ m ih =>
    intro Rr L x
    rw [piRel_succ, piRel_succ]
    unfold stepFn
    split_ifs
    · rw [mul_sub, sub_mul, mul_one, one_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun x' _ => rowAct_stepAux σ ih _ _ _ _
    · exact rowAct_stepAux σ ih _ _ _ _

/-! ### Lemma D -/

theorem insert_erase_erase {L : Finset α} {d x : α} (hd : d ∈ L) (hdx : d ≠ x) :
    insert d ((L.erase d).erase x) = L.erase x := by
  rw [Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hdx, hd⟩)]

theorem P_empty {L L' : Finset α} : P (∅ : Finset ι) L ≤ (P ∅ L' : Submodule R (Fn R ι α)) :=
  fun f hf t ht => by
    have g := hf t ht
    refine ⟨g.dom, fun j y hy => ?_, g.inj⟩
    have := (g.dom j).mp (by rw [hy]; simp)
    simp at this

/-- **Lemma D** (relative form).  For `Rr ⊆ S` and `|Rr| + |S| + 1 ≤ |L|` the maps
`piRel C |S| Rr L x` (`x ∈ L`) form a partition of unity for `Soc Rr S L`. -/
theorem piRel_spec (C : Chooser α) (m : ℕ) :
    ∀ (Rr S : Finset ι) (L : Finset α), S.card ≤ m → Rr ⊆ S → Rr.card + S.card + 1 ≤ L.card →
      IsPartition (piRel (R := R) C m Rr L) Rr S L := by
  induction m with
  | zero =>
    intro Rr S L hS hRS hL
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    subst hS0
    have hR0 : Rr = ∅ := Finset.subset_empty.mp hRS
    subst hR0
    have hL0 : L.Nonempty := Finset.card_pos.mp (by rw [Finset.card_empty] at hL; omega)
    refine ⟨fun y hy x _ => ?_, fun y _ => ?_⟩
    · rw [piRel_zero]
      split_ifs
      · exact ⟨P_empty hy.1, fun i hi => absurd hi (Finset.notMem_empty i)⟩
      · exact zero_mem _
    · simp only [piRel_zero]
      rw [Finset.sum_eq_single (C.ch L)]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (C.mem L hL0) h
  | succ m ih =>
    intro Rr S L hS hRS hL
    have hL0 : L.Nonempty := Finset.card_pos.mp (by omega)
    set d := C.ch L with hd_def
    have hd : d ∈ L := C.mem L hL0
    set L' := L.erase d with hL'
    have hL'card : L'.card = L.card - 1 := Finset.card_erase_of_mem hd
    -- the level-`m` facts used for every row `i ∈ S`
    have ih1 : ∀ i ∈ S, IsPartition (piRel (R := R) C m (Rr.erase i) L') (Rr.erase i) (S.erase i) L' := by
      intro i hi
      have h2 : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
      refine ih _ _ _ (by rw [Finset.card_erase_of_mem hi]; omega)
        (Finset.erase_subset_erase i hRS) ?_
      have h1 := Finset.card_erase_le (s := Rr) (a := i)
      rw [Finset.card_erase_of_mem hi, hL'card]
      omega
    have ih2 : ∀ i ∈ Rr, ∀ x ∈ L', IsPartition (piRel (R := R) C m (Rr.erase i) (L'.erase x))
        (Rr.erase i) (S.erase i) (L'.erase x) := by
      intro i hi x hx
      have hiS := hRS hi
      have h2 : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hiS⟩
      refine ih _ _ _ (by rw [Finset.card_erase_of_mem hiS]; omega)
        (Finset.erase_subset_erase i hRS) ?_
      rw [Finset.card_erase_of_mem hi, Finset.card_erase_of_mem hiS,
        Finset.card_erase_of_mem hx, hL'card]
      have : 1 ≤ Rr.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    -- the value of one row term
    have hterm : ∀ y ∈ Soc Rr S L, ∀ x ∈ L', ∀ i,
        rowOp (piRel (R := R) C m) Rr L' d x i (piRel C m (Rr.erase i) L' x (part i d y)) ∈
            Soc Rr S (L.erase x) ∧
          ∀ j, part j d (rowOp (piRel (R := R) C m) Rr L' d x i
              (piRel C m (Rr.erase i) L' x (part i d y))) =
            if j = i then piRel C m (Rr.erase i) L' x (part i d y) else 0 := by
      intro y hy x hx i
      have hdx : d ≠ x := fun h => (Finset.mem_erase.mp hx).1 h.symm
      have hdL'x : d ∉ L'.erase x := fun h => by
        rw [hL'] at h
        exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
      by_cases hiS : i ∈ S
      · have hpy : part i d y ∈ Soc (Rr.erase i) (S.erase i) L' := part_mem_Soc hy i d
        have hv := (ih1 i hiS).1 _ hpy x hx
        have hins : insert d (L'.erase x) = L.erase x := insert_erase_erase hd hdx
        by_cases hiR : i ∈ Rr
        · unfold rowOp
          rw [if_pos hiR]
          obtain ⟨h1, h2⟩ := corr_spec (ih2 i hiR x hx) (Finset.notMem_erase i S) hdL'x hv
          rw [Finset.insert_erase hiR, Finset.insert_erase hiS, hins] at h1
          exact ⟨h1, h2⟩
        · unfold rowOp
          rw [if_neg hiR]
          have hRe : Rr.erase i = Rr := Finset.erase_eq_of_notMem hiR
          have h1 := put_mem_Soc hv (Finset.notMem_erase i Rr) hdL'x
          have hSoc : Soc (Rr.erase i) S (L.erase x) = (Soc Rr S (L.erase x) :
              Submodule R (Fn R ι α)) := by rw [hRe]
          rw [Finset.insert_erase hiS, hins, hSoc] at h1
          refine ⟨h1, fun j => part_put_d hv.1 (Finset.notMem_erase i S) hdL'x j⟩
      · have h0 : part i d y = 0 := part_eq_zero_of_not_mem_S hy.1 hiS d
        rw [h0, map_zero, map_zero]
        refine ⟨zero_mem _, fun j => ?_⟩
        rw [map_zero]
        split_ifs <;> rfl
    have hA : ∀ y ∈ Soc Rr S L, ∀ x ∈ L',
        stepAux (piRel (R := R) C m) Rr L' d x y ∈ Soc Rr S (L.erase x) := by
      intro y hy x hx
      rw [stepAux_apply]
      exact sum_mem fun i _ => (hterm y hy x hx i).1
    have hB : ∀ y ∈ Soc Rr S L, ∀ x ∈ L', ∀ j,
        part j d (stepAux (piRel (R := R) C m) Rr L' d x y) =
          piRel C m (Rr.erase j) L' x (part j d y) := by
      intro y hy x hx j
      rw [stepAux_apply, map_sum]
      rw [Finset.sum_congr rfl fun i _ => (hterm y hy x hx i).2 j]
      simp
    have hstep : ∀ x ∈ L', piRel (R := R) C (m + 1) Rr L x = stepAux (piRel C m) Rr L' d x := by
      intro x hx
      rw [piRel_succ]
      unfold stepFn
      rw [if_neg (Finset.mem_erase.mp hx).1]
    have hdval : ∀ y, piRel (R := R) C (m + 1) Rr L d y =
        y - ∑ x' ∈ L', stepAux (piRel C m) Rr L' d x' y := by
      intro y
      rw [piRel_succ]
      unfold stepFn
      rw [if_pos rfl, LinearMap.sub_apply, LinearMap.sum_apply]
      rfl
    refine ⟨fun y hy x hx => ?_, fun y hy => ?_⟩
    · by_cases hxd : x = d
      · subst hxd
        rw [hdval]
        have hmem : y - ∑ x' ∈ L', stepAux (piRel (R := R) C m) Rr L' d x' y ∈ Soc Rr S L :=
          sub_mem hy (sum_mem fun x' hx' =>
            Soc_mono (Finset.erase_subset x' L) (hA y hy x' hx'))
        refine mem_Soc_erase hmem fun j => ?_
        rw [map_sub, map_sum, Finset.sum_congr rfl fun x' hx' => hB y hy x' hx' j]
        by_cases hjS : j ∈ S
        · rw [(ih1 j hjS).2 _ (part_mem_Soc hy j d), sub_self]
        · rw [part_eq_zero_of_not_mem_S hy.1 hjS d]
          simp
      · have hx' : x ∈ L' := Finset.mem_erase.mpr ⟨hxd, hx⟩
        rw [hstep x hx']
        exact hA y hy x hx'
    · rw [← Finset.add_sum_erase L _ hd, hdval]
      have hsum : ∑ x ∈ L', piRel (R := R) C (m + 1) Rr L x y =
          ∑ x ∈ L', stepAux (piRel C m) Rr L' d x y :=
        Finset.sum_congr rfl fun x hx => by rw [hstep x hx]
      rw [hsum]
      exact sub_add_cancel _ _

/-! ### Lemma D as stated in the paper -/

/-- A chooser with a default value. -/
noncomputable def Chooser.ofDefault (x₀ : α) : Chooser α where
  ch L := if h : L.Nonempty then h.choose else x₀
  mem L h := by rw [dif_pos h]; exact h.choose_spec

/-- **Lemma D.**  For `|L| ≥ 2|S| + 1` there are `R`-linear maps `π_x`, `x ∈ L`, with
`π_x (Soc_S(L)) ⊆ Soc_S(L \ x)` and `Σ_{x ∈ L} π_x = id` on `Soc_S(L)`, commuting with every
row permutation that preserves `S`. -/
theorem lemmaD (S : Finset ι) (L : Finset α) (hL : 2 * S.card + 1 ≤ L.card) :
    ∃ π : α → Module.End R (Fn R ι α),
      (∀ y ∈ Soc S S L, ∀ x ∈ L, π x y ∈ Soc S S (L.erase x)) ∧
      (∀ y ∈ Soc S S L, ∑ x ∈ L, π x y = y) ∧
      ∀ σ : Equiv.Perm ι, S.map σ.toEmbedding = S → ∀ x, rowAct σ * π x = π x * rowAct σ := by
  have hne : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₀, -⟩ := hne
  let C := Chooser.ofDefault x₀
  have h := piRel_spec (R := R) C S.card S S L le_rfl (subset_refl S) (by omega)
  refine ⟨piRel C S.card S L, h.1, h.2, fun σ hσ x => ?_⟩
  have := piRel_rowAct (R := R) C σ S.card S L x
  rwa [hσ] at this

/-! ### Corollary C (column splitting) -/

/-- The section of the `∞`-part map: `(w_i)_i ↦ Σ_{i ∈ S} F_{i,∞}(w_i)`. -/
noncomputable def colSection (C : Chooser α) (S : Finset ι) (L : Finset α) (inf : α)
    (w : ι → Fn R ι α) : Fn R ι α :=
  ∑ i ∈ S, corr (piRel C (S.card - 1) (S.erase i) L) L i inf (w i)

theorem colSection_spec (C : Chooser α) (S : Finset ι) (L : Finset α) {inf : α}
    (hinf : inf ∉ L) (hL : 2 * S.card ≤ L.card + 1) (w : ι → Fn R ι α)
    (hw : ∀ i ∈ S, w i ∈ Soc (S.erase i) (S.erase i) L) :
    colSection C S L inf w ∈ Soc S S (insert inf L) ∧
      ∀ j ∈ S, part j inf (colSection C S L inf w) = w j := by
  have hπ : ∀ i ∈ S, IsPartition (piRel (R := R) C (S.card - 1) (S.erase i) L)
      (S.erase i) (S.erase i) L := by
    intro i hi
    refine piRel_spec C _ _ _ _ (Finset.card_erase_of_mem hi).le (subset_refl _) ?_
    rw [Finset.card_erase_of_mem hi]
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have hterm := fun i (hi : i ∈ S) =>
    corr_spec (hπ i hi) (Finset.notMem_erase i S) hinf (hw i hi)
  refine ⟨sum_mem fun i hi => ?_, fun j hj => ?_⟩
  · have h1 := (hterm i hi).1
    rw [Finset.insert_erase hi] at h1
    exact h1
  · rw [colSection, map_sum, Finset.sum_congr rfl fun i hi => (hterm i hi).2 j]
    simp [hj]

/-- **Corollary C.**  For `|L| ≥ 2|S| - 1` and a new label `∞ ∉ L`, `Soc_S(L)` is a summand of
`Soc_S(L ⊔ ∞)`, via a projection commuting with the row permutations preserving `S`. -/
noncomputable def colProj (C : Chooser α) (S : Finset ι) (L : Finset α) (inf : α) :
    Module.End R (Fn R ι α) :=
  1 - ∑ i ∈ S, corr (piRel C (S.card - 1) (S.erase i) L) L i inf * part i inf

theorem colProj_apply (C : Chooser α) (S : Finset ι) (L : Finset α) (inf : α) (y : Fn R ι α) :
    colProj C S L inf y = y - colSection C S L inf (fun i => part i inf y) := by
  rw [colProj, LinearMap.sub_apply, LinearMap.sum_apply]
  rfl

theorem corC (C : Chooser α) (S : Finset ι) (L : Finset α) {inf : α} (hinf : inf ∉ L)
    (hL : 2 * S.card ≤ L.card + 1) :
    (∀ y ∈ Soc S S (insert inf L), colProj (R := R) C S L inf y ∈ Soc S S L) ∧
    (∀ y ∈ Soc S S L, colProj (R := R) C S L inf y = y) ∧
    ∀ σ : Equiv.Perm ι, S.map σ.toEmbedding = S →
      rowAct σ * colProj (R := R) C S L inf = colProj C S L inf * rowAct σ := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun σ hσ => ?_⟩
  · have hw : ∀ i ∈ S, part i inf y ∈ Soc (S.erase i) (S.erase i) L := by
      intro i _
      have := part_mem_Soc hy i inf
      rwa [Finset.erase_insert hinf] at this
    obtain ⟨h1, h2⟩ := colSection_spec C S L hinf hL _ hw
    rw [colProj_apply]
    have hmem := sub_mem hy h1
    have := mem_Soc_erase hmem (d := inf) fun j => by
      by_cases hj : j ∈ S
      · rw [map_sub, h2 j hj, sub_self]
      · rw [part_eq_zero_of_not_mem_S hmem.1 hj]
    rwa [Finset.erase_insert hinf] at this
  · rw [colProj_apply]
    have : (fun i => part i inf y) = fun _ => 0 := funext fun i =>
      part_eq_zero_of_not_mem_L hy.1 i hinf
    rw [this]
    simp [colSection]
  · unfold colProj
    rw [mul_sub, sub_mul, mul_one, one_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    have hS : ∀ i, (S.erase i).map σ.toEmbedding = S.erase (σ i) := fun i => by
      have := Finset.map_erase σ.toEmbedding S i
      simp only [Equiv.toEmbedding_apply] at this
      rw [this, hσ]
    have e : ∀ i ∈ S, rowAct σ * (corr (piRel (R := R) C (S.card - 1) (S.erase i) L) L i inf *
        part i inf) = corr (piRel C (S.card - 1) (S.erase (σ i)) L) L (σ i) inf *
          part (σ i) inf * rowAct σ := by
      intro i _
      rw [← mul_assoc, rowAct_corr σ (π' := piRel C (S.card - 1) (S.erase (σ i)) L)
        (fun x => by rw [piRel_rowAct, hS]), mul_assoc, rowAct_part, ← mul_assoc]
    rw [Finset.sum_congr rfl e]
    have key : ∀ f : ι → Module.End R (Fn R ι α), ∑ x ∈ S, f (σ x) = ∑ x ∈ S, f x := by
      intro f
      have := Finset.sum_map S σ.toEmbedding f
      simp only [Equiv.toEmbedding_apply] at this
      rw [← this, hσ]
    exact key (fun i => corr (piRel C (S.card - 1) (S.erase i) L) L i inf * part i inf *
      rowAct σ)

/-! ### Lemma 3 (cone lemma) -/

/-- Adding one free row `j`: `Ψ ↦ Σ_x (π_x Ψ with x in row j)`. -/
noncomputable def extendRow (C : Chooser α) (m : ℕ) (Rr : Finset ι) (L : Finset α) (j : ι) :
    Module.End R (Fn R ι α) :=
  ∑ x ∈ L, put j x * piRel C m Rr L x

theorem extendRow_spec (C : Chooser α) {m : ℕ} {Rr S : Finset ι} {L : Finset α}
    (hm : S.card ≤ m) (hRS : Rr ⊆ S)
    (hL : Rr.card + S.card + 1 ≤ L.card) {j : ι} (hj : j ∉ S) {Ψ : Fn R ι α}
    (hΨ : Ψ ∈ Soc Rr S L) :
    extendRow C m Rr L j Ψ ∈ Soc Rr (insert j S) L ∧
      del j (extendRow C m Rr L j Ψ) = Ψ := by
  have h := piRel_spec (R := R) C m Rr S L hm hRS hL
  have hjR : j ∉ Rr := fun h' => hj (hRS h')
  have happ : extendRow C m Rr L j Ψ = ∑ x ∈ L, put j x (piRel C m Rr L x Ψ) := by
    rw [extendRow, LinearMap.sum_apply]
    rfl
  rw [happ]
  refine ⟨sum_mem fun x hx => ?_, ?_⟩
  · have := put_mem_Soc (h.1 Ψ hΨ x hx) hjR (Finset.notMem_erase x L)
    rwa [Finset.insert_erase hx] at this
  · rw [map_sum, Finset.sum_congr rfl fun x hx => del_put_self (h.1 Ψ hΨ x hx).1 hj x]
    exact h.2 Ψ hΨ

theorem rowAct_extendRow (C : Chooser α) (σ : Equiv.Perm ι) (m : ℕ) (Rr : Finset ι)
    (L : Finset α) (j : ι) :
    rowAct σ * extendRow (R := R) C m Rr L j =
      extendRow C m (Rr.map σ.toEmbedding) L (σ j) * rowAct σ := by
  unfold extendRow
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_assoc, rowAct_put, mul_assoc, piRel_rowAct, ← mul_assoc]

/-- The cone map: add the free rows of the list `js`, the last one first (`m` is fuel: any
`m ≥ |Rr| + |js|` works). -/
noncomputable def cone (C : Chooser α) (m : ℕ) (Rr : Finset ι) (L : Finset α) :
    List ι → Module.End R (Fn R ι α)
  | [] => 1
  | j :: js => extendRow C m Rr L j * cone C m Rr L js

/-- Deleting the rows of a list. -/
def delList : List ι → Module.End R (Fn R ι α)
  | [] => 1
  | j :: js => delList js * del j

/-- **Lemma 3 (cone lemma).**  For free rows `js` (distinct, outside `Rr`) and
`|L| ≥ 2|Rr| + |js|`, the cone map sends `Soc_Rr(L)` into `Soc_Rr^{js}(L)` and is a section of
the deletion of the rows `js`. -/
theorem cone_spec (C : Chooser α) (m : ℕ) (Rr : Finset ι) (L : Finset α) :
    ∀ (js : List ι), js.Nodup → (∀ j ∈ js, j ∉ Rr) → 2 * Rr.card + js.length ≤ L.card →
      Rr.card + js.length ≤ m →
      ∀ Ψ ∈ Soc Rr Rr L, cone (R := R) C m Rr L js Ψ ∈ Soc Rr (Rr ∪ js.toFinset) L ∧
        delList js (cone (R := R) C m Rr L js Ψ) = Ψ := by
  intro js
  induction js with
  | nil =>
    intro _ _ _ _ Ψ hΨ
    simp only [cone, delList, List.toFinset_nil, Finset.union_empty]
    exact ⟨hΨ, rfl⟩
  | cons j js ih =>
    intro hnd hdisj hL hm Ψ hΨ
    have hnd' := List.nodup_cons.mp hnd
    have hjRr : j ∉ Rr := hdisj j List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih hnd'.2 (fun k hk => hdisj k (List.mem_cons_of_mem j hk))
      (by simp only [List.length_cons] at hL; omega)
      (by simp only [List.length_cons] at hm; omega) Ψ hΨ
    have hdisj' : Disjoint Rr js.toFinset := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      exact hdisj k (List.mem_cons_of_mem j (List.mem_toFinset.mp hk')) hk
    have hcard : (Rr ∪ js.toFinset).card = Rr.card + js.length := by
      rw [Finset.card_union_of_disjoint hdisj', List.toFinset_card_of_nodup hnd'.2]
    have hjS : j ∉ Rr ∪ js.toFinset := by
      rw [Finset.mem_union, not_or]
      exact ⟨hjRr, fun h => hnd'.1 (List.mem_toFinset.mp h)⟩
    have hL' : Rr.card + (Rr ∪ js.toFinset).card + 1 ≤ L.card := by
      rw [hcard]
      simp only [List.length_cons] at hL
      omega
    obtain ⟨h3, h4⟩ := extendRow_spec (R := R) C (m := m)
      (by rw [hcard]; simp only [List.length_cons] at hm; omega)
      Finset.subset_union_left hL' hjS h1
    refine ⟨?_, ?_⟩
    · show extendRow C m Rr L j (cone C m Rr L js Ψ) ∈ _
      have : Rr ∪ (j :: js).toFinset = insert j (Rr ∪ js.toFinset) := by
        rw [List.toFinset_cons, Finset.union_insert]
      rw [this]
      exact h3
    · show delList js (del j (extendRow C m Rr L j (cone C m Rr L js Ψ))) = Ψ
      rw [h4, h2]

theorem rowAct_cone_map (C : Chooser α) (σ : Equiv.Perm ι) (m : ℕ) (Rr : Finset ι)
    (L : Finset α) : ∀ (js : List ι),
      rowAct σ * cone (R := R) C m Rr L js =
        cone C m (Rr.map σ.toEmbedding) L (js.map σ) * rowAct σ := by
  intro js
  induction js with
  | nil => simp [cone]
  | cons j js ih =>
    simp only [cone, List.map_cons]
    rw [← mul_assoc, rowAct_extendRow, mul_assoc, ih, ← mul_assoc]

theorem rowAct_cone (C : Chooser α) (σ : Equiv.Perm ι) (m : ℕ) (Rr : Finset ι) (L : Finset α)
    (hσ : Rr.map σ.toEmbedding = Rr) (js : List ι) (hfix : ∀ j ∈ js, σ j = j) :
    rowAct σ * cone (R := R) C m Rr L js = cone C m Rr L js * rowAct σ := by
  rw [rowAct_cone_map, hσ]
  congr 2
  conv_rhs => rw [← List.map_id js]
  exact List.map_congr_left hfix

end BExact
