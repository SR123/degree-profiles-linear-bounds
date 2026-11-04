/-
Agent B, round 3 (26 Sep 2026).  Proposition 4 of `work/TPRIME_PROOF.md`: the block-rook
filtration of `Soc_b(Lr ⊔ B)` splits over `K S_b`, for `|Lr| ≥ 2b - 1` and any finite `B`.

Rows `ι` (all present: `Soc univ univ`), retained labels `Lr`, block labels `B` (disjoint).
`nb B t` = number of rows of `t` carrying a block label.
* `Filt Lr B k`  : cycles on `Lr ∪ B` supported on tuples with at most `k` block rows (`Soc^{≤k}`).
* `topPart B k`  : restriction to tuples with exactly `k` block rows.
* `Gr Lr B k`    : functions on `Lr ∪ B`, supported on tuples with exactly `k` block rows, whose
                   RETAINED marginals `Σ_{x ∈ Lr} part i x` vanish (`gr_k` of the paper).
Results:
* `topPart_mem_Gr` (Prop. 4(a)): `topPart k` maps `Filt k` into `Gr k`, with kernel `Filt (k-1)`
  (`mem_Filt_pred`).
* `blockSection_spec` (Prop. 4(b)): for `1 ≤ k` and `2|ι| ≤ |Lr| + 1`, the explicit map
  `blockSection` sends `Gr k` into `Filt k` and `topPart k ∘ blockSection = id` on `Gr k`.
* `rowAct_blockSection`: `blockSection` commutes with every row permutation.

The section is the paper's `s_β` summed over block patterns: for a pattern `pat` (rows `D`, block
labels `β`), `y = partL pat g ∈ Soc_{D^c}(Lr)`, `Φ = cone(y)` (Lemma 3, rows of `D` added in the
order of their labels in the enumeration `Bl` of `B`, which makes the sum equivariant), and
`s = Π_{i ∈ D} (put i (β i) ∘ del i - 1) Φ`.
-/
import BLemmaD
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
  {α : Type} [Fintype α] [DecidableEq α]

/-! ### Multi-row operators -/

/-- Take the `x`-parts in the rows of a list of (row, label) pairs. -/
def partL : List (ι × α) → Module.End R (Fn R ι α)
  | [] => 1
  | p :: ps => partL ps * part p.1 p.2

/-- Insert the labels of a list of (row, label) pairs. -/
def putL : List (ι × α) → Module.End R (Fn R ι α)
  | [] => 1
  | p :: ps => put p.1 p.2 * putL ps

/-- `Π (put i x ∘ del i - 1)`. -/
def Tl : List (ι × α) → Module.End R (Fn R ι α)
  | [] => 1
  | p :: ps => (put p.1 p.2 * del p.1 - 1) * Tl ps

/-- Fill in the pairs of a list. -/
def fillL : List (ι × α) → (ι → Option α) → (ι → Option α)
  | [], t => t
  | p :: ps, t => update (fillL ps t) p.1 (some p.2)

theorem fillL_of_not_mem (ps : List (ι × α)) (t : ι → Option α) {j : ι}
    (hj : j ∉ ps.map Prod.fst) : fillL ps t j = t j := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hj
    simp only [fillL]
    rw [update_of_ne hj.1, ih hj.2]

theorem fillL_of_mem (ps : List (ι × α)) (hnd : (ps.map Prod.fst).Nodup) (t : ι → Option α)
    {p : ι × α} (hp : p ∈ ps) : fillL ps t p.1 = some p.2 := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [fillL]
    rcases List.mem_cons.mp hp with h | h
    · subst h
      exact update_self _ _ _
    · have hne : p.1 ≠ q.1 := by
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem h)
      rw [update_of_ne hne, ih hnd.2 h]

theorem fillL_update (ps : List (ι × α)) (t : ι → Option α) {j : ι}
    (hj : j ∉ ps.map Prod.fst) (v : Option α) :
    fillL ps (update t j v) = update (fillL ps t) j v := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hj
    simp only [fillL]
    rw [ih hj.2, update_comm (Ne.symm hj.1)]

theorem partL_apply (ps : List (ι × α)) (hnd : (ps.map Prod.fst).Nodup) (g : Fn R ι α)
    (t : ι → Option α) :
    partL ps g t = if (∀ p ∈ ps, t p.1 = none) then g (fillL ps t) else 0 := by
  induction ps generalizing g with
  | nil => simp [partL, fillL]
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [partL, Module.End.mul_apply]
    rw [ih hnd.2, part_apply, fillL_of_not_mem ps t hnd.1]
    simp only [List.mem_cons, forall_eq_or_imp, fillL]
    by_cases h1 : t p.1 = none <;> simp [h1]

theorem putL_partL_apply (ps : List (ι × α)) (hnd : (ps.map Prod.fst).Nodup) (g : Fn R ι α)
    (t : ι → Option α) :
    putL ps (partL ps g) t = if (∀ p ∈ ps, t p.1 = some p.2) then g t else 0 := by
  induction ps generalizing g t with
  | nil => simp [putL, partL]
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [putL, partL, Module.End.mul_apply]
    rw [put_apply]
    simp only [List.mem_cons, forall_eq_or_imp]
    by_cases h1 : t p.1 = some p.2
    · rw [if_pos h1, ih hnd.2]
      have hupd : ∀ q ∈ ps, update t p.1 none q.1 = t q.1 := by
        intro q hq
        have : q.1 ≠ p.1 := fun he => hnd.1 (he ▸ List.mem_map_of_mem hq)
        exact update_of_ne this _ _
      have hpart : part p.1 p.2 g (update t p.1 none) = g t := by
        rw [part_apply, if_pos (update_self _ _ _), update_idem, ← h1, update_eq_self]
      rw [hpart]
      simp only [h1, true_and]
      by_cases h2 : ∀ q ∈ ps, t q.1 = some q.2
      · rw [if_pos h2, if_pos (fun q hq => (hupd q hq).trans (h2 q hq))]
      · rw [if_neg h2, if_neg (fun h => h2 (fun q hq => (hupd q hq).symm.trans (h q hq)))]
    · rw [if_neg h1]
      simp [h1]

/-! ### The block-rook filtration -/

/-- Rows carrying a block label. -/
def blockRows (B : Finset α) (t : ι → Option α) : Finset ι :=
  univ.filter (fun i => ∃ x ∈ B, t i = some x)

/-- Number of rows carrying a block label. -/
def nb (B : Finset α) (t : ι → Option α) : ℕ := (blockRows B t).card

theorem mem_blockRows {B : Finset α} {t : ι → Option α} {i : ι} :
    i ∈ blockRows B t ↔ ∃ x ∈ B, t i = some x := by
  simp [blockRows]

theorem blockRows_update_retained {B : Finset α} {t : ι → Option α} {i : ι} (hi : t i = none)
    {x : α} (hx : x ∉ B) : blockRows B (update t i (some x)) = blockRows B t := by
  ext j
  rw [mem_blockRows, mem_blockRows]
  by_cases hj : j = i
  · subst hj
    rw [update_self, hi]
    constructor
    · rintro ⟨y, hy, h⟩
      cases h
      exact absurd hy hx
    · rintro ⟨y, _, h⟩
      cases h
  · rw [update_of_ne hj]

theorem blockRows_update_block {B : Finset α} {t : ι → Option α} {i : ι} (hi : t i = none)
    {x : α} (hx : x ∈ B) : blockRows B (update t i (some x)) = insert i (blockRows B t) := by
  ext j
  rw [Finset.mem_insert, mem_blockRows, mem_blockRows]
  by_cases hj : j = i
  · subst hj
    rw [update_self]
    simp only [true_or, iff_true]
    exact ⟨x, hx, rfl⟩
  · rw [update_of_ne hj]
    simp [hj]

theorem not_mem_blockRows_of_none {B : Finset α} {t : ι → Option α} {i : ι} (hi : t i = none) :
    i ∉ blockRows B t := by
  rw [mem_blockRows]
  rintro ⟨x, _, h⟩
  rw [hi] at h
  cases h

/-- `Soc^{≤k}`: cycles on `Lr ∪ B` with at most `k` block rows. -/
def Filt (Lr B : Finset α) (k : ℕ) : Submodule R (Fn R ι α) where
  carrier := {f | f ∈ Soc univ univ (Lr ∪ B) ∧ ∀ t, k < nb B t → f t = 0}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun t ht => by
    show f t + g t = 0
    rw [hf.2 t ht, hg.2 t ht, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c f hf := ⟨(Soc univ univ (Lr ∪ B)).smul_mem c hf.1, fun t ht => by
    show c * f t = 0
    rw [hf.2 t ht, mul_zero]⟩

/-- Restriction to the tuples with exactly `k` block rows. -/
def topPart (B : Finset α) (k : ℕ) : Module.End R (Fn R ι α) where
  toFun f t := if nb B t = k then f t else 0
  map_add' f g := by
    funext t
    by_cases h : nb B t = k <;> simp [h]
  map_smul' c f := by
    funext t
    by_cases h : nb B t = k <;> simp [h]

theorem topPart_apply (B : Finset α) (k : ℕ) (f : Fn R ι α) (t : ι → Option α) :
    topPart B k f t = if nb B t = k then f t else 0 := rfl

/-- The retained marginal. -/
def delRet (Lr : Finset α) (i : ι) : Module.End R (Fn R ι α) := ∑ x ∈ Lr, part i x

theorem delRet_apply (Lr : Finset α) (i : ι) (g : Fn R ι α) (t : ι → Option α) :
    delRet Lr i g t = ∑ x ∈ Lr, part i x g t := by
  rw [delRet, LinearMap.sum_apply, Finset.sum_apply]

/-- `gr_k`: functions with exactly `k` block rows whose retained marginals vanish. -/
def Gr (Lr B : Finset α) (k : ℕ) : Submodule R (Fn R ι α) where
  carrier := {g | g ∈ P univ (Lr ∪ B) ∧ (∀ t, nb B t ≠ k → g t = 0) ∧ ∀ i, delRet Lr i g = 0}
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, fun t ht => by
    show f t + g t = 0
    rw [hf.2.1 t ht, hg.2.1 t ht, add_zero], fun i => by
    rw [map_add, hf.2.2 i, hg.2.2 i, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl, fun _ => map_zero _⟩
  smul_mem' c f hf := ⟨(P univ (Lr ∪ B)).smul_mem c hf.1, fun t ht => by
    show c * f t = 0
    rw [hf.2.1 t ht, mul_zero], fun i => by rw [map_smul, hf.2.2 i, smul_zero]⟩

theorem sum_retained_eq_del {Lr B : Finset α} {k : ℕ} {f : Fn R ι α}
    (hf : f ∈ P univ (Lr ∪ B)) {t : ι → Option α}
    (hti : ∀ i, t i = none → nb B t = k → ∀ x ∈ B, f (update t i (some x)) = 0)
    (i : ι) (hi : t i = none) (htk : nb B t = k) :
    ∑ x ∈ Lr, f (update t i (some x)) = ∑ x, f (update t i (some x)) := by
  rw [← Finset.sum_subset (Finset.subset_univ Lr)]
  intro x _ hx
  by_cases hxB : x ∈ B
  · exact hti i hi htk x hxB
  · by_contra h0
    have := (hf _ h0).val i x (update_self _ _ _)
    rcases Finset.mem_union.mp this with h | h
    · exact hx h
    · exact hxB h

/-- **Prop. 4(a).**  `topPart k` maps `Soc^{≤k}` into `gr_k`. -/
theorem topPart_mem_Gr {Lr B : Finset α} (hLB : Disjoint Lr B) {k : ℕ} {f : Fn R ι α}
    (hf : f ∈ Filt Lr B k) : topPart B k f ∈ Gr Lr B k := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun i => ?_⟩
  · rw [topPart_apply] at ht
    split_ifs at ht
    · exact hf.1.1 t ht
    · exact absurd rfl ht
  · rw [topPart_apply, if_neg ht]
  · funext t
    rw [delRet_apply]
    simp only [part_apply, topPart_apply]
    by_cases hi : t i = none
    · simp only [hi, if_true]
      have hnb : ∀ x ∈ Lr, nb B (update t i (some x)) = nb B t := fun x hx => by
        unfold nb
        rw [blockRows_update_retained hi (Finset.disjoint_left.mp hLB hx)]
      rw [Finset.sum_congr rfl fun x hx => by rw [hnb x hx]]
      by_cases htk : nb B t = k
      · simp only [htk, if_true]
        rw [sum_retained_eq_del hf.1.1 (fun i' hi' htk' x hxB => hf.2 _ (by
          unfold nb
          rw [blockRows_update_block hi' hxB, Finset.card_insert_of_notMem
            (not_mem_blockRows_of_none hi')]
          unfold nb at htk'
          omega)) i hi htk]
        have h := congrFun (hf.1.2 i (mem_univ i)) t
        rw [del_apply] at h
        simp only [part_apply, hi, if_true] at h
        exact h
      · simp [htk]
    · simp [hi]

/-- The kernel of `topPart k` on `Soc^{≤k}` is `Soc^{≤k-1}`. -/
theorem mem_Filt_pred {Lr B : Finset α} {k : ℕ} {f : Fn R ι α} (hf : f ∈ Filt Lr B k)
    (h0 : topPart B k f = 0) : f ∈ Filt Lr B (k - 1) := by
  refine ⟨hf.1, fun t ht => ?_⟩
  by_cases htk : nb B t = k
  · have := congrFun h0 t
    rwa [topPart_apply, if_pos htk] at this
  · exact hf.2 t (by omega)

/-! ### Block patterns -/

/-- The rows of a partial tuple. -/
def patDom (pat : ι → Option α) : Finset ι := univ.filter (fun i => pat i ≠ none)

/-- A block pattern with `k` rows: an injective partial tuple with labels in `B`. -/
def IsPat (B : Finset α) (k : ℕ) (pat : ι → Option α) : Prop :=
  (∀ i x, pat i = some x → x ∈ B) ∧ (∀ i j x, pat i = some x → pat j = some x → i = j) ∧
    (patDom pat).card = k

instance (B : Finset α) (k : ℕ) : DecidablePred (IsPat (ι := ι) B k) := fun pat => by
  unfold IsPat
  infer_instance

/-- The row carrying label `x`, if any. -/
noncomputable def rowOf (pat : ι → Option α) (x : α) : Option ι :=
  if h : ∃ i, pat i = some x then some h.choose else none

theorem rowOf_eq_some {pat : ι → Option α}
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j) (x : α) (i : ι) :
    rowOf pat x = some i ↔ pat i = some x := by
  unfold rowOf
  constructor
  · intro h
    split_ifs at h with hex
    · cases h
      exact hex.choose_spec
  · intro h
    have hex : ∃ i, pat i = some x := ⟨i, h⟩
    rw [dif_pos hex, hinj _ _ _ hex.choose_spec h]

/-- The (row, label) pairs of a pattern, in the order of the label list `Bl`. -/
noncomputable def pairs (Bl : List α) (pat : ι → Option α) : List (ι × α) :=
  Bl.filterMap (fun x => (rowOf pat x).map (fun i => (i, x)))

theorem mem_pairs {Bl : List α} {pat : ι → Option α}
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j)
    (hB : ∀ i x, pat i = some x → x ∈ Bl) (p : ι × α) :
    p ∈ pairs Bl pat ↔ pat p.1 = some p.2 := by
  unfold pairs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, _, hx⟩
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact (rowOf_eq_some hinj x i).mp hi
  · intro h
    refine ⟨p.2, hB _ _ h, ?_⟩
    rw [(rowOf_eq_some hinj p.2 p.1).mpr h]
    rfl

theorem pairs_nodup {Bl : List α} (hBl : Bl.Nodup) (pat : ι → Option α) :
    (pairs Bl pat).Nodup := by
  unfold pairs
  refine hBl.filterMap fun a a' b ha ha' => ?_
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨i', _, h⟩ := Option.map_eq_some_iff.mp ha'
  exact (congrArg Prod.snd h).symm

theorem pairs_fst_nodup {Bl : List α} (hBl : Bl.Nodup) {pat : ι → Option α}
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j)
    (hB : ∀ i x, pat i = some x → x ∈ Bl) : ((pairs Bl pat).map Prod.fst).Nodup := by
  refine (pairs_nodup hBl pat).map_on fun p hp q hq hpq => ?_
  have h1 := (mem_pairs hinj hB p).mp hp
  have h2 := (mem_pairs hinj hB q).mp hq
  rw [hpq] at h1
  rw [h1] at h2
  exact Prod.ext hpq (Option.some.inj h2)

theorem pairs_snd_nodup {Bl : List α} (hBl : Bl.Nodup) (pat : ι → Option α) :
    ((pairs Bl pat).map Prod.snd).Nodup := by
  unfold pairs
  rw [List.map_filterMap]
  refine hBl.filterMap fun a a' b ha ha' => ?_
  rw [Option.map_map] at ha ha'
  obtain ⟨i, _, h1⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨i', _, h2⟩ := Option.map_eq_some_iff.mp ha'
  have e1 : a = b := h1
  have e2 : a' = b := h2
  exact e1.trans e2.symm

theorem mem_pairs_fst {Bl : List α} {pat : ι → Option α}
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j)
    (hB : ∀ i x, pat i = some x → x ∈ Bl) (i : ι) :
    i ∈ (pairs Bl pat).map Prod.fst ↔ i ∈ patDom pat := by
  rw [List.mem_map]
  simp only [patDom, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [(mem_pairs hinj hB p).mp hp]
    simp
  · intro h
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨(i, x), (mem_pairs hinj hB (i, x)).mpr hx, rfl⟩

theorem pairs_length {Bl : List α} (hBl : Bl.Nodup) {B : Finset α} (hBB : Bl.toFinset = B)
    {k : ℕ} {pat : ι → Option α} (hpat : IsPat B k pat) : (pairs Bl pat).length = k := by
  have hB : ∀ i x, pat i = some x → x ∈ Bl := fun i x h => by
    rw [← List.mem_toFinset, hBB]
    exact hpat.1 i x h
  have hnd := pairs_fst_nodup hBl hpat.2.1 hB
  have := List.toFinset_card_of_nodup hnd
  rw [List.length_map] at this
  rw [← this, ← hpat.2.2]
  congr 1
  ext i
  rw [List.mem_toFinset]
  exact mem_pairs_fst hpat.2.1 hB i

theorem rowOf_comp {pat : ι → Option α}
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j) (σ : Equiv.Perm ι) (x : α) :
    rowOf (pat ∘ σ.symm) x = (rowOf pat x).map σ := by
  have hinj' : ∀ i j x, (pat ∘ σ.symm) i = some x → (pat ∘ σ.symm) j = some x → i = j :=
    fun i j x hi hj => σ.symm.injective (hinj _ _ x hi hj)
  apply Option.ext
  intro i
  rw [rowOf_eq_some hinj' x i, Option.map_eq_some_iff]
  constructor
  · intro h
    exact ⟨σ.symm i, (rowOf_eq_some hinj x _).mpr h, σ.apply_symm_apply i⟩
  · rintro ⟨j, hj, rfl⟩
    rw [comp_apply, σ.symm_apply_apply]
    exact (rowOf_eq_some hinj x j).mp hj

theorem pairs_comp {Bl : List α} {pat : ι → Option α}
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j) (σ : Equiv.Perm ι) :
    pairs Bl (pat ∘ σ.symm) = (pairs Bl pat).map (Prod.map σ id) := by
  unfold pairs
  rw [List.map_filterMap]
  congr 1
  funext x
  rw [rowOf_comp hinj σ x, Option.map_map, Option.map_map]
  rfl

/-! ### The product `Π (put i x ∘ del i - 1)` -/

theorem del_mem_P {S : Finset ι} {L : Finset α} {f : Fn R ι α} (hf : f ∈ P S L) (i : ι) :
    del i f ∈ P (S.erase i) L := by
  rw [del, LinearMap.sum_apply]
  exact sum_mem fun x _ => P_mono (Finset.erase_subset x L) (part_mem_P hf i x)

theorem delList_del_comm (i : ι) :
    ∀ js : List ι, del i * delList js = (delList js * del i : Module.End R (Fn R ι α)) := by
  intro js
  induction js with
  | nil => simp [delList]
  | cons j js ih =>
    simp only [delList]
    rw [← mul_assoc, ih, mul_assoc, del_comm i j, ← mul_assoc]

theorem partL_del_comm (i : ι) :
    ∀ ps : List (ι × α), i ∉ ps.map Prod.fst →
      partL ps * del i = (del i * partL ps : Module.End R (Fn R ι α)) := by
  intro ps
  induction ps with
  | nil => intro _; simp [partL]
  | cons p ps ih =>
    intro hi
    simp only [List.map_cons, List.mem_cons, not_or] at hi
    simp only [partL]
    rw [mul_assoc, ← del_part_comm hi.1 p.2, ← mul_assoc, ih hi.2, mul_assoc]

/-- Every non-retained label of `t` sits at one of the pairs. -/
def Compat (Lr : Finset α) (ps : List (ι × α)) (t : ι → Option α) : Prop :=
  ∀ j y, t j = some y → y ∉ Lr → (j, y) ∈ ps

theorem Tl_spec {Lr : Finset α} {Rr : Finset ι} :
    ∀ (ps : List (ι × α)), (ps.map Prod.fst).Nodup → (ps.map Prod.snd).Nodup →
      (∀ p ∈ ps, p.1 ∉ Rr) → (∀ p ∈ ps, p.2 ∉ Lr) → ∀ h ∈ Soc Rr univ Lr,
      Tl ps h ∈ Soc (Rr ∪ (ps.map Prod.fst).toFinset) univ
          (Lr ∪ (ps.map Prod.snd).toFinset) ∧
        (∀ t, (Tl ps h : Fn R ι α) t ≠ 0 → Compat Lr ps t) ∧
        partL ps (Tl ps h) = delList (ps.map Prod.fst) h := by
  intro ps
  induction ps with
  | nil =>
    intro _ _ _ _ h hh
    simp only [Tl, List.map_nil, List.toFinset_nil, Finset.union_empty, Module.End.one_apply,
      partL, delList]
    refine ⟨hh, fun t ht j y hy hyL => absurd ((hh.1 t ht).val j y hy) hyL, ?_⟩
    first | rfl | trivial
  | cons p ps ih =>
    intro hnd1 hnd2 hR hL h hh
    simp only [List.map_cons, List.nodup_cons] at hnd1 hnd2
    obtain ⟨i, x⟩ := p
    simp only at hnd1 hnd2
    have hiR : i ∉ Rr := hR (i, x) List.mem_cons_self
    have hxL : x ∉ Lr := hL (i, x) List.mem_cons_self
    obtain ⟨ha, hb, hc⟩ := ih hnd1.2 hnd2.2 (fun q hq => hR q (List.mem_cons_of_mem _ hq))
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) h hh
    set h' := Tl ps h with hh'
    have hTl : Tl ((i, x) :: ps) h = put i x (del i h') - h' := by
      simp only [Tl, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      rfl
    have hxL' : x ∉ Lr ∪ (ps.map Prod.snd).toFinset := by
      rw [Finset.mem_union, not_or, List.mem_toFinset]
      exact ⟨hxL, hnd2.1⟩
    have hdel : del i h' ∈ P (univ.erase i) (Lr ∪ (ps.map Prod.snd).toFinset) :=
      del_mem_P ha.1 i
    have hput : del i (put i x (del i h')) = del i h' :=
      del_put_self hdel (Finset.notMem_erase i univ) x
    refine ⟨⟨?_, fun j hj => ?_⟩, fun t ht => ?_, ?_⟩
    · rw [hTl]
      have h1 := put_mem_P hdel i hxL'
      rw [Finset.insert_erase (mem_univ i)] at h1
      have h2 := P_mono (Finset.subset_insert x _) ha.1
      have e : insert x (Lr ∪ (ps.map Prod.snd).toFinset) =
          Lr ∪ ((x :: ps.map Prod.snd).toFinset) := by
        rw [List.toFinset_cons, Finset.union_insert]
      rw [e] at h1 h2
      exact sub_mem h1 h2
    · rw [hTl, map_sub]
      by_cases hji : j = i
      · subst hji
        rw [hput, sub_self]
      · have hj' : j ∈ Rr ∪ (ps.map Prod.fst).toFinset := by
          simp only [List.map_cons, List.toFinset_cons, Finset.mem_union,
            Finset.mem_insert] at hj
          rw [Finset.mem_union]
          rcases hj with h1 | h1 | h1
          · exact Or.inl h1
          · exact absurd h1 hji
          · exact Or.inr h1
        rw [← Module.End.mul_apply, del_put_comm hji, Module.End.mul_apply,
          ← Module.End.mul_apply (del j), del_comm j i, Module.End.mul_apply, ha.2 j hj',
          map_zero, map_zero, sub_zero]
    · rw [hTl] at ht
      intro j y hy hyL
      by_cases h0 : h' t = 0
      · rw [Pi.sub_apply, h0, sub_zero, put_apply] at ht
        by_cases hti : t i = some x
        swap
        · rw [if_neg hti] at ht
          exact absurd rfl ht
        rw [if_pos hti, del_apply] at ht
        obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
        rw [part_apply, if_pos (update_self _ _ _), update_idem] at hz
        by_cases hji : j = i
        · subst hji
          rw [hti] at hy
          cases hy
          exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ (hb _ hz j y ?_ hyL)
          rw [update_of_ne hji]
          exact hy
      · exact List.mem_cons_of_mem _ (hb t h0 j y hy hyL)
    · have hpart0 : part i x h' = 0 := by
        funext t
        rw [part_apply]
        split_ifs with hti
        · by_contra hne
          have := hb _ hne i x (update_self _ _ _) hxL
          exact hnd1.1 (List.mem_map_of_mem (f := Prod.fst) this)
        · rfl
      have hpp : part i x (put i x (del i h')) = del i h' :=
        part_put_same hdel (Finset.notMem_erase i univ) x
      simp only [List.map_cons, delList, partL, Module.End.mul_apply]
      rw [hTl, map_sub, hpp, hpart0, sub_zero, ← Module.End.mul_apply,
        partL_del_comm i ps hnd1.1, Module.End.mul_apply, hc, ← Module.End.mul_apply,
        delList_del_comm, Module.End.mul_apply]

/-! ### The section of Prop. 4(b) -/

theorem compl_union_self' (s : Finset ι) : sᶜ ∪ s = univ := by
  rw [Finset.union_comm, Finset.union_compl]

/-- The piece of the section attached to one block pattern. -/
noncomputable def piece (C : Chooser α) (Lr : Finset α) (Bl : List α) (pat : ι → Option α) :
    Module.End R (Fn R ι α) :=
  Tl (pairs Bl pat) * cone C (Fintype.card ι) (patDom pat)ᶜ Lr ((pairs Bl pat).map Prod.fst) *
    partL (pairs Bl pat)

/-- The section `gr_k → Soc^{≤k}` of Prop. 4(b). -/
noncomputable def blockSection (C : Chooser α) (Lr : Finset α) (Bl : List α) (k : ℕ) :
    Module.End R (Fn R ι α) :=
  ∑ pat ∈ univ.filter (IsPat Bl.toFinset k), piece C Lr Bl pat

theorem patDom_subset_blockRows {B : Finset α} {Bl : List α} {pat : ι → Option α}
    (hB : ∀ i x, pat i = some x → x ∈ B)
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j)
    (hBl : ∀ i x, pat i = some x → x ∈ Bl) {s : ι → Option α}
    (hs : ∀ p ∈ pairs Bl pat, s p.1 = some p.2) : patDom pat ⊆ blockRows B s := by
  intro j hj
  simp only [patDom, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hj
  rw [mem_blockRows]
  exact ⟨x, hB j x hx, hs (j, x) ((mem_pairs hinj hBl (j, x)).mpr hx)⟩

/-- The slice of `g ∈ gr_k` at a pattern is a cycle on the retained labels. -/
theorem slice_mem {Lr : Finset α} {Bl : List α} (hBl : Bl.Nodup) {k : ℕ} {g : Fn R ι α}
    (hg : g ∈ Gr Lr Bl.toFinset k) {pat : ι → Option α} (hpat : IsPat Bl.toFinset k pat) :
    partL (pairs Bl pat) g ∈ Soc (patDom pat)ᶜ (patDom pat)ᶜ Lr := by
  set B := Bl.toFinset
  set ps := pairs Bl pat with hps
  have hBl' : ∀ i x, pat i = some x → x ∈ Bl := fun i x h =>
    List.mem_toFinset.mp (hpat.1 i x h)
  have hnd := pairs_fst_nodup hBl hpat.2.1 hBl'
  have hmemD : ∀ j, j ∈ ps.map Prod.fst ↔ j ∈ patDom pat := mem_pairs_fst hpat.2.1 hBl'
  have hfill : ∀ t, ∀ p ∈ ps, fillL ps t p.1 = some p.2 := fun t p hp => fillL_of_mem ps hnd t hp
  have hsub : ∀ s : ι → Option α, (∀ p ∈ ps, s p.1 = some p.2) → patDom pat ⊆ blockRows B s :=
    fun s hs => patDom_subset_blockRows hpat.1 hpat.2.1 hBl' hs
  -- a tuple containing the pattern and one more block row has too many block rows
  have hbig : ∀ s : ι → Option α, (∀ p ∈ ps, s p.1 = some p.2) → ∀ j, j ∉ patDom pat →
      j ∈ blockRows B s → k < nb B s := by
    intro s hs j hj hjB
    have h1 : insert j (patDom pat) ⊆ blockRows B s :=
      Finset.insert_subset hjB (hsub s hs)
    have h2 := Finset.card_le_card h1
    rw [Finset.card_insert_of_notMem hj, hpat.2.2] at h2
    unfold nb
    omega
  refine ⟨fun t ht => ?_, fun i hi => ?_⟩
  · rw [partL_apply ps hnd] at ht
    by_cases hnone : ∀ p ∈ ps, t p.1 = none
    swap
    · rw [if_neg hnone] at ht
      exact absurd rfl ht
    rw [if_pos hnone] at ht
    have G := hg.1 _ ht
    have hk : nb B (fillL ps t) = k := by
      by_contra h
      exact ht (hg.2.1 _ h)
    have hfj : ∀ j, j ∉ patDom pat → fillL ps t j = t j := fun j hj =>
      fillL_of_not_mem ps t (fun h => hj ((hmemD j).mp h))
    have htD : ∀ j, j ∈ patDom pat → t j = none := fun j hj => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((hmemD j).mpr hj)
      exact hnone p hp
    refine ⟨fun j => ?_, fun j y hy => ?_, fun j j' y hj hj' => ?_⟩
    · rw [Finset.mem_compl]
      by_cases hj : j ∈ patDom pat
      · simp [hj, htD j hj]
      · simp only [hj, not_false_eq_true, iff_true]
        rw [← hfj j hj]
        exact (G.dom j).mpr (mem_univ j)
    · have hj : j ∉ patDom pat := fun h => by rw [htD j h] at hy; cases hy
      have hy' : fillL ps t j = some y := by rw [hfj j hj]; exact hy
      rcases Finset.mem_union.mp (G.val j y hy') with h | h
      · exact h
      · exfalso
        have := hbig _ (hfill t) j hj (mem_blockRows.mpr ⟨y, h, hy'⟩)
        omega
    · have hj1 : j ∉ patDom pat := fun h => by rw [htD j h] at hj; cases hj
      have hj2 : j' ∉ patDom pat := fun h => by rw [htD j' h] at hj'; cases hj'
      exact G.inj j j' y (by rw [hfj j hj1]; exact hj) (by rw [hfj j' hj2]; exact hj')
  · have hiD : i ∉ patDom pat := Finset.mem_compl.mp hi
    have hips : i ∉ ps.map Prod.fst := fun h => hiD ((hmemD i).mp h)
    rw [← Module.End.mul_apply, ← partL_del_comm i ps hips]
    funext t
    rw [Module.End.mul_apply, partL_apply ps hnd]
    split_ifs with hnone
    · set s := fillL ps t
      have hsi : s i = t i := fillL_of_not_mem ps t hips
      rw [del_apply]
      simp only [part_apply]
      by_cases hti : s i = none
      · simp only [hti, if_true]
        have hret := congrFun (hg.2.2 i) s
        rw [delRet_apply] at hret
        simp only [part_apply, hti, if_true] at hret
        rw [← Finset.sum_subset (Finset.subset_univ Lr)]
        · exact hret
        · intro x _ hx
          by_contra h0
          have G := hg.1 _ h0
          have hk : nb B (update s i (some x)) = k := by
            by_contra h
            exact h0 (hg.2.1 _ h)
          rcases Finset.mem_union.mp (G.val i x (update_self _ _ _)) with h | h
          · exact hx h
          · have hs' : ∀ p ∈ ps, update s i (some x) p.1 = some p.2 := by
              intro p hp
              have : p.1 ≠ i := fun he => hips (he ▸ List.mem_map_of_mem hp)
              rw [update_of_ne this]
              exact hfill t p hp
            have := hbig _ hs' i hiD (mem_blockRows.mpr ⟨x, h, update_self _ _ _⟩)
            omega
      · simp [hti]
    · rfl

theorem piece_apply (C : Chooser α) (Lr : Finset α) (Bl : List α) (pat : ι → Option α)
    (g : Fn R ι α) :
    piece C Lr Bl pat g = Tl (pairs Bl pat) (cone C (Fintype.card ι) (patDom pat)ᶜ Lr
      ((pairs Bl pat).map Prod.fst) (partL (pairs Bl pat) g)) := rfl

/-- One piece lies in `Soc^{≤k}` and its top part is the slice put back. -/
theorem piece_spec (C : Chooser α) {Lr : Finset α} {Bl : List α} (hBl : Bl.Nodup)
    (hLB : Disjoint Lr Bl.toFinset) {k : ℕ} (hk : 1 ≤ k)
    (hL : 2 * Fintype.card ι ≤ Lr.card + 1) {g : Fn R ι α} (hg : g ∈ Gr Lr Bl.toFinset k)
    {pat : ι → Option α} (hpat : IsPat Bl.toFinset k pat) :
    piece C Lr Bl pat g ∈ Filt Lr Bl.toFinset k ∧
      topPart Bl.toFinset k (piece C Lr Bl pat g) =
        putL (pairs Bl pat) (partL (pairs Bl pat) g) := by
  set B := Bl.toFinset
  set ps := pairs Bl pat with hps
  set D := patDom pat
  have hBl' : ∀ i x, pat i = some x → x ∈ Bl := fun i x h =>
    List.mem_toFinset.mp (hpat.1 i x h)
  have hnd := pairs_fst_nodup hBl hpat.2.1 hBl'
  have hnd2 := pairs_snd_nodup hBl pat
  have hmemD : ∀ j, j ∈ ps.map Prod.fst ↔ j ∈ D := mem_pairs_fst hpat.2.1 hBl'
  have hlen : ps.length = k := pairs_length hBl rfl hpat
  have hpsB : ∀ p ∈ ps, p.2 ∈ B := fun p hp => hpat.1 p.1 p.2 ((mem_pairs hpat.2.1 hBl' p).mp hp)
  have hy := slice_mem hBl hg hpat
  have hDc : Dᶜ.card = Fintype.card ι - k := by
    rw [Finset.card_compl, hpat.2.2]
  have hkι : k ≤ Fintype.card ι := by
    rw [← hpat.2.2]
    exact Finset.card_le_univ _
  have hjs : (ps.map Prod.fst).toFinset = D := by
    ext j
    rw [List.mem_toFinset]
    exact hmemD j
  obtain ⟨hΦ, hΦdel⟩ := cone_spec (R := R) C (Fintype.card ι) Dᶜ Lr (ps.map Prod.fst) hnd
    (fun j hj => by rw [Finset.mem_compl, not_not]; exact (hmemD j).mp hj)
    (by rw [List.length_map, hlen, hDc]; omega) (by rw [List.length_map, hlen, hDc]; omega)
    _ hy
  rw [hjs, compl_union_self'] at hΦ
  set Φ := cone C (Fintype.card ι) Dᶜ Lr (ps.map Prod.fst) (partL ps g)
  obtain ⟨ha, hb, hc⟩ := Tl_spec (R := R) ps hnd hnd2
    (fun p hp => by rw [Finset.mem_compl, not_not]; exact (hmemD p.1).mp (List.mem_map_of_mem hp))
    (fun p hp => Finset.disjoint_right.mp hLB (hpsB p hp)) Φ hΦ
  rw [hjs, compl_union_self'] at ha
  have hlabs : Lr ∪ (ps.map Prod.snd).toFinset ⊆ Lr ∪ B := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      exact Finset.mem_union_right _ (hpsB p hp)
  have hpiece : piece C Lr Bl pat g = Tl ps Φ := rfl
  -- block rows of the support lie in `D`
  have hbr : ∀ t, Tl ps Φ t ≠ 0 → blockRows B t ⊆ D := by
    intro t ht j hj
    obtain ⟨y, hyB, hy⟩ := mem_blockRows.mp hj
    have := hb t ht j y hy (Finset.disjoint_right.mp hLB hyB)
    exact (hmemD j).mp (List.mem_map_of_mem (f := Prod.fst) this)
  rw [hpiece]
  refine ⟨⟨Soc_mono hlabs ha, fun t ht => ?_⟩, ?_⟩
  · by_contra h0
    have := Finset.card_le_card (hbr t h0)
    rw [hpat.2.2] at this
    unfold nb at ht
    omega
  · have e : partL ps g = partL ps (Tl ps Φ) := by rw [hc]; exact hΦdel.symm
    rw [e]
    funext t
    rw [topPart_apply, putL_partL_apply ps hnd]
    by_cases h0 : Tl ps Φ t = 0
    · simp [h0]
    · have hsub := hbr t h0
      by_cases hall : ∀ p ∈ ps, t p.1 = some p.2
      · have hD : D ⊆ blockRows B t :=
          patDom_subset_blockRows hpat.1 hpat.2.1 hBl' hall
        have : nb B t = k := by
          unfold nb
          rw [Finset.Subset.antisymm hsub hD, hpat.2.2]
        rw [if_pos this, if_pos hall]
      · rw [if_neg hall, if_neg]
        intro hnbk
        apply hall
        intro p hp
        have heq : blockRows B t = D :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hpat.2.2]; unfold nb at hnbk; omega)
        have hpD : p.1 ∈ D := (hmemD p.1).mp (List.mem_map_of_mem hp)
        rw [← heq] at hpD
        obtain ⟨y, hyB, hy⟩ := mem_blockRows.mp hpD
        have h1 := hb t h0 p.1 y hy (Finset.disjoint_right.mp hLB hyB)
        have h2 := (mem_pairs hpat.2.1 hBl' _).mp h1
        have h3 := (mem_pairs hpat.2.1 hBl' _).mp hp
        rw [h3] at h2
        rw [hy, Option.some.inj h2]

/-- Reconstruction of `g ∈ gr_k` from its slices. -/
theorem sum_putL_partL {Lr : Finset α} {Bl : List α} (hBl : Bl.Nodup) {k : ℕ} {g : Fn R ι α}
    (hg : g ∈ Gr Lr Bl.toFinset k) :
    ∑ pat ∈ univ.filter (IsPat Bl.toFinset k),
      putL (pairs Bl pat) (partL (pairs Bl pat) g) = g := by
  set B := Bl.toFinset
  funext t
  rw [Finset.sum_apply]
  have hterm : ∀ pat ∈ univ.filter (IsPat B k), putL (pairs Bl pat) (partL (pairs Bl pat) g) t =
      if (∀ i x, pat i = some x → t i = some x) then g t else 0 := by
    intro pat hpat
    have hpat := (Finset.mem_filter.mp hpat).2
    have hBl' : ∀ i x, pat i = some x → x ∈ Bl := fun i x h =>
      List.mem_toFinset.mp (hpat.1 i x h)
    rw [putL_partL_apply _ (pairs_fst_nodup hBl hpat.2.1 hBl')]
    congr 1
    apply propext
    constructor
    · intro h i x hx
      exact h (i, x) ((mem_pairs hpat.2.1 hBl' (i, x)).mpr hx)
    · intro h p hp
      exact h p.1 p.2 ((mem_pairs hpat.2.1 hBl' p).mp hp)
  rw [Finset.sum_congr rfl hterm]
  by_cases h0 : g t = 0
  · simp [h0]
  · have G := hg.1 t h0
    have hk : nb B t = k := by
      by_contra h
      exact h0 (hg.2.1 t h)
    let patT : ι → Option α := fun i => if i ∈ blockRows B t then t i else none
    have hdomT : patDom patT = blockRows B t := by
      ext i
      simp only [patDom, Finset.mem_filter, Finset.mem_univ, true_and, patT]
      by_cases hi : i ∈ blockRows B t
      · simp only [hi, if_true, iff_true]
        obtain ⟨y, _, hy⟩ := mem_blockRows.mp hi
        rw [hy]
        simp
      · simp [hi]
    have hpatT : IsPat B k patT := by
      refine ⟨fun i x hx => ?_, fun i j x hi hj => ?_, by rw [hdomT]; exact hk⟩
      · simp only [patT] at hx
        split_ifs at hx with hi
        obtain ⟨y, hyB, hy⟩ := mem_blockRows.mp hi
        rw [hy] at hx
        cases hx
        exact hyB
      · simp only [patT] at hi hj
        split_ifs at hi hj
        exact G.inj i j x hi hj
    rw [Finset.sum_eq_single patT]
    · rw [if_pos]
      intro i x hx
      simp only [patT] at hx
      split_ifs at hx
      exact hx
    · intro pat hpat hne
      have hpat := (Finset.mem_filter.mp hpat).2
      rw [if_neg]
      intro hsub
      apply hne
      have hBl' : ∀ i x, pat i = some x → x ∈ Bl := fun i x h =>
        List.mem_toFinset.mp (hpat.1 i x h)
      have hD : patDom pat ⊆ blockRows B t := patDom_subset_blockRows hpat.1 hpat.2.1 hBl'
        (fun p hp => hsub p.1 p.2 ((mem_pairs hpat.2.1 hBl' p).mp hp))
      have heq : patDom pat = blockRows B t :=
        Finset.eq_of_subset_of_card_le hD (by rw [hpat.2.2]; unfold nb at hk; omega)
      funext i
      simp only [patT]
      by_cases hi : i ∈ patDom pat
      · simp only [patDom, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hi
        have hiB : i ∈ blockRows B t := by
          rw [← heq]
          simp [patDom, hx]
        rw [if_pos hiB, hx, hsub i x hx]
      · have hiB : i ∉ blockRows B t := by rw [← heq]; exact hi
        rw [if_neg hiB]
        simpa [patDom] using hi
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨mem_univ _, hpatT⟩) h

/-- **Prop. 4(b).**  For `1 ≤ k` and `2|ι| ≤ |Lr| + 1`, `blockSection` is a section of
`topPart k : Soc^{≤k} → gr_k`. -/
theorem blockSection_spec (C : Chooser α) {Lr : Finset α} {Bl : List α} (hBl : Bl.Nodup)
    (hLB : Disjoint Lr Bl.toFinset) {k : ℕ} (hk : 1 ≤ k)
    (hL : 2 * Fintype.card ι ≤ Lr.card + 1) {g : Fn R ι α} (hg : g ∈ Gr Lr Bl.toFinset k) :
    blockSection C Lr Bl k g ∈ Filt Lr Bl.toFinset k ∧
      topPart Bl.toFinset k (blockSection C Lr Bl k g) = g := by
  have happ : blockSection C Lr Bl k g =
      ∑ pat ∈ univ.filter (IsPat Bl.toFinset k), piece C Lr Bl pat g := by
    rw [blockSection, LinearMap.sum_apply]
  rw [happ]
  refine ⟨sum_mem fun pat hpat => (piece_spec C hBl hLB hk hL hg
    (Finset.mem_filter.mp hpat).2).1, ?_⟩
  rw [map_sum, Finset.sum_congr rfl fun pat hpat => (piece_spec C hBl hLB hk hL hg
    (Finset.mem_filter.mp hpat).2).2]
  exact sum_putL_partL hBl hg

/-! ### Equivariance of the section -/

theorem rowAct_partL (σ : Equiv.Perm ι) : ∀ ps : List (ι × α),
    rowAct σ * partL ps = (partL (ps.map (Prod.map σ id)) * rowAct σ : Module.End R (Fn R ι α))
  | [] => by simp [partL]
  | p :: ps => by
    simp only [partL, List.map_cons]
    rw [← mul_assoc, rowAct_partL σ ps, mul_assoc, rowAct_part, ← mul_assoc]
    rfl

theorem rowAct_Tl (σ : Equiv.Perm ι) : ∀ ps : List (ι × α),
    rowAct σ * Tl ps = (Tl (ps.map (Prod.map σ id)) * rowAct σ : Module.End R (Fn R ι α))
  | [] => by simp [Tl]
  | p :: ps => by
    simp only [Tl, List.map_cons]
    have h1 : rowAct σ * (put p.1 p.2 * del p.1 - 1) =
        (put (σ p.1) p.2 * del (σ p.1) - 1 : Module.End R (Fn R ι α)) * rowAct σ := by
      rw [mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc, rowAct_put, mul_assoc, rowAct_del,
        ← mul_assoc]
    rw [← mul_assoc, h1, mul_assoc, rowAct_Tl σ ps, ← mul_assoc]
    rfl

theorem patDom_comp (pat : ι → Option α) (σ : Equiv.Perm ι) :
    (patDom (pat ∘ σ.symm))ᶜ = ((patDom pat)ᶜ).map σ.toEmbedding := by
  ext i
  rw [Finset.mem_map_equiv, Finset.mem_compl, Finset.mem_compl]
  simp [patDom]

theorem isPat_comp {B : Finset α} {k : ℕ} {pat : ι → Option α} (σ : Equiv.Perm ι)
    (h : IsPat B k pat) : IsPat B k (pat ∘ σ.symm) := by
  refine ⟨fun i x hx => h.1 _ x hx, fun i j x hi hj => σ.symm.injective (h.2.1 _ _ x hi hj), ?_⟩
  have : patDom (pat ∘ σ.symm) = (patDom pat).map σ.toEmbedding := by
    ext i
    rw [Finset.mem_map_equiv]
    simp [patDom]
  rw [this, Finset.card_map, h.2.2]

theorem rowAct_piece (C : Chooser α) (Lr : Finset α) (Bl : List α) {pat : ι → Option α}
    (hinj : ∀ i j x, pat i = some x → pat j = some x → i = j) (σ : Equiv.Perm ι) :
    rowAct σ * piece (R := R) C Lr Bl pat = piece C Lr Bl (pat ∘ σ.symm) * rowAct σ := by
  unfold piece
  rw [pairs_comp hinj σ, patDom_comp pat σ, ← mul_assoc, ← mul_assoc, rowAct_Tl, mul_assoc,
    mul_assoc, ← mul_assoc (rowAct σ), rowAct_cone_map, mul_assoc, rowAct_partL, List.map_map]
  simp only [mul_assoc]
  congr 3
  rw [List.map_map]
  rfl

/-- The section commutes with every row permutation. -/
theorem rowAct_blockSection (C : Chooser α) (Lr : Finset α) (Bl : List α) (k : ℕ)
    (σ : Equiv.Perm ι) :
    rowAct σ * blockSection (R := R) C Lr Bl k = blockSection C Lr Bl k * rowAct σ := by
  unfold blockSection
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun pat hpat =>
    rowAct_piece C Lr Bl (Finset.mem_filter.mp hpat).2.2.1 σ]
  refine Finset.sum_nbij' (fun pat : ι → Option α => pat ∘ σ.symm)
    (fun pat : ι → Option α => pat ∘ σ) ?_ ?_ ?_ ?_ ?_
  · intro pat hpat
    exact Finset.mem_filter.mpr ⟨mem_univ _, isPat_comp σ (Finset.mem_filter.mp hpat).2⟩
  · intro pat hpat
    have := isPat_comp σ.symm (Finset.mem_filter.mp hpat).2
    rw [Equiv.symm_symm] at this
    exact Finset.mem_filter.mpr ⟨mem_univ _, this⟩
  · intro pat _
    funext i
    simp
  · intro pat _
    funext i
    simp
  · intro pat _
    rfl

end BExact
