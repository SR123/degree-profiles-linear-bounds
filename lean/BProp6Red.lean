/-
Agent B, round 3 (26 Sep 2026).  Reduction of `Prop6Hyp` (a statement about `gr_k`) to the
paper's Prop. 6 proper, a statement about the block-pattern module alone.

`PatSp k` = functions on block patterns with `k` rows (`⊕_{|D| = k} K[Inj(D, B)]`).
`Prop6PatHyp`: for `1 ≤ k ≤ b` there is a row-stable, domain-graded `V ≤ PatSp k` with
`PatSp k = ⊕_{i<p} Z^i V` (injective `zSum`).  This is exactly "K[Inj([k],B)] is free over
`K⟨g⟩` with an `S_k`-stable complement", induced up to `S_b`; the paper's Prop. 6 (freeness over
`K S_k ⊗ K⟨g⟩`, `k < q`, generic `c`) gives it.

`prop6Hyp_of_pat`: `Prop6PatHyp → Prop6Hyp`, with `Q₀ = span {v ⊠ y}` where
`(v ⊠ y)(t) = v(block part of t) · y(retained part of t)` (`merge`), `v ∈ V` of domain `D`,
`y ∈ Soc_{D^c}(Lr)`.  Injectivity uses the evaluation maps `ev_s` at retained tuples `s`, which
commute with `Z` and map `Q₀` into `V`.
-/
import BThm5
import BTransC

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 ClaudeCP DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ConcreteM5

variable {K : Type} [Field K]

section Parts

variable {b N : ℕ} (n : ℕ)

/-- Is the entry a block label? -/
def isBlk : Option (Fin N) → Prop
  | none => False
  | some x => n ≤ x.val

instance : DecidablePred (isBlk (N := N) n) := fun o => by
  cases o <;> unfold isBlk <;> infer_instance

/-- The block part of a tuple. -/
def blockPart (t : Fin b → Option (Fin N)) : Fin b → Option (Fin N) :=
  fun i => if isBlk n (t i) then t i else none

/-- The retained part of a tuple. -/
def retPart (t : Fin b → Option (Fin N)) : Fin b → Option (Fin N) :=
  fun i => if isBlk n (t i) then none else t i

/-- Union of two partial tuples (the first wins). -/
def joinT (t s : Fin b → Option (Fin N)) : Fin b → Option (Fin N) := fun i => (t i).or (s i)

theorem join_parts (t : Fin b → Option (Fin N)) : joinT (blockPart n t) (retPart n t) = t := by
  funext i
  simp only [joinT, blockPart, retPart]
  split_ifs with h
  · cases t i <;> rfl
  · rfl

theorem isBlk_iff_mem_Bk {x : Fin N} : isBlk n (some x) ↔ x ∈ Bk n N := by
  simp [isBlk, Bk]

theorem mem_blockRows_iff_blockPart {t : Fin b → Option (Fin N)} {i : Fin b} :
    i ∈ blockRows (Bk n N) t ↔ blockPart n t i ≠ none := by
  rw [mem_blockRows]
  simp only [blockPart]
  constructor
  · rintro ⟨x, hx, hti⟩
    rw [hti, if_pos ((isBlk_iff_mem_Bk n).mpr hx)]
    simp
  · intro h
    split_ifs at h with hb
    · cases hti : t i with
      | none => rw [hti] at hb; exact absurd hb (by simp [isBlk])
      | some x => exact ⟨x, (isBlk_iff_mem_Bk n).mp (hti ▸ hb), rfl⟩
    · exact absurd rfl h

end Parts

/-! ### The merge `v ⊠ y` -/

section Merge

variable {b N : ℕ} (n : ℕ)

/-- `(v ⊠ y)(t) = v(block part) · y(retained part)`, linear in `y`. -/
def merge (v : Fn K (Fin b) (Fin N)) : Fn K (Fin b) (Fin N) →ₗ[K] Fn K (Fin b) (Fin N) where
  toFun y t := v (blockPart n t) * y (retPart n t)
  map_add' y y' := by funext t; simp [mul_add]
  map_smul' c y := by funext t; simp [mul_left_comm]

theorem merge_apply (v y : Fn K (Fin b) (Fin N)) (t : Fin b → Option (Fin N)) :
    merge n v y t = v (blockPart n t) * y (retPart n t) := rfl

theorem merge_add_left (v v' y : Fn K (Fin b) (Fin N)) :
    merge n (v + v') y = merge n v y + merge n v' y := by
  funext t
  simp [merge_apply, add_mul]

theorem merge_smul_left (c : K) (v y : Fn K (Fin b) (Fin N)) :
    merge n (c • v) y = c • merge n v y := by
  funext t
  simp [merge_apply, mul_assoc]

theorem merge_sum_left {ι : Type} (s : Finset ι) (v : ι → Fn K (Fin b) (Fin N))
    (y : Fn K (Fin b) (Fin N)) : merge n (∑ i ∈ s, v i) y = ∑ i ∈ s, merge n (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext t
    simp [merge_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, merge_add_left, ih]

theorem FixesLr.blockPart_map {π : Equiv.Perm (Fin N)} (h : FixesLr n π)
    (t : Fin b → Option (Fin N)) :
    blockPart n (fun i => (t i).map π.symm) = fun i => (blockPart n t i).map π.symm := by
  funext i
  simp only [blockPart]
  cases hti : t i with
  | none => simp [isBlk]
  | some x =>
    have : isBlk n (some (π.symm x)) ↔ isBlk n (some x) := by
      rw [isBlk_iff_mem_Bk, isBlk_iff_mem_Bk]
      exact FixesLr.mem_Bk_iff (FixesLr.symm h) x
    simp only [Option.map_some]
    by_cases hb : isBlk n (some x)
    · rw [if_pos (this.mpr hb), if_pos hb]
      rfl
    · rw [if_neg (fun h' => hb (this.mp h')), if_neg hb]
      rfl

theorem FixesLr.retPart_map {π : Equiv.Perm (Fin N)} (h : FixesLr n π)
    (t : Fin b → Option (Fin N)) :
    retPart n (fun i => (t i).map π.symm) = retPart n t := by
  funext i
  simp only [retPart]
  cases hti : t i with
  | none => simp
  | some x =>
    have hiff : isBlk n (some (π.symm x)) ↔ isBlk n (some x) := by
      rw [isBlk_iff_mem_Bk, isBlk_iff_mem_Bk]
      exact FixesLr.mem_Bk_iff (FixesLr.symm h) x
    simp only [Option.map_some]
    by_cases hb : isBlk n (some x)
    · rw [if_pos (hiff.mpr hb), if_pos hb]
    · rw [if_neg (fun h' => hb (hiff.mp h')), if_neg hb]
      have hx : x.val < n := by simpa [isBlk] using hb
      rw [FixesLr.symm h x hx]

theorem FixesLr.labAct_merge {π : Equiv.Perm (Fin N)} (h : FixesLr n π)
    (v y : Fn K (Fin b) (Fin N)) :
    labAct π (merge n v y) = merge n (labAct π v) y := by
  funext t
  rw [labAct_apply, merge_apply, merge_apply, FixesLr.blockPart_map n h, FixesLr.retPart_map n h,
    labAct_apply]

theorem rowAct_merge (σ : Equiv.Perm (Fin b)) (v y : Fn K (Fin b) (Fin N)) :
    rowAct σ (merge n v y) = merge n (rowAct σ v) (rowAct σ y) := by
  funext t
  rfl

end Merge

/-! ### Pattern space, and `v ⊠ y ∈ gr_k` -/

section PatSpace

variable {b N : ℕ} (n : ℕ)

/-- Functions on block patterns with `k` rows. -/
def PatSp (k : ℕ) : Submodule K (Fn K (Fin b) (Fin N)) where
  carrier := {h | ∀ t, h t ≠ 0 → IsPat (Bk n N) k t}
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

/-- `v` is supported on patterns with rows exactly `D`. -/
def HasDom (D : Finset (Fin b)) (v : Fn K (Fin b) (Fin N)) : Prop :=
  ∀ t, v t ≠ 0 → patDom t = D

theorem mem_patDom {t : Fin b → Option (Fin N)} {i : Fin b} : i ∈ patDom t ↔ t i ≠ none := by
  simp [patDom]

theorem blockRows_eq_patDom (t : Fin b → Option (Fin N)) :
    blockRows (Bk n N) t = patDom (blockPart n t) := by
  ext i
  rw [mem_blockRows_iff_blockPart, mem_patDom]

theorem blockPart_ne_none {t : Fin b → Option (Fin N)} {i : Fin b} (h : blockPart n t i ≠ none) :
    blockPart n t i = t i := by
  simp only [blockPart] at h ⊢
  split_ifs at h ⊢ with hb
  · rfl
  · exact absurd rfl h

theorem retPart_of_not_blk {t : Fin b → Option (Fin N)} {i : Fin b} (h : blockPart n t i = none) :
    retPart n t i = t i := by
  simp only [blockPart, retPart] at h ⊢
  split_ifs at h ⊢ with hb
  · cases hti : t i with
    | none => rfl
    | some x => rw [hti] at h; cases h
  · rfl

theorem retPart_of_blk {t : Fin b → Option (Fin N)} {i : Fin b} (h : blockPart n t i ≠ none) :
    retPart n t i = none := by
  simp only [blockPart, retPart] at h ⊢
  split_ifs at h ⊢ with hb
  · rfl
  · exact absurd rfl h

/-- `v ⊠ y ∈ gr_k`. -/
theorem merge_mem_Gr {k : ℕ} {D : Finset (Fin b)} {v : Fn K (Fin b) (Fin N)}
    (hv : v ∈ PatSp n k) (hD : HasDom D v) {y : Fn K (Fin b) (Fin N)}
    (hy : y ∈ Soc Dᶜ Dᶜ (Lr n N)) : merge n v y ∈ Gr (Lr n N) (Bk n N) k := by
  -- the two factors at a tuple in the support
  have key : ∀ t, merge n v y t ≠ 0 → IsPat (Bk n N) k (blockPart n t) ∧
      patDom (blockPart n t) = D ∧ Good Dᶜ (Lr n N) (retPart n t) := by
    intro t ht
    rw [merge_apply] at ht
    have h1 : v (blockPart n t) ≠ 0 := left_ne_zero_of_mul ht
    have h2 : y (retPart n t) ≠ 0 := right_ne_zero_of_mul ht
    exact ⟨hv _ h1, hD _ h1, hy.1 _ h2⟩
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun j => ?_⟩
  · obtain ⟨hpat, hdom, hgood⟩ := key t ht
    refine ⟨fun j => ?_, fun j y' _ => by rw [Lr_union]; exact mem_univ _, fun j j' y' hj hj' => ?_⟩
    · simp only [mem_univ, iff_true]
      by_cases hjD : j ∈ D
      · rw [← hdom, mem_patDom] at hjD
        rw [← blockPart_ne_none n hjD]
        exact hjD
      · have := (hgood.dom j).mpr (Finset.mem_compl.mpr hjD)
        by_cases hb : blockPart n t j = none
        · rwa [retPart_of_not_blk n hb] at this
        · rw [← blockPart_ne_none n hb]; exact hb
    · by_cases hb : isBlk n (some y')
      · have e1 : blockPart n t j = some y' := by simp [blockPart, hj, hb]
        have e2 : blockPart n t j' = some y' := by simp [blockPart, hj', hb]
        exact hpat.2.1 j j' y' e1 e2
      · have e1 : retPart n t j = some y' := by simp [retPart, hj, hb]
        have e2 : retPart n t j' = some y' := by simp [retPart, hj', hb]
        exact hgood.inj j j' y' e1 e2
  · by_contra h0
    obtain ⟨hpat, _, _⟩ := key t h0
    apply ht
    unfold BExact.nb
    rw [blockRows_eq_patDom]
    exact hpat.2.2
  · funext t
    rw [delRet_apply]
    simp only [part_apply]
    by_cases htj : t j = none
    · simp only [htj, if_true]
      have hbp : ∀ x ∈ Lr n N, blockPart n (update t j (some x)) = blockPart n t := by
        intro x hx
        have hx' : ¬ isBlk n (some x) := by simp [isBlk, Lr] at hx ⊢; omega
        funext i
        by_cases hij : i = j
        · subst hij
          simp [blockPart, hx', htj]
        · simp [blockPart, update_of_ne hij]
      have hrp : ∀ x ∈ Lr n N, retPart n (update t j (some x)) = update (retPart n t) j (some x) := by
        intro x hx
        have hx' : ¬ isBlk n (some x) := by simp [isBlk, Lr] at hx ⊢; omega
        funext i
        by_cases hij : i = j
        · subst hij
          simp [retPart, hx']
        · simp [retPart, update_of_ne hij]
      rw [Finset.sum_congr rfl fun x hx => by rw [merge_apply, hbp x hx, hrp x hx],
        ← Finset.mul_sum]
      by_cases hv0 : v (blockPart n t) = 0
      · rw [hv0, zero_mul]
        rfl
      · have hdom := hD _ hv0
        have hjD : j ∉ D := by
          rw [← hdom, mem_patDom]
          simp [blockPart, htj, isBlk]
        have hrj : retPart n t j = none := by simp [retPart, htj]
        have hdel := congrFun (hy.2 j (Finset.mem_compl.mpr hjD)) (retPart n t)
        rw [del_apply] at hdel
        simp only [part_apply, hrj, if_true] at hdel
        rw [← Finset.sum_subset (Finset.subset_univ (Lr n N))] at hdel
        · rw [hdel]
          simp
        · intro x _ hx
          by_contra h0
          exact hx ((hy.1 _ h0).val j x (update_self _ _ _))
    · simp [htj]

end PatSpace

/-! ### Reconstruction of `gr_k` from slices, domain restriction, evaluation -/

section Tools

variable {b N : ℕ} (n : ℕ)

theorem merge_single_slice {k : ℕ} {g : Fn K (Fin b) (Fin N)}
    (hg : g ∈ Gr (Lr n N) (Bk n N) k) {pat : Fin b → Option (Fin N)}
    (hpat : IsPat (Bk n N) k pat) :
    merge n (Pi.single pat 1) (partL (pairs (Bl n N) pat) g) =
      putL (pairs (Bl n N) pat) (partL (pairs (Bl n N) pat) g) := by
  have hBl' : ∀ i x, pat i = some x → x ∈ Bl n N := fun i x h => by
    rw [← List.mem_toFinset, Bl_toFinset]
    exact hpat.1 i x h
  have hnd := pairs_fst_nodup (Bl_nodup n N) hpat.2.1 hBl'
  have hmem := mem_pairs (Bl := Bl n N) hpat.2.1 hBl'
  funext t
  rw [merge_apply, putL_partL_apply _ hnd, partL_apply _ hnd, Pi.single_apply]
  by_cases hbt : blockPart n t = pat
  · subst hbt
    have hall : ∀ q ∈ pairs (Bl n N) (blockPart n t), t q.1 = some q.2 := fun q hq => by
      have h1 := (hmem q).mp hq
      rw [← h1, blockPart_ne_none n (by rw [h1]; simp)]
    have hnone : ∀ q ∈ pairs (Bl n N) (blockPart n t), retPart n t q.1 = none := fun q hq =>
      retPart_of_blk n (by rw [(hmem q).mp hq]; simp)
    have hfill : fillL (pairs (Bl n N) (blockPart n t)) (retPart n t) = t := by
      funext i
      by_cases hi : i ∈ (pairs (Bl n N) (blockPart n t)).map Prod.fst
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        rw [fillL_of_mem _ hnd _ hq, hall q hq]
      · rw [fillL_of_not_mem _ _ hi]
        apply retPart_of_not_blk
        by_contra h
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp h
        exact hi (List.mem_map.mpr ⟨(i, x), (hmem (i, x)).mpr hx, rfl⟩)
    rw [if_pos rfl, one_mul, if_pos hnone, hfill, if_pos hall]
  · rw [if_neg hbt, zero_mul]
    split_ifs with hall
    · symm
      apply hg.2.1
      intro hk
      apply hbt
      have hsub : patDom pat ⊆ blockRows (Bk n N) t := by
        intro i hi
        rw [mem_patDom] at hi
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hi
        rw [mem_blockRows]
        exact ⟨x, hpat.1 i x hx, hall (i, x) ((hmem (i, x)).mpr hx)⟩
      have heq : patDom pat = blockRows (Bk n N) t :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hpat.2.2]; unfold BExact.nb at hk; omega)
      rw [blockRows_eq_patDom] at heq
      funext i
      by_cases hi : i ∈ patDom pat
      · rw [mem_patDom] at hi
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hi
        rw [hx, blockPart_ne_none n (by rw [← mem_patDom, ← heq, mem_patDom, hx]; simp),
          hall (i, x) ((hmem (i, x)).mpr hx)]
      · have h1 : pat i = none := by simpa [mem_patDom] using hi
        have h2 : blockPart n t i = none := by
          rw [heq] at hi
          simpa [mem_patDom] using hi
        rw [h1, h2]
    · rfl

/-- Restriction to patterns with rows exactly `D`. -/
def resD (D : Finset (Fin b)) : Module.End K (Fn K (Fin b) (Fin N)) where
  toFun h t := if patDom t = D then h t else 0
  map_add' f g := by funext t; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by funext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

theorem resD_apply (D : Finset (Fin b)) (h : Fn K (Fin b) (Fin N)) (t : Fin b → Option (Fin N)) :
    resD D h t = if patDom t = D then h t else 0 := rfl

theorem hasDom_resD (D : Finset (Fin b)) (h : Fn K (Fin b) (Fin N)) : HasDom D (resD D h) := by
  intro t ht
  rw [resD_apply] at ht
  split_ifs at ht with hd
  · exact hd
  · exact absurd rfl ht

theorem resD_of_hasDom {D : Finset (Fin b)} {h : Fn K (Fin b) (Fin N)} (hh : HasDom D h) :
    resD D h = h := by
  funext t
  rw [resD_apply]
  split_ifs with hd
  · rfl
  · by_contra h0
    exact hd (hh t (Ne.symm h0))

theorem patDom_map (π : Equiv.Perm (Fin N)) (t : Fin b → Option (Fin N)) :
    patDom (fun i => (t i).map π.symm) = patDom t := by
  ext i
  simp [mem_patDom]

theorem labAct_resD (π : Equiv.Perm (Fin N)) (D : Finset (Fin b)) :
    labAct π * resD D = (resD D * labAct π : Module.End K (Fn K (Fin b) (Fin N))) := by
  apply LinearMap.ext
  intro h
  funext t
  simp only [Module.End.mul_apply, labAct_apply, resD_apply, patDom_map]

/-- Evaluation at a retained tuple `s`: `(ev_s F)(t) = F(t ∪ s)` for block-only `t` disjoint
from `s`. -/
noncomputable def evR (s : Fin b → Option (Fin N)) : Module.End K (Fn K (Fin b) (Fin N)) where
  toFun F t := by
    classical
    exact if (∀ i, t i = none ∨ s i = none) ∧ retPart n t = (fun _ => none) then F (joinT t s)
      else 0
  map_add' f g := by
    classical
    funext t
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c f := by
    classical
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem evR_apply (s : Fin b → Option (Fin N)) (F : Fn K (Fin b) (Fin N))
    (t : Fin b → Option (Fin N)) :
    evR n s F t = by
      classical
      exact if (∀ i, t i = none ∨ s i = none) ∧ retPart n t = (fun _ => none) then F (joinT t s)
        else 0 := rfl

/-- Retained-only tuples. -/
def RetOnly (s : Fin b → Option (Fin N)) : Prop := ∀ i, ¬ isBlk n (s i)

theorem retOnly_retPart (t : Fin b → Option (Fin N)) : RetOnly n (retPart n t) := by
  intro i
  simp only [retPart]
  split_ifs with h
  · simp [isBlk]
  · exact h

theorem evR_merge {s : Fin b → Option (Fin N)} (hs : RetOnly n s) {k : ℕ} {D : Finset (Fin b)}
    {v : Fn K (Fin b) (Fin N)} (hv : v ∈ PatSp n k) (hD : HasDom D v) {y : Fn K (Fin b) (Fin N)}
    (hy : y ∈ P Dᶜ (Lr n N)) : evR n s (merge n v y) = y s • v := by
  classical
  funext t
  rw [evR_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hc
  · obtain ⟨hdisj, hret⟩ := hc
    have hblk : ∀ i, t i ≠ none → isBlk n (t i) := fun i hi => by
      have := congrFun hret i
      simp only [retPart] at this
      split_ifs at this with hb
      · exact hb
      · exact absurd this hi
    have hbp : blockPart n (joinT t s) = t := by
      funext i
      simp only [blockPart, joinT]
      by_cases hti : t i = none
      · rw [hti]
        simp only [Option.none_or]
        rw [if_neg (hs i)]
      · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hti
        have hb := hblk i hti
        rw [hx] at hb ⊢
        simp [hb]
    have hrp : retPart n (joinT t s) = s := by
      funext i
      simp only [retPart, joinT]
      by_cases hti : t i = none
      · rw [hti]
        simp only [Option.none_or]
        rw [if_neg (hs i)]
      · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hti
        have hb := hblk i hti
        rw [hx] at hb ⊢
        simp only [Option.some_or, if_pos hb]
        exact ((hdisj i).resolve_left hti).symm
    rw [merge_apply, hbp, hrp, mul_comm]
  · by_contra hne0
    have hne : y s * v t ≠ 0 := fun h => hne0 h.symm
    apply hc
    have hv0 : v t ≠ 0 := right_ne_zero_of_mul hne
    have hy0 : y s ≠ 0 := left_ne_zero_of_mul hne
    have hpat := hv t hv0
    have hdt := hD t hv0
    have hgs := hy s hy0
    refine ⟨fun i => ?_, ?_⟩
    · by_cases hi : i ∈ D
      · right
        by_contra h
        exact (Finset.mem_compl.mp ((hgs.dom i).mp h)) hi
      · left
        rw [← hdt, mem_patDom] at hi
        simpa using hi
    · funext i
      simp only [retPart]
      split_ifs with hb
      · rfl
      · cases hti : t i with
        | none => rfl
        | some x =>
          exfalso
          apply hb
          rw [hti, isBlk_iff_mem_Bk]
          exact hpat.1 i x hti

theorem FixesLr.joinT_map {π : Equiv.Perm (Fin N)} (h : FixesLr n π) {s : Fin b → Option (Fin N)}
    (hs : RetOnly n s) (t : Fin b → Option (Fin N)) :
    (fun i => (joinT t s i).map π.symm) = joinT (fun i => (t i).map π.symm) s := by
  funext i
  simp only [joinT]
  cases hti : t i with
  | some x => simp
  | none =>
    simp only [Option.none_or, Option.map_none]
    cases hsi : s i with
    | none => rfl
    | some x =>
      have hx : x.val < n := by
        have := hs i
        rw [hsi] at this
        simpa [isBlk] using this
      simp [FixesLr.symm h x hx]

theorem FixesLr.evR_comm {π : Equiv.Perm (Fin N)} (h : FixesLr n π) {s : Fin b → Option (Fin N)}
    (hs : RetOnly n s) :
    evR n s * labAct π = (labAct π * evR n s : Module.End K (Fn K (Fin b) (Fin N))) := by
  classical
  apply LinearMap.ext
  intro F
  funext t
  simp only [Module.End.mul_apply, evR_apply, labAct_apply]
  have hc : ((∀ i, (t i).map π.symm = none ∨ s i = none) ∧
      retPart n (fun i => (t i).map π.symm) = fun _ => none) ↔
      ((∀ i, t i = none ∨ s i = none) ∧ retPart n t = fun _ => none) := by
    rw [FixesLr.retPart_map n h]
    simp
  by_cases hct : (∀ i, t i = none ∨ s i = none) ∧ retPart n t = fun _ => none
  · rw [if_pos hct, if_pos (hc.mpr hct), FixesLr.joinT_map n h hs]
  · rw [if_neg hct, if_neg (fun h' => hct (hc.mp h'))]

theorem evR_recover (F : Fn K (Fin b) (Fin N)) (t : Fin b → Option (Fin N)) :
    evR n (retPart n t) F (blockPart n t) = F t := by
  classical
  rw [evR_apply, if_pos, join_parts]
  refine ⟨fun i => ?_, ?_⟩
  · by_cases h : blockPart n t i = none
    · exact Or.inl h
    · exact Or.inr (retPart_of_blk n h)
  · funext i
    simp only [retPart, blockPart]
    split_ifs <;> rfl

end Tools

/-! ### The reduction -/

section Reduction

variable {b N : ℕ}

theorem rowAct_mem_Soc_map (σ : Equiv.Perm (Fin b)) {Rr S : Finset (Fin b)} {L : Finset (Fin N)}
    {y : Fn K (Fin b) (Fin N)} (hy : y ∈ Soc Rr S L) :
    rowAct σ y ∈ Soc (Rr.map σ.toEmbedding) (S.map σ.toEmbedding) L := by
  refine ⟨fun t ht => ?_, fun i hi => ?_⟩
  · have g := hy.1 _ ht
    refine ⟨fun j => ?_, fun j x hx => g.val (σ.symm j) x (by simpa using hx),
      fun j j' x hj hj' => σ.symm.injective (g.inj (σ.symm j) (σ.symm j') x (by simpa using hj)
        (by simpa using hj'))⟩
    rw [Finset.mem_map_equiv, ← g.dom (σ.symm j)]
    simp
  · have h := rowAct_del (R := K) (α := Fin N) σ (σ.symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [← Module.End.mul_apply, ← h, Module.End.mul_apply,
      hy.2 _ ((Finset.mem_map_equiv).mp hi), map_zero]

theorem hasDom_rowAct (σ : Equiv.Perm (Fin b)) {D : Finset (Fin b)} {v : Fn K (Fin b) (Fin N)}
    (hv : HasDom D v) : HasDom (D.map σ.toEmbedding) (rowAct σ v) := by
  intro t ht
  have := hv _ ht
  ext i
  rw [Finset.mem_map_equiv, ← this, mem_patDom, mem_patDom]
  simp

theorem compl_map (σ : Equiv.Perm (Fin b)) (D : Finset (Fin b)) :
    (D.map σ.toEmbedding)ᶜ = Dᶜ.map σ.toEmbedding := by
  ext i
  simp [Finset.mem_map_equiv]

variable (p : ℕ) [Fact p.Prime] {a n : ℕ} (c : Fin a → K)

theorem Z_merge (v y : Fn K (Fin b) (Fin (n + p ^ a))) :
    rhoFn (zEltP p a n c) (merge n v y) = merge n (rhoFn (zEltP p a n c) v) y := by
  rw [Z_eq, LinearMap.sum_apply, LinearMap.sum_apply, merge_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
  rw [merge_smul_left, FixesLr.labAct_merge n (sigma_fixesLr p i)]
  congr 1
  funext t
  simp [merge_apply, sub_mul]

theorem Z_pow_merge (k : ℕ) (v y : Fn K (Fin b) (Fin (n + p ^ a))) :
    (rhoFn (zEltP p a n c) ^ k) (merge n v y) = merge n ((rhoFn (zEltP p a n c) ^ k) v) y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Z_merge]
    rfl

/-- **Prop. 6, pattern form** (CONDITIONAL input): for `1 ≤ k ≤ b`, `PatSp k = ⊕_{i<p} Z^i V`
with `V` row-stable and graded by the rows of the patterns. -/
def Prop6PatHyp (b : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ b → ∃ V : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))),
    (∀ σ : Equiv.Perm (Fin b), ∀ v ∈ V, rowAct σ v ∈ V) ∧
    (∀ D : Finset (Fin b), ∀ v ∈ V, resD D v ∈ V) ∧
    LinearMap.range (zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) V) = PatSp n k ∧
    Function.Injective (zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) V)

/-- **The reduction**: the pattern form of Prop. 6 implies `Prop6Hyp`. -/
theorem prop6Hyp_of_pat (h : Prop6PatHyp p (n := n) c b) : Prop6Hyp p a n b c := by
  intro k hk hkb
  have hZres : ∀ (D : Finset (Fin b)) (j : ℕ) (x : Fn K (Fin b) (Fin (n + p ^ a))),
      resD D ((rhoFn (zEltP p a n c) ^ j) x) = (rhoFn (zEltP p a n c) ^ j) (resD D x) := by
    intro D j x
    have hc : resD D * rhoFn (ι := Fin b) (zEltP p a n c) = rhoFn (zEltP p a n c) * resD D :=
      Z_comm p c (resD D) (fun π _ => (labAct_resD π D).symm)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.pow_right hc j).eq]
  have hevZ : ∀ s : Fin b → Option (Fin (n + p ^ a)), RetOnly n s →
      ∀ (j : ℕ) (x : Fn K (Fin b) (Fin (n + p ^ a))),
        evR n s ((rhoFn (zEltP p a n c) ^ j) x) = (rhoFn (zEltP p a n c) ^ j) (evR n s x) := by
    intro s hs j x
    have hc : evR n s * rhoFn (ι := Fin b) (zEltP p a n c) = rhoFn (zEltP p a n c) * evR n s :=
      Z_comm p c (evR n s) (fun π hπ => FixesLr.evR_comm n hπ hs)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.pow_right hc j).eq]
  have hZGr : ∀ e ∈ Gr (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) k,
      rhoFn (ι := Fin b) (zEltP p a n c) e ∈ Gr (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) k :=
    fun e he => Z_mem p _ (fun π hπ F hF => FixesLr.mem_Gr hπ hF) he
  obtain ⟨V, hVrow, hVres, hVrange, hVinj⟩ := h k hk hkb
  have hVP : V ≤ PatSp n k := by
    rw [← hVrange]
    exact C_le_range _ (by omega) _ _
  let gens : Set (Fn K (Fin b) (Fin (n + p ^ a))) := {F | ∃ v ∈ V, ∃ D : Finset (Fin b),
    HasDom D v ∧ ∃ y ∈ (Soc Dᶜ Dᶜ (Lr n (n + p ^ a)) : Submodule K _), F = merge n v y}
  have hQGr : Submodule.span K gens ≤ Gr (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) k := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨v, hv, D, hD, y, hy, rfl⟩
    exact merge_mem_Gr n (hVP hv) hD hy
  refine ⟨Submodule.span K gens, ?_, ?_, ?_⟩
  · -- row stability
    intro σ x hx
    induction hx using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨v, hv, D, hD, y, hy, rfl⟩ := hF
      rw [rowAct_merge]
      refine Submodule.subset_span ⟨rowAct σ v, hVrow σ v hv, D.map σ.toEmbedding,
        hasDom_rowAct σ hD, rowAct σ y, ?_, rfl⟩
      rw [compl_map]
      exact rowAct_mem_Soc_map σ hy
    | zero => rw [map_zero]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
    | smul c' x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · apply le_antisymm
    · rintro F ⟨q, rfl⟩
      exact zSum_mem _ _ _ _ hZGr hQGr q
    · intro g hg
      have hg' : g ∈ Gr (Lr n (n + p ^ a)) (Bl n (n + p ^ a)).toFinset k := by
        rwa [Bl_toFinset]
      have hrec := sum_putL_partL (Bl_nodup n (n + p ^ a)) hg'
      rw [Bl_toFinset] at hrec
      rw [← hrec]
      refine Submodule.sum_mem _ fun pat hpat => ?_
      have hpat' : IsPat (Bk n (n + p ^ a)) k pat := (Finset.mem_filter.mp hpat).2
      rw [← merge_single_slice n hg hpat']
      have hδ : (Pi.single pat 1 : Fn K (Fin b) (Fin (n + p ^ a))) ∈ PatSp n k := by
        intro t ht
        rw [Pi.single_apply] at ht
        split_ifs at ht with h'
        · rw [h']; exact hpat'
        · exact absurd rfl ht
      have hδD : HasDom (patDom pat) (Pi.single pat 1 : Fn K (Fin b) (Fin (n + p ^ a))) := by
        intro t ht
        rw [Pi.single_apply] at ht
        split_ifs at ht with h'
        · rw [h']
        · exact absurd rfl ht
      rw [← hVrange] at hδ
      obtain ⟨cv, hcv⟩ := hδ
      have hy := slice_mem (Bl_nodup n (n + p ^ a)) hg' (by rwa [Bl_toFinset])
      have hmem : ∀ i : Fin (p - 1 + 1), merge n (resD (patDom pat) (cv i : Fn K (Fin b) _))
          (partL (pairs (Bl n (n + p ^ a)) pat) g) ∈ Submodule.span K gens := fun i =>
        Submodule.subset_span ⟨_, hVres _ _ (cv i).2, patDom pat, hasDom_resD _ _, _, hy, rfl⟩
      have hsum : merge n (Pi.single pat 1) (partL (pairs (Bl n (n + p ^ a)) pat) g) =
          zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) (Submodule.span K gens)
            (fun i => ⟨_, hmem i⟩) := by
        rw [zSum_apply, ← resD_of_hasDom hδD, ← hcv, zSum_apply, map_sum, merge_sum_left]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hZres, Z_pow_merge]
      rw [hsum]
      exact LinearMap.mem_range_self _ _
  · -- injectivity, through the evaluations `ev_s`
    intro q q' hqq
    have h0 : zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) (Submodule.span K gens) (q - q') = 0 := by
      rw [map_sub, hqq, sub_self]
    have hev : ∀ s : Fin b → Option (Fin (n + p ^ a)), RetOnly n s →
        ∀ x ∈ Submodule.span K gens, evR n s x ∈ V := by
      intro s hs x hx
      induction hx using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨v, hv, D, hD, y, hy, rfl⟩ := hF
        rw [evR_merge n hs (hVP hv) hD hy.1]
        exact V.smul_mem _ hv
      | zero => rw [map_zero]; exact zero_mem _
      | add x x' _ _ hx hx' => rw [map_add]; exact add_mem hx hx'
      | smul c' x _ hx => rw [map_smul]; exact V.smul_mem _ hx
    have hd0 : ∀ i, ((q - q') i : Fn K (Fin b) (Fin (n + p ^ a))) = 0 := by
      intro i
      funext t
      rw [← evR_recover n (((q - q') i : Fn K (Fin b) (Fin (n + p ^ a)))) t]
      have hs := retOnly_retPart n t
      let e : Fin (p - 1 + 1) → V := fun j =>
        ⟨evR n (retPart n t) ((q - q') j), hev _ hs _ ((q - q') j).2⟩
      have he : zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) V e = 0 := by
        have h1 : zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) V e =
            evR n (retPart n t) (zSum (p - 1 + 1) (rhoFn (zEltP p a n c))
              (Submodule.span K gens) (q - q')) := by
          rw [zSum_apply, zSum_apply, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hevZ _ hs]
        rw [h1, h0, map_zero]
      have he0 : e = 0 := hVinj (he.trans (map_zero _).symm)
      have h2 := congrArg Subtype.val (congrFun he0 i)
      have h3 : evR n (retPart n t) (((q - q') i : Fn K (Fin b) (Fin (n + p ^ a)))) = 0 := h2
      rw [h3]
      rfl
    funext i
    have := hd0 i
    rw [Pi.sub_apply, Submodule.coe_sub, sub_eq_zero] at this
    exact Subtype.ext this

/-- **Theorem A modulo the pattern form of Prop. 6 and DCP_b** (CONDITIONAL). -/
theorem topWitnessHypothesis_of_prop6Pat_dcp (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ r a n : ℕ, r < p ^ a → 2 * r - 1 ≤ n → ∀ c : Fin a → L, Generic p c →
      ∀ b, 1 ≤ b → b ≤ r → Prop6PatHyp p (n := n) c b ∧ DCPHyp (K := L) b (n + p ^ a)) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  topWitnessHypothesis_of_prop6_dcp p L fun r a n hr hn c hc b hb hbr =>
    ⟨prop6Hyp_of_pat p c (H r a n hr hn c hc b hb hbr).1, (H r a n hr hn c hc b hb hbr).2⟩

end Reduction

end BExact
