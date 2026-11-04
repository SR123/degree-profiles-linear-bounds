/-
Agent D, round 4 (26 Sep 2026).  Interface: the rook-form DCP on the full board `Fin N × Fin N`
gives B's hypothesis `DCPHyp b N` (BTransC), restated verbatim here as `DCPHypB` (same body, same
constants `SocV`, `VpV`, `GV`, `TupleRelations`, `permRep`, `injTuples` from the verbatim copies of
B's `BLayer`/`BBridge` and the project's Stage 5).

* `Phi φ u v` : the matrix entry `⟨e_u, φ e_v⟩`; `Phi_comp` (`S_b`-invariance from `GV`).
* `Frk φ` : the rook function of `φ`; `Frk_rk` : `Frk φ (rk (tup u) (tup v)) = Phi φ u v`.
* `zb_Frk` : `Frk φ ∈ Z_b` (row lines from `φ(V') = 0` via `sum_dl_eq_delT`; column lines from
  `im φ ⊆ Soc`).
* `liftPerm`, `rhoFn_apply_sum` : realisers become elements of `K[S_N]`.
* `dcpHypB_of_dcpr` : `DCPR (Fin N) K b N → DCPHypB b N` (`1 ≤ b ≤ N`).
* **`dcpHypB_of_half`** : `DCPHypB b N` from `HALF` in the window (all other inputs proved).
* **`dcpHypB_le_two`** : `DCPHypB b N` for `1 ≤ b ≤ 2`, `b ≤ N`, unconditionally.
-/
import DCPBridge
import BLayer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ClaudeDCP

open Finset Function BExact DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 ClaudeCP

variable {K : Type} [Field K]

/-- **B's hypothesis `DCPHyp b N`** (BTransC.lean), restated verbatim. -/
def DCPHypB (b N : ℕ) : Prop :=
  ∀ φ : Module.End K (permRep K (injTuples b) N).V,
    (∀ v, φ v ∈ SocV K b N) → (∀ v ∈ VpV K b N, φ v = 0) → (∀ g ∈ GV K b N, g * φ = φ * g) →
    ∃ x ∈ TupleRelations K (b - 1) N, (permRep K (injTuples b) N).ρ.asAlgebraHom x = φ

section Delta

variable {b N : ℕ}

/-- The indicator function of a tuple. -/
def dl (t : Fin b → Option (Fin N)) : Fn K (Fin b) (Fin N) := fun t' => if t' = t then 1 else 0

theorem dl_mem_P {S : Finset (Fin b)} {t : Fin b → Option (Fin N)}
    (ht : Good S (univ : Finset (Fin N)) t) : dl (K := K) t ∈ P S (univ : Finset (Fin N)) := by
  intro t' h
  by_cases e : t' = t
  · rw [e]; exact ht
  · exact absurd (by simp [dl, e]) h

theorem embT_eq_tup (τ : (injTuples b).Rk N) : embT τ = tup (fun i => τ.1 i) := rfl

theorem ofFn_dl_embT (τ : (injTuples b).Rk N) :
    ofFn (dl (K := K) (embT τ)) = Finsupp.single τ 1 := by
  classical
  ext τ'
  rw [ofFn_apply, Finsupp.single_apply]
  simp only [dl]
  by_cases h : τ' = τ
  · subst h; simp
  · rw [if_neg (fun e => h (embT_injective e)), if_neg (Ne.symm h)]

theorem toFn_injective' : Injective (toFn (K := K) (b := b) (N := N)) :=
  fun f g h => by rw [← ofFn_toFn f, h, ofFn_toFn]

theorem tup_inj_of_good {v : Fin b → Fin N}
    (h : Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) (tup v)) : Injective v :=
  good_tup_inj h

/-- `Σ_{y free} e_{v[i := y]} = del_iᵀ e_{v without i}`. -/
theorem sum_dl_eq_delT {u v : Fin b → Fin N} (hu : Injective u) (hv : Injective v) (i : Fin b) :
    ∑ y ∈ (univ : Finset (Fin N)) \ colsOf (rk (tup u) (update (tup v) i none)),
      dl (K := K) (update (tup v) i (some y)) = delT i (dl (update (tup v) i none)) := by
  classical
  funext t
  rw [Finset.sum_apply, delT_apply]
  by_cases hc : Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t ∧
      update t i none = update (tup v) i none
  · obtain ⟨w, rfl⟩ := exists_tup hc.1
    have hw := good_tup_inj hc.1
    rw [if_pos hc.1]
    simp only [dl]
    rw [if_pos hc.2]
    have hwv : ∀ j, j ≠ i → w j = v j := by
      intro j hj
      have := congrFun hc.2 j
      simp only [update_of_ne hj, tup, Option.some.injEq] at this
      exact this
    have heq : tup w = update (tup v) i (some (w i)) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [tup]
      · rw [update_of_ne hj]; simp [tup, hwv j hj]
    rw [Finset.sum_eq_single (w i)]
    · rw [if_pos heq]
    · intro y _ hy
      rw [if_neg]
      intro h
      have := congrFun h i
      simp [tup] at this
      exact hy this.symm
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_sdiff, mem_colsOf_rk_erase hu]
      refine ⟨mem_univ _, ?_⟩
      rintro ⟨j, hj, hvj⟩
      exact hj (hw (by rw [hwv j hj, hvj]))
  · have hr : (if Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t then
        dl (K := K) (update (tup v) i none) (update t i none) else 0) = 0 := by
      split_ifs with hg
      · simp only [dl]
        rw [if_neg (fun h => hc ⟨hg, h⟩)]
      · rfl
    rw [hr]
    refine Finset.sum_eq_zero fun y hy => ?_
    simp only [dl]
    rw [if_neg]
    rintro rfl
    apply hc
    refine ⟨(good_update_iff hu (fun _ => mem_univ _) hv i y).mpr hy, ?_⟩
    rw [update_idem]

end Delta

section Matrix

variable {b N : ℕ}

/-- The matrix entry `⟨e_u, φ e_v⟩`. -/
noncomputable def Phi (φ : Module.End K (permRep K (injTuples b) N).V) (u v : Fin b → Fin N) : K :=
  toFn (φ (ofFn (dl (tup v)))) (tup u)

theorem Phi_comp (φ : Module.End K (permRep K (injTuples b) N).V)
    (hG : ∀ g ∈ GV K b N, g * φ = φ * g) (σ : Equiv.Perm (Fin b)) (u : Fin b → Fin N)
    {v : Fin b → Fin N} (hv : Injective v) :
    Phi φ (u ∘ σ) v = Phi φ u (v ∘ (σ⁻¹ : Equiv.Perm (Fin b))) := by
  have h := congrArg (fun T => T (ofFn (dl (K := K) (tup v)))) (hG (rowV K b N σ) ⟨σ, rfl⟩)
  simp only [Module.End.mul_apply] at h
  have hdl : rowV K b N σ (ofFn (dl (K := K) (tup v))) =
      ofFn (dl (K := K) (tup (v ∘ (σ⁻¹ : Equiv.Perm (Fin b))))) := by
    simp only [rowV, LinearMap.comp_apply]
    rw [toFn_ofFn (dl_mem_P (good_tup (fun _ => mem_univ _) hv))]
    congr 1
    funext t
    simp only [rowAct_apply, dl]
    have key : t ∘ σ = tup v ↔ t = tup (v ∘ (σ⁻¹ : Equiv.Perm (Fin b))) := by
      constructor
      · intro h
        funext j
        have := congrFun h (σ⁻¹ j)
        simpa [tup] using this
      · rintro rfl
        funext j
        simp [tup]
    by_cases hk : t ∘ σ = tup v
    · rw [if_pos hk, if_pos (key.mp hk)]
    · rw [if_neg hk, if_neg (fun h => hk (key.mpr h))]
  rw [hdl] at h
  unfold Phi
  rw [← h]
  simp only [rowV, LinearMap.comp_apply]
  rw [toFn_ofFn (rowAct_mem_P σ (toFn_mem_P _)), rowAct_apply]
  rfl

theorem Phi_invariant (φ : Module.End K (permRep K (injTuples b) N).V)
    (hG : ∀ g ∈ GV K b N, g * φ = φ * g) {u v u' v' : Fin b → Fin N} (hu' : Injective u')
    (hv : Injective v) (h : rk (tup u) (tup v) = rk (tup u') (tup v')) :
    Phi φ u v = Phi φ u' v' := by
  obtain ⟨σ, rfl, rfl⟩ := exists_perm_of_rk_eq hu' h
  rw [Phi_comp φ hG σ u (hv.comp σ.injective)]
  have e : (v ∘ σ) ∘ (σ⁻¹ : Equiv.Perm (Fin b)) = v := by
    funext j
    simp
  rw [e]

/-- The rook function of `φ`. -/
noncomputable def Frk (φ : Module.End K (permRep K (injTuples b) N).V)
    (ρ : Finset (Fin N × Fin N)) : K :=
  if h : ρ.card = Fintype.card (Fin b) then
    Phi φ (fun i => (enumE ρ h i).1.1) (fun i => (enumE ρ h i).1.2) else 0

theorem Frk_rk (φ : Module.End K (permRep K (injTuples b) N).V)
    (hG : ∀ g ∈ GV K b N, g * φ = φ * g) {u v : Fin b → Fin N} (hu : Injective u)
    (hv : Injective v) : Frk φ (rk (tup u) (tup v)) = Phi φ u v := by
  have h : (rk (tup u) (tup v)).card = Fintype.card (Fin b) := card_rk_tup hu v
  unfold Frk
  rw [dif_pos h]
  have hρ : IsRook (rk (tup u) (tup v)) :=
    (onBoard_rk_tup (R := univ) (C := univ) (fun _ => mem_univ _) hu (fun _ => mem_univ _) hv).1
  exact Phi_invariant φ hG hu (enum_injective hρ _).2 (rk_enum _ _)

theorem mem_Soc_of_SocV {φ : Module.End K (permRep K (injTuples b) N).V}
    (hSoc : ∀ v, φ v ∈ SocV K b N) (w : (permRep K (injTuples b) N).V) :
    toFn (φ w) ∈ Soc (univ : Finset (Fin b)) univ (univ : Finset (Fin N)) := by
  have := hSoc w
  rw [SocV, Submodule.mem_comap] at this
  exact this

/-- `Frk φ ∈ Z_b` of the full board. -/
theorem zb_Frk (φ : Module.End K (permRep K (injTuples b) N).V)
    (hSoc : ∀ v, φ v ∈ SocV K b N) (hV : ∀ v ∈ VpV K b N, φ v = 0)
    (hG : ∀ g ∈ GV K b N, g * φ = φ * g) :
    ZB (univ : Finset (Fin N)) univ b (Frk φ) := by
  have hk : Fintype.card (Fin b) = b := Fintype.card_fin b
  refine ⟨fun ρ' hρ' hcard x hx hxr => ?_, fun ρ' hρ' hcard y hy hyc => ?_⟩
  · -- row lines: `φ` kills `V'`
    by_cases hne : ((univ : Finset (Fin N)) \ colsOf ρ').Nonempty
    · obtain ⟨y1, hy1⟩ := hne
      have hy1c := (Finset.mem_sdiff.mp hy1).2
      have hon := hρ'.insert hx hxr (mem_univ y1) hy1c
      obtain ⟨u, v, -, hu, -, hv, hρeq⟩ := exists_enum (ι := Fin b) hon
        (by rw [card_insert_cell hxr, hcard, hk])
      obtain ⟨i, hui, hvi⟩ : ∃ i, u i = x ∧ v i = y1 := by
        have : (x, y1) ∈ rk (tup u) (tup v) := by rw [hρeq]; exact Finset.mem_insert_self _ _
        exact mem_rk_tup.mp this
      have hρ'eq : ρ' = rk (tup u) (update (tup v) i none) := by
        rw [rk_erase_col hu, hρeq, hui, hvi, Finset.erase_insert (fun h => hxr (rowsOf_mem h))]
      have hterm : ∀ y ∈ (univ : Finset (Fin N)) \ colsOf ρ', Frk φ (insert (x, y) ρ') =
          toFn (φ (ofFn (dl (K := K) (update (tup v) i (some y))))) (tup u) := by
        intro y hy
        have hy' : ∀ j, j ≠ i → v j ≠ y := fun j hj h => (Finset.mem_sdiff.mp hy).2 (by
          rw [hρ'eq, mem_colsOf_rk_erase hu]; exact ⟨j, hj, h⟩)
        rw [hρ'eq, ← hui, ← rk_update_col, ← tup_update, Frk_rk φ hG hu (injective_update hv hy')]
        rfl
      rw [Finset.sum_congr rfl hterm]
      have hlin : ∑ y ∈ (univ : Finset (Fin N)) \ colsOf ρ',
          toFn (φ (ofFn (dl (K := K) (update (tup v) i (some y))))) (tup u) =
          toFn (φ (ofFn (∑ y ∈ (univ : Finset (Fin N)) \ colsOf ρ',
            dl (K := K) (update (tup v) i (some y))))) (tup u) := by
        rw [map_sum, map_sum, map_sum, Finset.sum_apply]
      rw [hlin, hρ'eq, sum_dl_eq_delT hu hv i]
      have hgood0 : Good (univ.erase i) (univ : Finset (Fin N)) (update (tup v) i none) := by
        refine ⟨fun j => ?_, fun j z hz => mem_univ z, fun j k z hj hk => ?_⟩
        · by_cases hj : j = i
          · subst hj; simp
          · rw [update_of_ne hj]; simp [tup, hj]
        · have hji : j ≠ i := by rintro rfl; simp at hj
          have hki : k ≠ i := by rintro rfl; simp at hk
          rw [update_of_ne hji] at hj
          rw [update_of_ne hki] at hk
          simp only [tup, Option.some.injEq] at hj hk
          exact hv (hj.trans hk.symm)
      have hPdel : delT i (dl (K := K) (update (tup v) i none)) ∈
          P (univ : Finset (Fin b)) (univ : Finset (Fin N)) := by
        intro t ht
        rw [delT_apply] at ht
        by_contra hg
        exact ht (if_neg hg)
      have hmem : ofFn (delT i (dl (K := K) (update (tup v) i none))) ∈ VpV K b N := by
        rw [VpV, Submodule.mem_comap, toFn_ofFn hPdel]
        exact Submodule.subset_span ⟨i, _, dl_mem_P hgood0, rfl⟩
      rw [hV _ hmem, map_zero]
      rfl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
  · -- column lines: `im φ ⊆ Soc`
    by_cases hne : ((univ : Finset (Fin N)) \ rowsOf ρ').Nonempty
    · obtain ⟨x1, hx1⟩ := hne
      have hx1r := (Finset.mem_sdiff.mp hx1).2
      have hon := hρ'.insert (mem_univ x1) hx1r hy hyc
      obtain ⟨u, v, -, hu, -, hv, hρeq⟩ := exists_enum (ι := Fin b) hon
        (by rw [card_insert_cell hx1r, hcard, hk])
      obtain ⟨i, hui, hvi⟩ : ∃ i, u i = x1 ∧ v i = y := by
        have : (x1, y) ∈ rk (tup u) (tup v) := by rw [hρeq]; exact Finset.mem_insert_self _ _
        exact mem_rk_tup.mp this
      have hρ'eq : ρ' = rk (update (tup u) i none) (tup v) := by
        rw [rk_erase_row u hv, hρeq, hui, hvi, Finset.erase_insert (fun h => hx1r (rowsOf_mem h))]
      set G := toFn (φ (ofFn (dl (K := K) (tup v)))) with hGdef
      have hGs := mem_Soc_of_SocV hSoc (ofFn (dl (K := K) (tup v)))
      rw [← hGdef] at hGs
      have hset : (univ : Finset (Fin N)) \ rowsOf ρ' =
          (univ : Finset (Fin N)) \ colsOf (rk (tup v) (update (tup u) i none)) := by
        ext z
        rw [Finset.mem_sdiff, Finset.mem_sdiff, hρ'eq, mem_rowsOf_rk_erase hv,
          mem_colsOf_rk_erase hv]
      have hterm : ∀ x ∈ (univ : Finset (Fin N)) \ rowsOf ρ', Frk φ (insert (x, y) ρ') =
          G (update (tup u) i (some x)) := by
        intro x hx
        have hx' : ∀ j, j ≠ i → u j ≠ x := fun j hj h => (Finset.mem_sdiff.mp hx).2 (by
          rw [hρ'eq, mem_rowsOf_rk_erase hv]; exact ⟨j, hj, h⟩)
        rw [hρ'eq, ← hvi, ← rk_update_row, ← tup_update, Frk_rk φ hG (injective_update hu hx') hv]
        rfl
      rw [Finset.sum_congr rfl hterm]
      have hdel : ∑ x, part i x G (update (tup u) i none) = 0 := by
        have := congrFun (hGs.2 i (mem_univ i)) (update (tup u) i none)
        rw [del_apply] at this
        exact this
      refine Eq.trans ?_ hdel
      rw [Finset.sum_subset (Finset.subset_univ ((univ : Finset (Fin N)) \ rowsOf ρ'))]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [part_apply, if_pos (by simp), update_idem]
      · intro x _ hx
        by_contra hne0
        have hgood := hGs.1 _ hne0
        rw [good_update_iff hv (fun _ => mem_univ _) hu i x, ← hset] at hgood
        exact hx hgood
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]

end Matrix

/-! ### From realisers to `K[S_N]` -/

section Lift

variable {N : ℕ}

/-- Extend a permutation of `Fin N` to `ℕ` by the identity. -/
def extN (w : Equiv.Perm (Fin N)) : Equiv.Perm ℕ where
  toFun n := if h : n < N then (w ⟨n, h⟩ : ℕ) else n
  invFun n := if h : n < N then (w.symm ⟨n, h⟩ : ℕ) else n
  left_inv n := by
    by_cases h : n < N
    · simp [h]
    · simp [h]
  right_inv n := by
    by_cases h : n < N
    · simp [h]
    · simp [h]

/-- The element of `S_N = Sfin N` induced by a permutation of `Fin N`. -/
def liftPerm (w : Equiv.Perm (Fin N)) : Sfin N :=
  ⟨extN w, fun i hi => by simp [extN, not_lt.mpr hi]⟩

theorem finPerm_liftPerm (w : Equiv.Perm (Fin N)) : finPerm (liftPerm w) = w := by
  ext x
  rw [finPerm_val]
  simp [liftPerm, extN]

/-- The group-algebra element of a coefficient function. -/
noncomputable def algOf (c : Equiv.Perm (Fin N) → K) : MonoidAlgebra K (Sfin N) :=
  ∑ w, MonoidAlgebra.single (liftPerm w) (c w)

theorem rhoFn_algOf_apply {ι : Type} [Fintype ι] [DecidableEq ι] (c : Equiv.Perm (Fin N) → K)
    (F : Fn K ι (Fin N)) (s : ι → Option (Fin N)) :
    rhoFn (algOf c) F s = ∑ w, c w * F (fun i => (s i).map w.symm) := by
  unfold algOf
  rw [map_sum, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [rhoFn_single, finPerm_liftPerm, LinearMap.smul_apply, Pi.smul_apply, labAct_apply,
    smul_eq_mul]

end Lift

theorem chi_rk_tup {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (w : Equiv.Perm α) (u v : ι → α) :
    chi (K := K) w (rk (tup u) (tup v)) = if (fun i => w.symm (u i)) = v then 1 else 0 := by
  unfold chi
  have key : (∀ p ∈ rk (tup u) (tup v), w p.2 = p.1) ↔ (fun i => w.symm (u i)) = v := by
    constructor
    · intro h
      funext i
      have := h (u i, v i) (mem_rk_tup.mpr ⟨i, rfl, rfl⟩)
      simp only at this
      rw [← this, Equiv.symm_apply_apply]
    · intro h p hp
      obtain ⟨i, h1, h2⟩ := mem_rk_tup.mp hp
      rw [← h1, ← h2, ← congrFun h i]
      simp
  by_cases h : (fun i => w.symm (u i)) = v
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]

/-- Downward vanishing of a realiser. -/
theorem realFn_zero_down {α : Type} [Fintype α] [DecidableEq α] {R C : Finset α}
    {c : Equiv.Perm α → K} (hc : FitsAll R C c) {m : ℕ} (hm : m ≤ C.card)
    (h0 : ∀ ρ, OnBoard R C ρ → ρ.card = m → realFn c ρ = 0) :
    ∀ d ρ, OnBoard R C ρ → ρ.card + d = m → realFn c ρ = 0 := by
  intro d
  induction d with
  | zero => intro ρ hρ hcard; exact h0 ρ hρ (by omega)
  | succ d ih =>
    intro ρ hρ hcard
    have hlt : (colsOf ρ).card < C.card := by rw [card_colsOf hρ.1]; omega
    obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    rw [← sum_col_realFn hc hy hyc]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxR, hxr⟩ := Finset.mem_sdiff.mp hx
    exact ih _ (hρ.insert hxR hxr hy hyc) (by rw [card_insert_cell hxr]; omega)

/-- **Interface.** DCP in rook form on the full `N × N` board gives B's `DCPHyp b N`. -/
theorem dcpHypB_of_dcpr {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) (hD : DCPR (Fin N) K b N) :
    DCPHypB (K := K) b N := by
  intro φ hSoc hV hG
  have hk : Fintype.card (Fin b) = b := Fintype.card_fin b
  have hZ := zb_Frk φ hSoc hV hG
  obtain ⟨c, hcfit, hc⟩ := hD univ univ (Finset.card_fin N) (Finset.card_fin N) (Frk φ) hZ
  -- lower levels vanish
  have hlow : ∀ ρ, OnBoard (univ : Finset (Fin N)) univ ρ → ρ.card < b → realFn c ρ = 0 := by
    have h1 : ∀ ρ, OnBoard (univ : Finset (Fin N)) univ ρ → ρ.card = b - 1 → realFn c ρ = 0 :=
      fun ρ hρ hcard => realFn_eq_zero_below hcfit hc hZ.2 hρ (by omega)
        (by rw [Finset.card_fin]; omega)
    intro ρ hρ hlt
    exact realFn_zero_down hcfit (by rw [Finset.card_fin]; omega) h1 (b - 1 - ρ.card) ρ hρ
      (by omega)
  refine ⟨algOf c, fun b' hb' => ?_, ?_⟩
  · -- tuple relation of support `b - 1`
    rw [asAlgebraHom_eq_zero_iff]
    intro F hF
    funext s
    rw [Pi.zero_apply]
    by_cases hs : Good (univ : Finset (Fin b')) (univ : Finset (Fin N)) s
    · obtain ⟨u', rfl⟩ := exists_tup hs
      have hu' := good_tup_inj hs
      rw [rhoFn_algOf_apply]
      have hexp : ∀ w : Equiv.Perm (Fin N), c w * F (fun i => (tup u' i).map w.symm) =
          ∑ v' : Fin b' → Fin N, c w * chi w (rk (tup u') (tup v')) * F (tup v') := by
        intro w
        simp_rw [chi_rk_tup, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        rw [if_pos (mem_univ _)]
        rfl
      rw [Finset.sum_congr rfl fun w _ => hexp w, Finset.sum_comm]
      refine Finset.sum_eq_zero fun v' _ => ?_
      rw [← Finset.sum_mul]
      by_cases hv' : Injective v'
      · have : realFn c (rk (tup u') (tup v')) = 0 :=
          hlow _ (onBoard_rk_tup (fun _ => mem_univ _) hu' (fun _ => mem_univ _) hv')
            (by rw [card_rk_tup hu', Fintype.card_fin]; omega)
        unfold realFn at this
        rw [this, zero_mul]
      · have : F (tup v') = 0 := by
          by_contra hne
          exact hv' (good_tup_inj (hF _ hne))
        rw [this, mul_zero]
    · by_contra hne
      exact hs (rhoFn_mem_P hF s hne)
  · -- `ρ_b (algOf c) = φ`
    apply Finsupp.lhom_ext
    intro τ a
    rw [← Finsupp.smul_single_one, map_smul, map_smul]
    congr 1
    apply toFn_injective'
    funext s
    rw [toFn_asAlgebraHom]
    have hτ : toFn (Finsupp.single τ (1 : K)) = dl (embT τ) := by
      rw [← ofFn_dl_embT, toFn_ofFn (dl_mem_P (embT_good τ))]
    have hτinj : Injective (fun i => τ.1 i) := good_tup_inj (embT_good τ)
    by_cases hs : Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) s
    · obtain ⟨u, rfl⟩ := exists_tup hs
      have hu := good_tup_inj hs
      rw [hτ, rhoFn_algOf_apply]
      have hterm : ∀ w : Equiv.Perm (Fin N), c w * dl (K := K) (embT τ)
          (fun i => (tup u i).map w.symm) = c w * chi w (rk (tup u) (tup fun i => τ.1 i)) := by
        intro w
        rw [chi_rk_tup, embT_eq_tup]
        simp only [dl]
        congr 1
        by_cases h : (fun i => w.symm (u i)) = fun i => τ.1 i
        · rw [if_pos h, if_pos (by rw [← h]; rfl)]
        · rw [if_neg h, if_neg]
          intro h'
          apply h
          funext i
          have := congrFun h' i
          simpa [tup] using this
      rw [Finset.sum_congr rfl fun w _ => hterm w]
      have hval := hc _ (onBoard_rk_tup (fun _ => mem_univ _) hu (fun _ => mem_univ _) hτinj)
        (by rw [card_rk_tup hu, hk])
      unfold realFn at hval
      rw [← hval, Frk_rk φ hG hu hτinj, Phi, ← embT_eq_tup, ofFn_dl_embT]
    · have h1 : toFn (φ (Finsupp.single τ 1)) s = 0 := by
        by_contra hne
        exact hs (toFn_mem_P _ s hne)
      rw [h1]
      by_contra hne
      exact hs (rhoFn_mem_P (toFn_mem_P _) s hne)

/-- **`DCPHyp b N` from HALF in the window** (`1 ≤ b ≤ N`); all other inputs are proved. -/
theorem dcpHypB_of_half {b N : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N)
    (hhalf : ∀ b' M, b' ≤ b → b' + 2 ≤ M → M + 1 ≤ 2 * b' → HALF (Fin N) K b' M) :
    DCPHypB (K := K) b N :=
  dcpHypB_of_dcpr hb hbN (dcpr_of_halfWindow b hhalf N)

/-- **`DCPHyp b N` for `b ≤ 2`, unconditionally** (`1 ≤ b ≤ N`). -/
theorem dcpHypB_le_two {b N : ℕ} (hb : 1 ≤ b) (hb2 : b ≤ 2) (hbN : b ≤ N) :
    DCPHypB (K := K) b N :=
  dcpHypB_of_dcpr hb hbN (dcpr_le_two_uncond hb2 N)

end ClaudeDCP
