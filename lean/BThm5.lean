/-
Agent B, round 3 (26 Sep 2026).  Theorem 5 and (P1), (T′_soc) of Cor. 6 in the concrete
setting, CONDITIONAL on Prop. 6 (freeness of `gr_k` over `K⟨g⟩` with an `S_b`-stable complement).

Setting: rows `Fin b`, labels `Fin N`, `N = n + p^a`; retained labels `Lr = {x < n}`, block
`B = {x ≥ n}`; `Z = rhoFn (zEltP p a n c)` (the paper's `z` on `Fn`), `u = Z^(p-1)`.
* `labAct` of a block permutation fixes `Lr` pointwise, preserves `B`; hence `Z` preserves the
  filtration `Filt k`, the quotients `Gr k`, commutes with `topPart k` and with row permutations,
  kills functions with retained labels only, and maps everything into `PB` (functions vanishing on
  tuples without block labels).  `Z^p = 0` (`Z_pow`).
* `Prop6Hyp` (the hypothesis): for `1 ≤ k ≤ b`, `Gr k = ⊕_{i<p} Z^i Q₀` with `Q₀` row-stable.
* `thm5_concrete`: under `Prop6Hyp` and `n ≥ 2b - 1`,
  `Soc_b(N) = Soc_b(n) ⊕ (⊕_{i<p} Z^i C)` with `C` row-stable (by `thm5_step` along `Filt k`,
  sections from Prop. 4(b) upgraded by Lemma 5).
* `P1_concrete`, `Tsoc_concrete`: (P1) and (T′_soc) for `Soc_b(N)`.
-/
import BProp4
import BCor6
import BLayer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 ClaudeCP DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ConcreteM5

variable {K : Type} [Field K]

/-! ### Retained labels, block labels -/

section Labels

variable (n N : ℕ)

/-- Retained labels `{x < n}`. -/
def Lr : Finset (Fin N) := univ.filter (fun x => x.val < n)

/-- Block labels `{x ≥ n}`. -/
def Bk : Finset (Fin N) := univ.filter (fun x => n ≤ x.val)

/-- The block labels as a list. -/
def Bl : List (Fin N) := (List.finRange N).filter (fun x => n ≤ x.val)

theorem Bl_nodup : (Bl n N).Nodup := (List.nodup_finRange N).filter _

theorem Bl_toFinset : (Bl n N).toFinset = Bk n N := by
  ext x
  simp [Bl, Bk]

theorem Lr_disjoint : Disjoint (Lr n N) (Bk n N) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Lr, Bk, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  omega

theorem Lr_union : Lr n N ∪ Bk n N = univ := by
  ext x
  simp only [Lr, Bk, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  omega

theorem Lr_card (h : n ≤ N) : (Lr n N).card = n := by
  rw [Lr]
  have : (univ.filter (fun x : Fin N => x.val < n)) = (Finset.range n).attachFin
      (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) h) := by
    ext x
    simp
  rw [this, Finset.card_attachFin, Finset.card_range]

end Labels

/-! ### Block permutations -/

section BlockPerm

variable {b N : ℕ} {n : ℕ}

/-- A label permutation fixing the retained labels. -/
def FixesLr (n : ℕ) (π : Equiv.Perm (Fin N)) : Prop := ∀ x : Fin N, x.val < n → π x = x

theorem FixesLr.symm {π : Equiv.Perm (Fin N)} (h : FixesLr n π) : FixesLr n π.symm := by
  intro x hx
  conv_lhs => rw [← h x hx]
  exact π.symm_apply_apply x

theorem FixesLr.block {π : Equiv.Perm (Fin N)} (h : FixesLr n π) {x : Fin N} (hx : n ≤ x.val) :
    n ≤ (π x).val := by
  by_contra h'
  push_neg at h'
  have h1 := h (π x) h'
  exact absurd (π.injective h1 ▸ hx) (by omega)

theorem FixesLr.mem_Bk_iff {π : Equiv.Perm (Fin N)} (h : FixesLr n π) (x : Fin N) :
    π x ∈ Bk n N ↔ x ∈ Bk n N := by
  simp only [Bk, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    by_contra h'
    push_neg at h'
    rw [h x h'] at hx
    omega
  · exact FixesLr.block h

theorem FixesLr.blockRows_eq {π : Equiv.Perm (Fin N)} (h : FixesLr n π) (t : Fin b → Option (Fin N)) :
    blockRows (Bk n N) (fun i => (t i).map π.symm) = blockRows (Bk n N) t := by
  ext i
  rw [mem_blockRows, mem_blockRows]
  constructor
  · rintro ⟨x, hx, hti⟩
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hti
    exact ⟨y, ((FixesLr.mem_Bk_iff (FixesLr.symm h)) y).mp hx, hy⟩
  · rintro ⟨x, hx, hti⟩
    exact ⟨π.symm x, ((FixesLr.mem_Bk_iff (FixesLr.symm h)) x).mpr hx, by rw [hti]; rfl⟩

theorem FixesLr.nb_eq {π : Equiv.Perm (Fin N)} (h : FixesLr n π) (t : Fin b → Option (Fin N)) :
    nb (Bk n N) (fun i => (t i).map π.symm) = nb (Bk n N) t := by
  unfold BExact.nb
  rw [FixesLr.blockRows_eq h]

/-- A tuple without block labels is fixed. -/
theorem FixesLr.fix_tuple {π : Equiv.Perm (Fin N)} (h : FixesLr n π) {t : Fin b → Option (Fin N)}
    (ht : nb (Bk n N) t = 0) : (fun i => (t i).map π.symm) = t := by
  funext i
  cases hti : t i with
  | none => rfl
  | some x =>
    have hx : x.val < n := by
      by_contra h'
      push_neg at h'
      have : i ∈ blockRows (Bk n N) t := mem_blockRows.mpr ⟨x, by simp [Bk, h'], hti⟩
      unfold BExact.nb at ht
      rw [Finset.card_eq_zero] at ht
      rw [ht] at this
      exact Finset.notMem_empty i this
    simp [FixesLr.symm h x hx]

theorem FixesLr.topPart_comm {π : Equiv.Perm (Fin N)} (h : FixesLr n π) (k : ℕ) :
    labAct π * topPart (Bk n N) k = (topPart (Bk n N) k * labAct π :
      Module.End K (Fn K (Fin b) (Fin N))) := by
  apply LinearMap.ext
  intro F
  funext t
  simp only [Module.End.mul_apply, labAct_apply, topPart_apply, FixesLr.nb_eq h]

theorem FixesLr.mem_Filt {π : Equiv.Perm (Fin N)} (h : FixesLr n π) {k : ℕ}
    {F : Fn K (Fin b) (Fin N)} (hF : F ∈ Filt (Lr n N) (Bk n N) k) :
    labAct π F ∈ Filt (Lr n N) (Bk n N) k := by
  refine ⟨?_, fun t ht => ?_⟩
  · have := labAct_mem_Soc hF.1 π
    rw [Lr_union, Finset.map_univ_equiv] at this
    rw [Lr_union]
    exact this
  · rw [labAct_apply]
    exact hF.2 _ (by rw [FixesLr.nb_eq h]; exact ht)

theorem FixesLr.delRet_comm {π : Equiv.Perm (Fin N)} (h : FixesLr n π) (i : Fin b) :
    labAct π * delRet (Lr n N) i = (delRet (Lr n N) i * labAct π :
      Module.End K (Fn K (Fin b) (Fin N))) := by
  simp only [BExact.delRet, Finset.mul_sum, Finset.sum_mul, labAct_part]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.val < n := by simpa [Lr] using hx
  rw [h x hx']

theorem FixesLr.mem_Gr {π : Equiv.Perm (Fin N)} (h : FixesLr n π) {k : ℕ}
    {F : Fn K (Fin b) (Fin N)} (hF : F ∈ Gr (Lr n N) (Bk n N) k) :
    labAct π F ∈ Gr (Lr n N) (Bk n N) k := by
  refine ⟨?_, fun t ht => ?_, fun i => ?_⟩
  · have := labAct_mem_P hF.1 π
    rw [Lr_union, Finset.map_univ_equiv] at this
    rw [Lr_union]
    exact this
  · rw [labAct_apply]
    exact hF.2.1 _ (by rw [FixesLr.nb_eq h]; exact ht)
  · rw [← Module.End.mul_apply, ← FixesLr.delRet_comm h, Module.End.mul_apply, hF.2.2 i, map_zero]

/-- Functions vanishing on tuples without block labels. -/
def PB (n N b : ℕ) : Submodule K (Fn K (Fin b) (Fin N)) where
  carrier := {F | ∀ t, nb (Bk n N) t = 0 → F t = 0}
  add_mem' hF hG t ht := by
    show _ + _ = (0 : K)
    rw [hF t ht, hG t ht, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c F hF t ht := by
    show c * F t = 0
    rw [hF t ht, mul_zero]

/-- Functions supported on tuples without block labels. -/
def P0 (n N b : ℕ) : Submodule K (Fn K (Fin b) (Fin N)) where
  carrier := {F | ∀ t, 1 ≤ nb (Bk n N) t → F t = 0}
  add_mem' hF hG t ht := by
    show _ + _ = (0 : K)
    rw [hF t ht, hG t ht, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c F hF t ht := by
    show c * F t = 0
    rw [hF t ht, mul_zero]

theorem FixesLr.fix_P0 {π : Equiv.Perm (Fin N)} (h : FixesLr n π) {F : Fn K (Fin b) (Fin N)}
    (hF : F ∈ P0 n N b) : labAct π F = F := by
  funext t
  rw [labAct_apply]
  by_cases ht : nb (Bk n N) t = 0
  · rw [FixesLr.fix_tuple h ht]
  · rw [hF t (by omega), hF _ (by rw [FixesLr.nb_eq h]; omega)]

theorem FixesLr.sub_mem_PB {π : Equiv.Perm (Fin N)} (h : FixesLr n π) (F : Fn K (Fin b) (Fin N)) :
    labAct π F - F ∈ PB n N b := by
  intro t ht
  show labAct π F t - F t = 0
  rw [labAct_apply, FixesLr.fix_tuple h ht, sub_self]

end BlockPerm

/-! ### The operator `Z` -/

section Zop

variable (p : ℕ) [Fact p.Prime] {a n b : ℕ}

theorem sigma_fixesLr (i : Fin a) : FixesLr n (finPerm (σgen p a n i)) := by
  intro x hx
  apply Fin.ext
  rw [finPerm_val]
  show blockHom p a n _ x.val = x.val
  exact blockHom_apply_not_block p a n _ (by omega)

/-- `Z = rhoFn z = Σ c_i (labAct σ_i - 1)`. -/
theorem Z_eq (c : Fin a → K) :
    rhoFn (ι := Fin b) (zEltP p a n c) =
      ∑ i, c i • (labAct (finPerm (σgen p a n i)) - 1) := by
  rw [zEltP, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_sub, rhoFn_single, one_smul, map_one]

/-- Any `T` commuting with the block permutations commutes with `Z`. -/
theorem Z_comm (c : Fin a → K) (T : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))))
    (hT : ∀ π : Equiv.Perm (Fin (n + p ^ a)), FixesLr n π → T * labAct π = labAct π * T) :
    T * rhoFn (zEltP p a n c) = rhoFn (zEltP p a n c) * T := by
  rw [Z_eq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul,
    hT _ (sigma_fixesLr p i)]

theorem Z_mem {c : Fin a → K} (Sub : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))))
    (hS : ∀ π : Equiv.Perm (Fin (n + p ^ a)), FixesLr n π → ∀ F ∈ Sub, labAct π F ∈ Sub)
    {F : Fn K (Fin b) (Fin (n + p ^ a))} (hF : F ∈ Sub) : rhoFn (zEltP p a n c) F ∈ Sub := by
  rw [Z_eq, LinearMap.sum_apply]
  refine sum_mem fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact Sub.smul_mem _ (Sub.sub_mem (hS _ (sigma_fixesLr p i) F hF) hF)

theorem Z_P0 {c : Fin a → K} {F : Fn K (Fin b) (Fin (n + p ^ a))} (hF : F ∈ P0 n (n + p ^ a) b) :
    rhoFn (zEltP p a n c) F = 0 := by
  rw [Z_eq, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    FixesLr.fix_P0 (sigma_fixesLr p i) hF, sub_self, smul_zero]

theorem Z_PB (c : Fin a → K) (F : Fn K (Fin b) (Fin (n + p ^ a))) :
    rhoFn (zEltP p a n c) F ∈ PB n (n + p ^ a) b := by
  rw [Z_eq, LinearMap.sum_apply]
  refine sum_mem fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact Submodule.smul_mem _ _ (FixesLr.sub_mem_PB (sigma_fixesLr p i) F)

variable [CharP K p]

theorem Z_pow (c : Fin a → K) :
    (rhoFn (ι := Fin b) (zEltP p a n c)) ^ (p - 1 + 1) = 0 := by
  have h := zOp_pow_p a n c (labHom (K := K) (ι := Fin b) (N := n + p ^ a))
  have e : rhoFn (ι := Fin b) (zEltP p a n c) = zOp (σgen p a n) c labHom := by
    rw [Z_eq, zOp]
    rfl
  rw [e]
  exact h

end Zop

/-! ### Theorem 5 (conditional on Prop. 6) -/

section Thm5

variable (p : ℕ) [Fact p.Prime] [CharP K p] (a n b : ℕ) (c : Fin a → K)

/-- **Prop. 6 at level `b`** (the CONDITIONAL input of this file): for `1 ≤ k ≤ b`,
`gr_k = ⊕_{i<p} Z^i Q₀` with `Q₀` stable under row permutations. -/
def Prop6Hyp : Prop :=
  ∀ k, 1 ≤ k → k ≤ b → ∃ Q₀ : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))),
    (∀ σ : Equiv.Perm (Fin b), ∀ x ∈ Q₀, rowAct σ x ∈ Q₀) ∧
    LinearMap.range (zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) Q₀) =
      Gr (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) k ∧
    Function.Injective (zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) Q₀)

variable {p a n b c}

theorem Filt_mono {Lr B : Finset (Fin (n + p ^ a))} {k k' : ℕ} (h : k ≤ k') :
    Filt (ι := Fin b) (R := K) Lr B k ≤ Filt Lr B k' :=
  fun _ hF => ⟨hF.1, fun t ht => hF.2 t (by omega)⟩

theorem Filt_top :
    (Soc (univ : Finset (Fin b)) univ univ : Submodule K (Fn K (Fin b) (Fin (n + p ^ a)))) ≤
      Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) b := by
  intro F hF
  refine ⟨by rw [Lr_union]; exact hF, fun t ht => ?_⟩
  exfalso
  have := Finset.card_le_univ (blockRows (Bk n (n + p ^ a)) t)
  rw [Fintype.card_fin] at this
  unfold BExact.nb at ht
  omega

theorem Filt_le_Soc (k : ℕ) :
    Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) k ≤
      (Soc (univ : Finset (Fin b)) univ univ : Submodule K (Fn K (Fin b) (Fin (n + p ^ a)))) :=
  fun F hF => by rw [← Lr_union n (n + p ^ a)]; exact hF.1

theorem Filt_zero_le_P0 :
    Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) 0 ≤ (P0 n (n + p ^ a) b : Submodule K _) :=
  fun F hF t ht => hF.2 t (by omega)

/-- **Theorem 5 along the filtration** (conditional on Prop. 6): for `k ≤ b`,
`Filt k = Filt 0 ⊕ (⊕_{i<p} Z^i C_k)` with `C_k` row-stable. -/
theorem thm5_filt (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1) :
    ∀ k, k ≤ b → ∃ C : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))),
      (∀ σ : Equiv.Perm (Fin b), ∀ x ∈ C, rowAct σ x ∈ C) ∧
      C ≤ Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) k ∧
      (∀ s ∈ Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) k,
        ∃ s₀ ∈ Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) 0,
          ∃ x ∈ LinearMap.range (zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) C), s = s₀ + x) ∧
      (∀ s₀ ∈ Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) 0,
        ∀ x ∈ LinearMap.range (zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) C), s₀ + x = 0 → s₀ = 0) ∧
      Function.Injective (zSum (p - 1 + 1) (rhoFn (zEltP p a n c)) C) := by
  set N := n + p ^ a
  set Z := rhoFn (ι := Fin b) (zEltP p a n c)
  have hN : 0 < N := by
    have : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
    omega
  let Ch : Chooser (Fin N) := Chooser.ofDefault ⟨0, hN⟩
  have hZp : ∀ e : Fn K (Fin b) (Fin N), (Z ^ (p - 1 + 1)) e = 0 := fun e => by
    rw [Z_pow]
    rfl
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨⊥, fun σ x hx => by rw [(Submodule.mem_bot K).mp hx, map_zero]; exact zero_mem _,
      bot_le, fun s hs => ⟨s, hs, 0, zero_mem _, (add_zero s).symm⟩, ?_, ?_⟩
    · intro s₀ _ x hx h0
      obtain ⟨v, rfl⟩ := hx
      have hv : v = 0 := funext fun i => Subtype.ext ((Submodule.mem_bot K).mp (v i).2)
      rw [hv, map_zero, add_zero] at h0
      exact h0
    · intro v v' _
      funext i
      exact Subtype.ext (((Submodule.mem_bot K).mp (v i).2).trans
        ((Submodule.mem_bot K).mp (v' i).2).symm)
  | succ k ih =>
    intro hk
    obtain ⟨C, hCrow, hCF, hF, hFind, hinjC⟩ := ih (by omega)
    obtain ⟨Q₀, hQ₀row, hQ, hinjQ⟩ := hP6 (k + 1) (by omega) hk
    have hBl := Bl_toFinset n N
    have hsec : ∀ x : Fn K (Fin b) (Fin N), x ∈ Gr (Lr n N) (Bk n N) (k + 1) →
        blockSection Ch (Lr n N) (Bl n N) (k + 1) x ∈ Filt (Lr n N) (Bk n N) (k + 1) ∧
          topPart (Bk n N) (k + 1) (blockSection Ch (Lr n N) (Bl n N) (k + 1) x) = x := by
      intro x hx
      have hL : 2 * Fintype.card (Fin b) ≤ (Lr n N).card + 1 := by
        rw [Fintype.card_fin, Lr_card n N (by omega)]
        exact hn
      have := blockSection_spec (R := K) Ch (Bl_nodup n N) (hBl ▸ Lr_disjoint n N) (by omega) hL
        (hBl ▸ hx)
      rw [hBl] at this
      exact this
    have hfilt : ∀ j, ∀ π : Equiv.Perm (Fin N), FixesLr n π →
        ∀ F : Fn K (Fin b) (Fin N), F ∈ Filt (Lr n N) (Bk n N) j →
          labAct π F ∈ Filt (Lr n N) (Bk n N) j :=
      fun j π hπ F hF => FixesLr.mem_Filt hπ hF
    obtain ⟨C', hCC', hC'F, hdec, hind, hinj, hstab⟩ := thm5_step (p - 1) Z
      (Filt (Lr n N) (Bk n N) k) (Filt (Lr n N) (Bk n N) (k + 1)) (Gr (Lr n N) (Bk n N) (k + 1))
      Q₀ (Filt (Lr n N) (Bk n N) 0) C (topPart (Bk n N) (k + 1))
      (blockSection Ch (Lr n N) (Bl n N) (k + 1)) (Filt_mono (by omega))
      (fun e he h0 => by
        have := mem_Filt_pred he h0
        simpa using this)
      (fun e he => by
        funext t
        rw [topPart_apply]
        split_ifs with h
        · exact he.2 t (by omega)
        · rfl)
      (fun e he => topPart_mem_Gr (Lr_disjoint n N) he) hsec
      (fun e _ => by
        have := Z_comm (b := b) p c (topPart (Bk n N) (k + 1))
          (fun π hπ => (FixesLr.topPart_comm (b := b) hπ (k + 1)).symm)
        rw [← Module.End.mul_apply, this, Module.End.mul_apply])
      (fun e he => Z_mem p _ (hfilt (k + 1)) he) (fun e _ => hZp e) hQ hinjQ (fun e _ => hZp e)
      hF hFind (Filt_mono (by omega)) (le_trans hCF (Filt_mono (by omega))) hinjC
    refine ⟨C', fun σ x hx => ?_, hC'F, hdec, hind, hinj⟩
    exact hstab (rowAct σ) (rowAct_rhoFn σ _) (hCrow σ) (hQ₀row σ)
      (fun y _ => by
        rw [← Module.End.mul_apply, ← rowAct_blockSection, Module.End.mul_apply]) x hx

theorem rowAct_mem_Soc_univ {L : Finset (Fin (n + p ^ a))} (σ : Equiv.Perm (Fin b))
    {F : Fn K (Fin b) (Fin (n + p ^ a))} (hF : F ∈ Soc (univ : Finset (Fin b)) univ L) :
    rowAct σ F ∈ Soc (univ : Finset (Fin b)) univ L := by
  refine ⟨fun t ht => ?_, fun j _ => ?_⟩
  · have g := hF.1 _ ht
    refine ⟨fun j => ?_, fun j y hy => g.val (σ.symm j) y (by simpa using hy),
      fun j k y hj hk => ?_⟩
    · simp only [mem_univ, iff_true]
      have := (g.dom (σ.symm j)).mpr (mem_univ _)
      simpa [comp_apply] using this
    · exact σ.symm.injective (g.inj (σ.symm j) (σ.symm k) y (by simpa using hj)
        (by simpa using hk))
  · have h := rowAct_del (R := K) (α := Fin (n + p ^ a)) σ (σ.symm j)
    rw [Equiv.apply_symm_apply] at h
    rw [← Module.End.mul_apply, ← h, Module.End.mul_apply, hF.2 _ (mem_univ _), map_zero]

theorem blockRows_comp (σ : Equiv.Perm (Fin b)) (B : Finset (Fin (n + p ^ a)))
    (t : Fin b → Option (Fin (n + p ^ a))) :
    nb B (t ∘ σ) = nb B t := by
  unfold BExact.nb
  have : blockRows B (t ∘ σ) = (blockRows B t).map σ.symm.toEmbedding := by
    ext i
    rw [Finset.mem_map_equiv, Equiv.symm_symm, mem_blockRows, mem_blockRows]
    rfl
  rw [this, Finset.card_map]

theorem rowAct_mem_Filt (σ : Equiv.Perm (Fin b)) {Lr' B : Finset (Fin (n + p ^ a))} {k : ℕ}
    {F : Fn K (Fin b) (Fin (n + p ^ a))} (hF : F ∈ Filt Lr' B k) : rowAct σ F ∈ Filt Lr' B k :=
  ⟨rowAct_mem_Soc_univ σ hF.1, fun t ht => hF.2 _ (by rw [blockRows_comp]; exact ht)⟩

theorem Z_mem_Soc (F : Fn K (Fin b) (Fin (n + p ^ a)))
    (hF : F ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _)) :
    rhoFn (zEltP p a n c) F ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) := by
  refine Z_mem p _ (fun π _ G hG => ?_) hF
  have := labAct_mem_Soc hG π
  rwa [Finset.map_univ_equiv] at this

/-- **(P1)** at level `b`, conditional on Prop. 6. -/
theorem P1_concrete (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1) :
    ∀ v ∈ (P (univ : Finset (Fin b)) (univ : Finset (Fin (n + p ^ a))) : Submodule K _),
      (rhoFn (zEltP p a n c) ^ (p - 1)) v ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) →
      ∃ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        (rhoFn (zEltP p a n c) ^ (p - 1)) v = (rhoFn (zEltP p a n c) ^ (p - 1)) s := by
  obtain ⟨C, _, hCF, hdec, _, hinj⟩ := thm5_filt hP6 hn b le_rfl
  have hp : 2 ≤ p - 1 + 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have h := P1_of_decomp (p - 1 + 1) hp (rhoFn (ι := Fin b) (zEltP p a n c))
    (P univ univ) (P0 n (n + p ^ a) b) (PB n (n + p ^ a) b) (Soc univ univ univ)
    (Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) 0) C
    (fun v hv0 hvB => funext fun t => by
      by_cases ht : nb (Bk n (n + p ^ a)) t = 0
      · exact hvB t ht
      · exact hv0 t (by omega))
    (fun v hv => Z_P0 p hv) (fun v _ => Z_PB p c v) (fun v hv => rhoFn_mem_P hv)
    (fun v _ => by rw [Z_pow]; rfl)
    (fun s hs => hdec s (Filt_top hs)) Filt_zero_le_P0 (le_trans hCF (Filt_le_Soc b))
    (fun F hF => hF.1) hinj
  simpa using h

/-- **(T′_soc)** at level `b`, conditional on Prop. 6. -/
theorem Tsoc_concrete (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1) :
    ∃ wS : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))),
      (∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        wS s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _)) ∧
      (∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        (rhoFn (zEltP p a n c) ^ (p - 1)) (wS ((rhoFn (zEltP p a n c) ^ (p - 1)) s)) =
          (rhoFn (zEltP p a n c) ^ (p - 1)) s) ∧
      (∀ σ : Equiv.Perm (Fin b), ∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        rowAct σ (wS s) = wS (rowAct σ s)) := by
  obtain ⟨C, hCrow, hCF, hdec, hind, hinj⟩ := thm5_filt hP6 hn b le_rfl
  have hp : 1 ≤ p - 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hCS := le_trans hCF (Filt_le_Soc b)
  obtain ⟨wS, h1, h2, h3⟩ := Tsoc_of_decomp (p - 1) hp (rhoFn (ι := Fin b) (zEltP p a n c))
    (Soc univ univ univ) (Filt (Lr n (n + p ^ a)) (Bk n (n + p ^ a)) 0) C
    (fun s hs => hdec s (Filt_top hs)) hind (Filt_le_Soc 0)
    (by
      rintro x ⟨v, rfl⟩
      exact zSum_mem _ _ C _ (fun e he => Z_mem_Soc e he) hCS v)
    (fun s hs => Z_P0 p (Filt_zero_le_P0 hs)) (fun _ _ => by rw [Z_pow]; rfl) hinj
  exact ⟨wS, h1, h2, fun σ s hs => h3 (rowAct σ) (rowAct_rhoFn σ _)
    (fun s hs => rowAct_mem_Filt σ hs) (hCrow σ) s hs⟩

end Thm5

/-! ### Transfer to `P_b(N)` and the reduced hypothesis -/

section Transfer

variable (p : ℕ) [Fact p.Prime] [CharP K p] {a n b : ℕ} {c : Fin a → K}

theorem toFn_injective' {N : ℕ} : Function.Injective (toFn (K := K) (b := b) (N := N)) :=
  fun f g h => by rw [← ofFn_toFn f, h, ofFn_toFn]

theorem toFn_u (v : (permRep K (injTuples b) (n + p ^ a)).V) :
    toFn ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v) =
      (rhoFn (zEltP p a n c) ^ (p - 1)) (toFn v) := by
  rw [toFn_asAlgebraHom, map_pow]

theorem toFn_rowV (σ : Equiv.Perm (Fin b)) (v : (permRep K (injTuples b) (n + p ^ a)).V) :
    toFn (rowV K b (n + p ^ a) σ v) = rowAct σ (toFn v) := by
  show toFn (ofFn (rowAct σ (toFn v))) = _
  rw [toFn_ofFn (rowAct_mem_P σ (toFn_mem_P v))]

/-- (P1) on `P_b(N)`, conditional on Prop. 6. -/
theorem hP1_V (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1)
    (v : (permRep K (injTuples b) (n + p ^ a)).V)
    (hv : (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
      SocV K b (n + p ^ a)) :
    ∃ s ∈ SocV K b (n + p ^ a),
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v =
        (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s := by
  have hv' : (rhoFn (zEltP p a n c) ^ (p - 1)) (toFn v) ∈
      (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) := by
    have := hv
    rw [SocV, Submodule.mem_comap, toFn_u] at this
    exact this
  obtain ⟨s', hs', he⟩ := P1_concrete hP6 hn (toFn v) (toFn_mem_P v) hv'
  refine ⟨ofFn s', ?_, toFn_injective' ?_⟩
  · rw [SocV, Submodule.mem_comap, toFn_ofFn hs'.1]
    exact hs'
  · rw [toFn_u, toFn_u, toFn_ofFn hs'.1, he]

/-- **The layer conditions not yet proved** (CONDITIONAL package): DCP_b (Prop. 8, BDM),
(P2) and T′_top (Cor. 6 by transposition). -/
structure LayerConditionsRest (a n : ℕ) (c : Fin a → K) (b : ℕ) where
  hDCP : ∀ φ : Module.End K (permRep K (injTuples b) (n + p ^ a)).V,
    (∀ v, φ v ∈ SocV K b (n + p ^ a)) → (∀ v ∈ VpV K b (n + p ^ a), φ v = 0) →
    (∀ g ∈ GV K b (n + p ^ a), g * φ = φ * g) →
    ∃ x ∈ TupleRelations K (b - 1) (n + p ^ a),
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom x = φ
  hP2 : ∀ v, (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
      VpV K b (n + p ^ a) → ∃ v' ∈ VpV K b (n + p ^ a),
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v =
        (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v'
  wT : Module.End K (permRep K (injTuples b) (n + p ^ a)).V
  hwT : ∀ v ∈ VpV K b (n + p ^ a), wT v ∈ VpV K b (n + p ^ a)
  hwTu : ∀ v,
    (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1))
      (wT ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v)) -
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
        VpV K b (n + p ^ a)
  hwTG : ∀ g ∈ GV K b (n + p ^ a), ∀ v, g (wT v) - wT (g v) ∈ VpV K b (n + p ^ a)

/-- Prop. 6 and the remaining conditions give the full `LayerConditions` (with (P1) and
T′_soc PROVED from Prop. 6 via Thm. 5). -/
noncomputable def LayerConditions.ofRest (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1)
    (Rst : LayerConditionsRest p a n c b) : LayerConditions p a n c b :=
  let W := (Tsoc_concrete hP6 hn).choose
  have hW := (Tsoc_concrete hP6 hn).choose_spec
  have hWP : ∀ F, F ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) →
      toFn (ofFn (W F)) = W F := fun F hF => toFn_ofFn (hW.1 F hF).1
  have hSocZ : ∀ s ∈ SocV K b (n + p ^ a),
      toFn ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s) ∈
        (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) := by
    intro s hs
    rw [toFn_u]
    exact pow_mem_of_mem _ _ (fun e he => Z_mem_Soc e he) _ _ hs
  { hDCP := Rst.hDCP
    hP1 := hP1_V p hP6 hn
    hP2 := Rst.hP2
    wS := ofFn ∘ₗ W ∘ₗ toFn
    hwS := fun s hs => by
      show toFn (ofFn (W (toFn s))) ∈
        (Soc (univ : Finset (Fin b)) univ univ : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))))
      rw [hWP _ hs]
      exact hW.1 _ hs
    hwSu := fun s hs => by
      apply toFn_injective'
      simp only [LinearMap.comp_apply]
      rw [toFn_u, toFn_ofFn (hW.1 _ (hSocZ s hs)).1, toFn_u, hW.2.1 _ hs]
    hwSG := fun g hg s hs => by
      obtain ⟨σ, rfl⟩ := hg
      apply toFn_injective'
      show toFn (rowV K b (n + p ^ a) σ (ofFn (W (toFn s)))) =
        toFn (ofFn (W (toFn (rowV K b (n + p ^ a) σ s))))
      rw [toFn_rowV, toFn_rowV, hWP _ hs, toFn_ofFn (hW.1 _ (rowAct_mem_Soc_univ σ hs)).1,
        hW.2.2 σ _ hs]
    wT := Rst.wT
    hwT := Rst.hwT
    hwTu := Rst.hwTu
    hwTG := Rst.hwTG }

/-- **Theorem A modulo Prop. 6, DCP_b, (P2) and T′_top** (CONDITIONAL stepping stone), with
the linear budget `2r - 1`.  (P1) and T′_soc are no longer assumed: they are derived from Prop. 6
through Prop. 4, Lemma 5 and Thm. 5. -/
theorem topWitnessHypothesis_of_prop6 (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ r a n : ℕ, r < p ^ a → 2 * r - 1 ≤ n → ∀ c : Fin a → L, Generic p c →
      ∀ b, 1 ≤ b → b ≤ r → Prop6Hyp p a n b c ∧ Nonempty (LayerConditionsRest p a n c b)) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  topWitnessHypothesis_of_layerConditions p L _ fun r a n hr hn c hc b hb hbr =>
    ⟨LayerConditions.ofRest p (H r a n hr hn c hc b hb hbr).1 (by omega)
      (H r a n hr hn c hc b hb hbr).2.some⟩

end Transfer

end BExact
