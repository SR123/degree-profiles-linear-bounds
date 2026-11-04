/-
Agent B, round 3 (26 Sep 2026).  The concrete transposition of Cor. 6: (P2) and T′_top at level
`b` from (P1) and T′_soc for `zᵀ = ι z ι⁻¹` (`ι` inverts the regular block `A`), all CONDITIONAL
only on Prop. 6 (through `BThm5`).

* `dotForm` : `B f g = Σ_t f t * g t` on `Fn` (symmetric, nondegenerate).
* `resP`    : restriction to injective total tuples (self-adjoint idempotent onto `P univ univ`).
* `dot_delT`: `B (delᵢᵀ w) x = B w (delᵢ x)`; hence `SocChar` (Soc = V'^⊥ ∩ P) and `V' ⊥ Soc`.
* `dot_labAct`, `dot_rowAct`: adjoints of label and row permutations.
-/
import BThm5
import BTranspose

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 ClaudeCP DegreeProfilesReview.Shifted DegreeProfilesReview.ShiftedM5
open DegreeProfilesReview.ShiftedFunctor DegreeProfilesReview.ConcreteM5

variable {K : Type} [Field K]

/-! ### The dot form -/

section Dot

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- `B f g = Σ_t f t * g t`. -/
noncomputable def dotForm : LinearMap.BilinForm K (Fn K ι α) :=
  LinearMap.mk₂ K (fun f g => ∑ t, f t * g t)
    (fun f f' g => by simp [add_mul, Finset.sum_add_distrib])
    (fun c f g => by simp [Finset.mul_sum, mul_assoc])
    (fun f g g' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c f g => by simp [Finset.mul_sum, mul_left_comm])

theorem dotForm_apply (f g : Fn K ι α) : dotForm f g = ∑ t, f t * g t := rfl

theorem dotForm_symm (f g : Fn K ι α) : dotForm f g = dotForm g f := by
  simp only [dotForm_apply, mul_comm]

theorem dotForm_single (f : Fn K ι α) (s : ι → Option α) :
    dotForm f (Pi.single s 1) = f s := by
  rw [dotForm_apply, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem dotForm_nondegenerate : (dotForm : LinearMap.BilinForm K (Fn K ι α)).Nondegenerate := by
  intro f hf
  funext s
  rw [← dotForm_single f s]
  exact hf _

theorem dot_labAct (π : Equiv.Perm α) (f g : Fn K ι α) :
    dotForm (labAct π f) g = dotForm f (labAct π⁻¹ g) := by
  rw [dotForm_apply, dotForm_apply]
  let e : (ι → Option α) ≃ (ι → Option α) :=
    { toFun := fun t i => (t i).map π.symm
      invFun := fun t i => (t i).map π
      left_inv := fun t => by funext i; simp [Option.map_map]
      right_inv := fun t => by funext i; simp [Option.map_map] }
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [labAct_apply]
  congr 2
  funext i
  simp [e, Option.map_map]

theorem dot_rowAct (σ : Equiv.Perm ι) (f g : Fn K ι α) :
    dotForm (rowAct σ f) g = dotForm f (rowAct σ⁻¹ g) := by
  rw [dotForm_apply, dotForm_apply]
  let e : (ι → Option α) ≃ (ι → Option α) :=
    { toFun := fun t => t ∘ σ
      invFun := fun t => t ∘ σ.symm
      left_inv := fun t => by funext i; simp
      right_inv := fun t => by funext i; simp }
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [rowAct_apply]
  congr 2
  funext i
  simp [e]

end Dot

/-! ### Restriction to injective total tuples -/

section ResP

variable {b N : ℕ}

/-- Restriction to `P univ univ`. -/
noncomputable def resP : Module.End K (Fn K (Fin b) (Fin N)) where
  toFun f t := by
    classical
    exact if Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t then f t else 0
  map_add' f g := by
    classical
    funext t
    by_cases h : Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t <;> simp [h]
  map_smul' c f := by
    classical
    funext t
    by_cases h : Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t <;> simp [h]

theorem resP_apply (f : Fn K (Fin b) (Fin N)) (t : Fin b → Option (Fin N)) :
    resP f t = by
      classical
      exact if Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t then f t else 0 := rfl

theorem resP_mem (f : Fn K (Fin b) (Fin N)) :
    resP f ∈ (P (univ : Finset (Fin b)) (univ : Finset (Fin N)) : Submodule K _) := by
  classical
  intro t ht
  rw [resP_apply] at ht
  split_ifs at ht with h
  · exact h
  · exact absurd rfl ht

theorem resP_of_mem {f : Fn K (Fin b) (Fin N)}
    (hf : f ∈ (P (univ : Finset (Fin b)) (univ : Finset (Fin N)) : Submodule K _)) :
    resP f = f := by
  classical
  funext t
  rw [resP_apply]
  split_ifs with h
  · rfl
  · by_contra h0
    exact h (hf t (Ne.symm h0))

theorem dot_resP (f g : Fn K (Fin b) (Fin N)) : dotForm (resP f) g = dotForm f (resP g) := by
  classical
  rw [dotForm_apply, dotForm_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [resP_apply, resP_apply]
  split_ifs <;> simp

end ResP

/-! ### `del` and its transpose -/

section DelAdj

variable {b N : ℕ}

theorem update_none_of_none {t : Fin b → Option (Fin N)} {i : Fin b} (h : t i = none) :
    update t i none = t := by
  rw [← h]
  exact update_eq_self i t

/-- The key count: `B (delᵢᵀ δ_s) x = (delᵢ x)(s)` for `s i = none`, `x ∈ P`. -/
theorem dot_delT_single (i : Fin b) {s : Fin b → Option (Fin N)} (hs : s i = none)
    {x : Fn K (Fin b) (Fin N)}
    (hx : x ∈ (P (univ : Finset (Fin b)) (univ : Finset (Fin N)) : Submodule K _)) :
    dotForm (delT i (Pi.single s 1)) x = del i x s := by
  classical
  rw [dotForm_apply, del_apply]
  simp only [part_apply, hs, if_true]
  have hinj : Function.Injective (fun z : Fin N => update s i (some z)) := by
    intro z z' h
    have := congrFun h i
    simpa using this
  rw [← Finset.sum_image (f := fun t => x t) (fun z _ z' _ h => hinj h)]
  have h1 : ∑ t, delT i (Pi.single s 1 : Fn K (Fin b) (Fin N)) t * x t =
      ∑ t ∈ univ.image (fun z => update s i (some z)),
        delT i (Pi.single s 1 : Fn K (Fin b) (Fin N)) t * x t := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun t _ ht => ?_).symm
    rw [delT_apply]
    split_ifs with hg
    · rw [Pi.single_apply]
      split_ifs with hts
      · exfalso
        apply ht
        obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp ((hg.dom i).mpr (mem_univ i))
        refine Finset.mem_image.mpr ⟨z, mem_univ _, ?_⟩
        rw [← hts, update_idem, ← hz, update_eq_self]
      · simp
    · simp
  rw [h1]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp ht
  rw [delT_apply]
  have hupd : update (update s i (some z)) i none = s := by
    rw [update_idem, update_none_of_none hs]
  split_ifs with hg
  · rw [hupd, Pi.single_eq_same, one_mul]
  · rw [zero_mul]
    by_contra h0
    exact hg (hx _ (Ne.symm h0))

/-- `B (delᵢᵀ w) x = B w (delᵢ x)` for `w ∈ P (univ \ i)`, `x ∈ P`. -/
theorem dot_delT (i : Fin b) {w : Fn K (Fin b) (Fin N)}
    (hw : w ∈ (P (univ.erase i) (univ : Finset (Fin N)) : Submodule K _))
    {x : Fn K (Fin b) (Fin N)}
    (hx : x ∈ (P (univ : Finset (Fin b)) (univ : Finset (Fin N)) : Submodule K _)) :
    dotForm (delT i w) x = dotForm w (del i x) := by
  classical
  have hw' : w = ∑ s, w s • (Pi.single s 1 : Fn K (Fin b) (Fin N)) := by
    funext t
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw']
  rw [map_sum, map_sum, LinearMap.sum_apply, dotForm_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  by_cases hs : s i = none
  · rw [dot_delT_single i hs hx]
  · have : w s = 0 := by
      by_contra h0
      have g := hw s (Ne.symm h0 |> fun h => by simpa using h0)
      exact (Finset.notMem_erase i univ) ((g.dom i).mp hs)
    rw [this, zero_mul, zero_mul]

end DelAdj

/-! ### `Soc = V'^⊥ ∩ P` and `V' ⊥ Soc` -/

section SocPerp

variable {b N : ℕ}

theorem VpFn_le_P : VpFn (K := K) b N ≤ P (univ : Finset (Fin b)) (univ : Finset (Fin N)) := by
  classical
  refine Submodule.span_le.mpr ?_
  rintro F ⟨i, w, _, rfl⟩
  intro t ht
  rw [delT_apply] at ht
  split_ifs at ht with hg
  · exact hg
  · exact absurd rfl ht

theorem single_mem_P {S : Finset (Fin b)} {s : Fin b → Option (Fin N)}
    (hs : Good S (univ : Finset (Fin N)) s) :
    (Pi.single s 1 : Fn K (Fin b) (Fin N)) ∈ P S (univ : Finset (Fin N)) := by
  intro t ht
  rw [Pi.single_apply] at ht
  split_ifs at ht with h
  · rw [h]
    exact hs
  · exact absurd rfl ht

theorem socChar {x : Fn K (Fin b) (Fin N)}
    (hx : x ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N)))
    (h : ∀ v ∈ VpFn (K := K) b N, dotForm v x = 0) :
    x ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) := by
  refine ⟨hx, fun i _ => funext fun s => ?_⟩
  by_cases hs : s i = none
  · by_cases hg : Good (univ.erase i) (univ : Finset (Fin N)) s
    · rw [← dot_delT_single i hs hx]
      exact h _ (Submodule.subset_span ⟨i, _, single_mem_P hg, rfl⟩)
    · rw [del_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [part_apply, if_pos hs]
      by_contra h0
      have g := hx _ h0
      have g' := g.part hs
      exact hg ⟨g'.dom, fun j y _ => mem_univ y, g'.inj⟩
  · rw [del_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [part_apply, if_neg hs]

theorem dot_VpFn_Soc {v : Fn K (Fin b) (Fin N)} (hv : v ∈ VpFn (K := K) b N)
    {s : Fn K (Fin b) (Fin N)} (hs : s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _)) :
    dotForm v s = 0 := by
  induction hv using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨i, w, hw, rfl⟩ := hF
    rw [dot_delT i hw hs.1, hs.2 i (mem_univ i), map_zero]
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add F G _ _ hF hG => rw [map_add, LinearMap.add_apply, hF, hG, add_zero]
  | smul c F _ hF => rw [map_smul, LinearMap.smul_apply, hF, smul_zero]

end SocPerp

/-! ### The inversion `ι` of the block and `zᵀ = ι z ι⁻¹` -/

section Iota

variable (p : ℕ) [Fact p.Prime] (a n : ℕ)

/-- Inversion of `A`, transported to the block and extended by the identity. -/
noncomputable def iotaN : Equiv.Perm ℕ :=
  (Equiv.inv (ElemAb p a)).extendDomain (blockEquiv p a n)

theorem iotaN_mem : iotaN p a n ∈ Sfin (n + p ^ a) := fun k hk =>
  Equiv.Perm.extendDomain_apply_not_subtype _ _ (by omega)

/-- `ι` as an element of `S_N`. -/
noncomputable def iotaS : Sfin (n + p ^ a) := ⟨iotaN p a n, iotaN_mem p a n⟩

theorem toPerm_conj (v : ElemAb p a) :
    Equiv.inv (ElemAb p a) * MulAction.toPerm v * (Equiv.inv (ElemAb p a))⁻¹ =
      MulAction.toPerm v⁻¹ := by
  refine Equiv.ext fun w => ?_
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.inv_symm, Equiv.inv_apply,
    MulAction.toPerm_apply, smul_eq_mul, mul_inv_rev, inv_inv]
  exact mul_comm (G := ElemAb p a) _ _

theorem iota_conj_sigma (i : Fin a) :
    iotaS p a n * σgen p a n i * (iotaS p a n)⁻¹ = (σgen p a n i)⁻¹ := by
  apply Subtype.ext
  show iotaN p a n * blockHom p a n _ * (iotaN p a n)⁻¹ = (blockHom p a n _)⁻¹
  unfold iotaN blockHom
  simp only [MonoidHom.coe_comp, Function.comp_apply, Equiv.Perm.extendDomainHom_apply,
    MulAction.toPermHom_apply, Equiv.Perm.extendDomain_inv, Equiv.Perm.extendDomain_mul]
  rw [toPerm_conj]
  congr 1
  exact map_inv (MulAction.toPermHom (ElemAb p a) (ElemAb p a)) _

theorem finPerm_inv {N : ℕ} (g : Sfin N) : finPerm g⁻¹ = (finPerm g)⁻¹ := by
  rw [Equiv.Perm.inv_def, finPerm_symm]

end Iota

/-! ### `zᵀ` and the transposed layer conditions -/

section Transposed

variable (p : ℕ) [Fact p.Prime] {a n b : ℕ} (c : Fin a → K)

theorem labAct_mem_Soc_univ (π : Equiv.Perm (Fin (n + p ^ a))) {F : Fn K (Fin b) (Fin (n + p ^ a))}
    (hF : F ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _)) :
    labAct π F ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) := by
  have := labAct_mem_Soc hF π
  rwa [Finset.map_univ_equiv] at this

theorem labAct_mem_P_univ (π : Equiv.Perm (Fin (n + p ^ a))) {F : Fn K (Fin b) (Fin (n + p ^ a))}
    (hF : F ∈ (P (univ : Finset (Fin b)) univ : Submodule K _)) :
    labAct π F ∈ (P (univ : Finset (Fin b)) univ : Submodule K _) := by
  have := labAct_mem_P hF π
  rwa [Finset.map_univ_equiv] at this

/-- `zᵀ = Σ c_i (σ_i⁻¹ - 1)` on `Fn`. -/
noncomputable def Zt : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))) :=
  ∑ i, c i • (labAct (finPerm (σgen p a n i))⁻¹ - 1)

theorem dot_Z (f g : Fn K (Fin b) (Fin (n + p ^ a))) :
    dotForm (rhoFn (zEltP p a n c) f) g = dotForm f (Zt p c g) := by
  rw [Z_eq, Zt, LinearMap.sum_apply, LinearMap.sum_apply, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub,
    LinearMap.sub_apply, dot_labAct]

theorem dot_Z_pow (k : ℕ) (f g : Fn K (Fin b) (Fin (n + p ^ a))) :
    dotForm ((rhoFn (zEltP p a n c) ^ k) f) g = dotForm f ((Zt p c ^ k) g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, dot_Z, ih, pow_succ, Module.End.mul_apply]

/-- `I = labAct ι`, `J = labAct ι⁻¹`. -/
noncomputable def Iop : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))) :=
  labAct (finPerm (iotaS p a n))

noncomputable def Jop : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))) :=
  labAct (finPerm (iotaS p a n)⁻¹)

theorem Jop_Iop : Jop (K := K) (b := b) p (a := a) (n := n) * Iop p = 1 := by
  rw [Jop, Iop, ← labAct_mul, ← finPerm_mul, inv_mul_cancel, finPerm_one, labAct_one]

theorem Iop_Jop : Iop (K := K) (b := b) p (a := a) (n := n) * Jop p = 1 := by
  rw [Jop, Iop, ← labAct_mul, ← finPerm_mul, mul_inv_cancel, finPerm_one, labAct_one]

theorem Zt_eq_conj : Zt (b := b) p c = Iop p * rhoFn (zEltP p a n c) * Jop p := by
  rw [Zt, Z_eq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, Iop_Jop, Iop, Jop,
    ← labAct_mul, ← labAct_mul, ← finPerm_mul, ← finPerm_mul, iota_conj_sigma, finPerm_inv]

theorem Zt_pow_conj (k : ℕ) :
    Zt (b := b) p c ^ k = Iop p * rhoFn (zEltP p a n c) ^ k * Jop p := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, Iop_Jop]
  | succ k ih =>
    rw [pow_succ, ih, Zt_eq_conj, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (Jop p) (Iop p), Jop_Iop, one_mul]

variable [CharP K p]

/-- (P1) for `uᵀ = (zᵀ)^(p-1)`, conditional on Prop. 6. -/
theorem P1_transposed (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1) :
    ∀ y ∈ (P (univ : Finset (Fin b)) (univ : Finset (Fin (n + p ^ a))) : Submodule K _),
      (Zt p c ^ (p - 1)) y ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) →
      ∃ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        (Zt p c ^ (p - 1)) y = (Zt p c ^ (p - 1)) s := by
  intro y hy hu
  rw [Zt_pow_conj, Module.End.mul_apply, Module.End.mul_apply] at hu
  have hu' : (rhoFn (zEltP p a n c) ^ (p - 1)) (Jop p y) ∈
      (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) := by
    have := labAct_mem_Soc_univ p (finPerm (iotaS p a n)⁻¹) hu
    rwa [← Jop, ← Module.End.mul_apply (Jop p) (Iop p), Jop_Iop, Module.End.one_apply] at this
  obtain ⟨s₀, hs₀, he⟩ := P1_concrete hP6 hn (Jop p y) (labAct_mem_P_univ p _ hy) hu'
  have he' : (rhoFn (zEltP p a n c) ^ (p - 1)) (Jop p y) = (rhoFn (zEltP p a n c) ^ (p - 1)) s₀ :=
    he
  refine ⟨Iop p s₀, labAct_mem_Soc_univ p _ hs₀, ?_⟩
  rw [Zt_pow_conj, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, he', ← Module.End.mul_apply (Jop p) (Iop p), Jop_Iop,
    Module.End.one_apply]

/-- T′_soc for `uᵀ`, conditional on Prop. 6. -/
theorem Tsoc_transposed (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1) :
    ∃ w' : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))),
      (∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        w' s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _)) ∧
      (∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        (Zt p c ^ (p - 1)) (w' ((Zt p c ^ (p - 1)) s)) = (Zt p c ^ (p - 1)) s) ∧
      (∀ σ : Equiv.Perm (Fin b), ∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
        rowAct σ (w' s) = w' (rowAct σ s)) := by
  obtain ⟨wS, h1, h2, h3⟩ := Tsoc_concrete hP6 hn
  have hJS : ∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
      Jop (K := K) p (a := a) (n := n) s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) :=
    fun s hs => labAct_mem_Soc_univ p _ hs
  have hIS : ∀ s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _),
      Iop (K := K) p (a := a) (n := n) s ∈ (Soc (univ : Finset (Fin b)) univ univ : Submodule K _) :=
    fun s hs => labAct_mem_Soc_univ p _ hs
  have hJI : ∀ x, Jop (K := K) (b := b) p (a := a) (n := n) (Iop p x) = x := fun x => by
    rw [← Module.End.mul_apply, Jop_Iop, Module.End.one_apply]
  refine ⟨Iop p * wS * Jop p, fun s hs => hIS _ (h1 _ (hJS s hs)), fun s hs => ?_,
    fun σ s hs => ?_⟩
  · simp only [Zt_pow_conj, Module.End.mul_apply, hJI]
    rw [h2 _ (hJS s hs)]
  · have hI : rowAct σ * Iop (K := K) (b := b) p (a := a) (n := n) = Iop p * rowAct σ :=
      (labAct_rowAct _ _).symm
    have hJ : rowAct σ * Jop (K := K) (b := b) p (a := a) (n := n) = Jop p * rowAct σ :=
      (labAct_rowAct _ _).symm
    simp only [Module.End.mul_apply]
    rw [← Module.End.mul_apply (rowAct σ) (Iop p), hI, Module.End.mul_apply,
      h3 σ _ (hJS s hs), ← Module.End.mul_apply (rowAct σ) (Jop p), hJ, Module.End.mul_apply]

end Transposed

/-! ### (P2) and T′_top, and Theorem A modulo Prop. 6 and DCP -/

section Final

variable (p : ℕ) [Fact p.Prime] [CharP K p] {a n b : ℕ} (c : Fin a → K)

theorem Zt_mem_P {F : Fn K (Fin b) (Fin (n + p ^ a))}
    (hF : F ∈ (P (univ : Finset (Fin b)) univ : Submodule K _)) :
    Zt p c F ∈ (P (univ : Finset (Fin b)) univ : Submodule K _) := by
  rw [Zt_eq_conj, Module.End.mul_apply, Module.End.mul_apply]
  exact labAct_mem_P_univ p _ (rhoFn_mem_P (labAct_mem_P_univ p _ hF))

/-- **(P2)** at level `b` on `Fn`, conditional on Prop. 6. -/
theorem P2_concrete (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1) :
    ∀ v ∈ (P (univ : Finset (Fin b)) (univ : Finset (Fin (n + p ^ a))) : Submodule K _),
      (rhoFn (zEltP p a n c) ^ (p - 1)) v ∈ VpFn (K := K) b (n + p ^ a) →
      ∃ v' ∈ VpFn (K := K) b (n + p ^ a),
        (rhoFn (zEltP p a n c) ^ (p - 1)) v = (rhoFn (zEltP p a n c) ^ (p - 1)) v' := by
  set B := dotForm (K := K) (ι := Fin b) (α := Fin (n + p ^ a))
  set PP : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))) := P univ univ
  set SS : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))) := Soc univ univ univ
  set VV : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))) := VpFn b (n + p ^ a)
  set u := rhoFn (ι := Fin b) (zEltP p a n c) ^ (p - 1)
  set u' := Zt (b := b) p c ^ (p - 1)
  have hE1 : ∀ x ∈ PP, resP x = x := fun x hx => resP_of_mem hx
  have hEP : ∀ x, resP x ∈ PP := resP_mem
  have hSocChar : ∀ x ∈ PP, (∀ v ∈ VV, B v x = 0) → x ∈ SS := fun x hx h => socChar hx h
  have hperp : ∀ v ∈ VV, ∀ s ∈ SS, B v s = 0 := fun v hv s hs => dot_VpFn_Soc hv hs
  have hadj : ∀ x y, B (u x) y = B x (u' y) := dot_Z_pow p c (p - 1)
  have huP : ∀ x ∈ PP, u x ∈ PP := pow_mem_of_mem _ _ (fun x hx => rhoFn_mem_P hx) _
  have hu'P : ∀ x ∈ PP, u' x ∈ PP := pow_mem_of_mem _ _ (fun x hx => Zt_mem_P p c hx) _
  exact P2_of_transpose B dotForm_symm dotForm_nondegenerate PP VV SS resP hE1 hEP dot_resP
    VpFn_le_P hSocChar hperp u u' hadj huP hu'P (P1_transposed p c hP6 hn)

/-- **T′_top** at level `b` on `Fn`, conditional on Prop. 6. -/
theorem Ttop_concrete (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1) :
    ∃ wT : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))),
      (∀ x, wT x ∈ (P (univ : Finset (Fin b)) univ : Submodule K _)) ∧
      (∀ v ∈ VpFn (K := K) b (n + p ^ a), wT v ∈ VpFn (K := K) b (n + p ^ a)) ∧
      (∀ v ∈ (P (univ : Finset (Fin b)) univ : Submodule K _),
        (rhoFn (zEltP p a n c) ^ (p - 1)) (wT ((rhoFn (zEltP p a n c) ^ (p - 1)) v)) -
          (rhoFn (zEltP p a n c) ^ (p - 1)) v ∈ VpFn (K := K) b (n + p ^ a)) ∧
      (∀ σ : Equiv.Perm (Fin b), ∀ v ∈ (P (univ : Finset (Fin b)) univ : Submodule K _),
        rowAct σ (wT v) - wT (rowAct σ v) ∈ VpFn (K := K) b (n + p ^ a)) := by
  obtain ⟨w', hw'S, hw'u, hw'G⟩ := Tsoc_transposed p c hP6 hn
  set B := dotForm (K := K) (ι := Fin b) (α := Fin (n + p ^ a))
  set PP : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))) := P univ univ
  set SS : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))) := Soc univ univ univ
  set VV : Submodule K (Fn K (Fin b) (Fin (n + p ^ a))) := VpFn b (n + p ^ a)
  set u := rhoFn (ι := Fin b) (zEltP p a n c) ^ (p - 1)
  set u' := Zt (b := b) p c ^ (p - 1)
  have hE1 : ∀ x ∈ PP, resP x = x := fun x hx => resP_of_mem hx
  have hEP : ∀ x, resP x ∈ PP := resP_mem
  have hSocChar : ∀ x ∈ PP, (∀ v ∈ VV, B v x = 0) → x ∈ SS := fun x hx h => socChar hx h
  have hperp : ∀ v ∈ VV, ∀ s ∈ SS, B v s = 0 := fun v hv s hs => dot_VpFn_Soc hv hs
  have hadj : ∀ x y, B (u x) y = B x (u' y) := dot_Z_pow p c (p - 1)
  have huP : ∀ x ∈ PP, u x ∈ PP := pow_mem_of_mem _ _ (fun x hx => rhoFn_mem_P hx) _
  have hu'P : ∀ x ∈ PP, u' x ∈ PP := pow_mem_of_mem _ _ (fun x hx => Zt_mem_P p c hx) _
  have hLstar : ∀ x ∈ PP, (∀ s ∈ SS, B x s = 0) → x ∈ VV :=
    Lstar_of_SocChar B dotForm_symm dotForm_nondegenerate PP VV SS resP hE1 hEP dot_resP
      VpFn_le_P hSocChar
  have hSP : SS ≤ PP := fun F hF => hF.1
  set G : Set (Module.End K (Fn K (Fin b) (Fin (n + p ^ a)))) :=
    {g | ∃ σ : Equiv.Perm (Fin b), g = rowAct σ}
  have hGP : ∀ g ∈ G, ∀ x ∈ PP, g x ∈ PP := fun g hg x hx => by
    obtain ⟨σ, rfl⟩ := hg
    exact rowAct_mem_P σ hx
  have hGadj : ∀ g ∈ G, ∃ g' : Module.End K (Fn K (Fin b) (Fin (n + p ^ a))),
      (∀ x y, B (g x) y = B x (g' y)) ∧ (∀ s ∈ SS, g' s ∈ SS) ∧
        ∀ s ∈ SS, g' (w' s) = w' (g' s) := fun g hg => by
    obtain ⟨σ, rfl⟩ := hg
    exact ⟨rowAct σ⁻¹, dot_rowAct σ, fun s hs => rowAct_mem_Soc_univ σ⁻¹ hs,
      fun s hs => hw'G σ⁻¹ s hs⟩
  obtain ⟨wT, h0, h1, h2, h3⟩ := Ttop_of_transpose B dotForm_nondegenerate PP VV SS resP hE1 hEP
    dot_resP hSP hLstar hperp u u' hadj huP hu'P w' hw'S hw'u G hGP hGadj
  exact ⟨wT, h0, h1, h2, fun σ v hv => h3 (rowAct σ) ⟨σ, rfl⟩ v hv⟩

/-- **DCP_b** for `P_b(N)` (Prop. 8; from Bowman–Doty–Martin in the paper): every
`S_b`-equivariant map `Top_b → Soc_b` is induced by a tuple relation of support `b - 1`. -/
def DCPHyp (b N : ℕ) : Prop :=
  ∀ φ : Module.End K (permRep K (injTuples b) N).V,
    (∀ v, φ v ∈ SocV K b N) → (∀ v ∈ VpV K b N, φ v = 0) → (∀ g ∈ GV K b N, g * φ = φ * g) →
    ∃ x ∈ TupleRelations K (b - 1) N, (permRep K (injTuples b) N).ρ.asAlgebraHom x = φ

/-- Prop. 6 and DCP_b give the remaining layer conditions ((P2) and T′_top are PROVED here). -/
noncomputable def LayerConditionsRest.ofDCP (hP6 : Prop6Hyp p a n b c) (hn : 2 * b ≤ n + 1)
    (hD : DCPHyp (K := K) b (n + p ^ a)) : LayerConditionsRest p a n c b :=
  let W := (Ttop_concrete p c hP6 hn).choose
  have hW := (Ttop_concrete p c hP6 hn).choose_spec
  { hDCP := hD
    hP2 := fun v hv => by
      have hv' : (rhoFn (zEltP p a n c) ^ (p - 1)) (toFn v) ∈ VpFn (K := K) b (n + p ^ a) := by
        have := hv
        rw [VpV, Submodule.mem_comap, toFn_u] at this
        exact this
      obtain ⟨v'', hv'', he⟩ := P2_concrete p c hP6 hn (toFn v) (toFn_mem_P v) hv'
      refine ⟨ofFn v'', ?_, toFn_injective' ?_⟩
      · rw [VpV, Submodule.mem_comap, toFn_ofFn (VpFn_le_P hv'')]
        exact hv''
      · rw [toFn_u, toFn_u, toFn_ofFn (VpFn_le_P hv''), he]
    wT := ofFn ∘ₗ W ∘ₗ toFn
    hwT := fun v hv => by
      show toFn (ofFn (W (toFn v))) ∈ VpFn (K := K) b (n + p ^ a)
      rw [toFn_ofFn (hW.1 _)]
      exact hW.2.1 _ hv
    hwTu := fun v => by
      show toFn (_ - _) ∈ VpFn (K := K) b (n + p ^ a)
      rw [map_sub, toFn_u, toFn_u]
      simp only [LinearMap.comp_apply]
      rw [toFn_ofFn (hW.1 _), toFn_u]
      exact hW.2.2.1 _ (toFn_mem_P v)
    hwTG := fun g hg v => by
      obtain ⟨σ, rfl⟩ := hg
      show toFn (_ - _) ∈ VpFn (K := K) b (n + p ^ a)
      rw [map_sub, toFn_rowV]
      simp only [LinearMap.comp_apply]
      rw [toFn_ofFn (hW.1 (toFn v)), toFn_rowV, toFn_ofFn (hW.1 (rowAct σ (toFn v)))]
      exact hW.2.2.2 σ _ (toFn_mem_P v) }

/-- **Theorem A modulo Prop. 6 and DCP_b** (CONDITIONAL stepping stone): if, whenever
`r < p^a` and `n ≥ 2r - 1`, every generic `c` satisfies Prop. 6 at every level `1 ≤ b ≤ r` and
DCP_b holds for `P_b(n + p^a)`, then `TopWitnessHypothesis p L (fun r => 2r - 1)`.  All other steps
of the paper proof (Lemma D, Lemma 3, Prop. 4, Lemma 5, Thm. 5, Cor. 6 including the
transposition, Thm. 7 and the assembly) are proved. -/
theorem topWitnessHypothesis_of_prop6_dcp (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (H : ∀ r a n : ℕ, r < p ^ a → 2 * r - 1 ≤ n → ∀ c : Fin a → L, Generic p c →
      ∀ b, 1 ≤ b → b ≤ r → Prop6Hyp p a n b c ∧ DCPHyp (K := L) b (n + p ^ a)) :
    TopWitnessHypothesis p L (fun r => 2 * r - 1) :=
  topWitnessHypothesis_of_prop6 p L fun r a n hr hn c hc b hb hbr =>
    ⟨(H r a n hr hn c hc b hb hbr).1,
      ⟨LayerConditionsRest.ofDCP p c (H r a n hr hn c hc b hb hbr).1 (by omega)
        (H r a n hr hn c hc b hb hbr).2⟩⟩

end Final

end BExact
