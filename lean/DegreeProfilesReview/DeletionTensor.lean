/-
Stage 3, step 4b: the two identifications used by M5, still at the level of linear algebra.

Setting: `Γ` acts on a finite set `X`; `A ≤ Γ`; `j : F → X` is an injection onto the `A`-fixed
points and every other `A`-orbit has cardinality zero in `K` (hypothesis `FixedData`).

* `permDelEquiv : del A K[X] ≃ K[F]`
      — hom:  the class of an invariant `m` goes to its restriction `f ↦ m (j f)`;
      — inv:  `f ↦ [j f]`.
* `tensDelEquiv σ : del A (K[X] ⊗ Y) ≃ K[F] ⊗ del A Y`
      — inv:  `f ⊗ [y] ↦ [j f ⊗ y]`.

Both are compatible with the residual action of a group `G₀` commuting with `A`
(`permDelEquiv_equivariant`, `tensDelEquiv_symm_equivariant`), and natural
(`permDelEquiv_natural`, `tensDelEquiv_symm_natural`).

Everything here is proved; there is no external hypothesis.
-/
import DegreeProfilesReview.DeletionLinear

open TensorProduct

namespace DegreeProfilesReview.Del

variable {K : Type*} [Field K] {Γ : Type*} [Group Γ] (A : Subgroup Γ)

/-! ### The comparison as an equivalence, with explicit inverse -/

/-- The data of the fixed points: an injection `j` onto the `A`-fixed points of a finite
`Γ`-set, all other orbits having cardinality zero in `K`. -/
structure FixedData (K : Type*) [Field K] {Γ : Type*} [Group Γ] (A : Subgroup Γ)
    (X : Type*) [MulAction Γ X] (F : Type*) where
  j : F → X
  inj : Function.Injective j
  fix : ∀ f, ∀ a ∈ A, a • j f = j f
  orb : ∀ x, x ∉ Set.range j → ((Nat.card (MulAction.orbit A x) : ℕ) : K) = 0

section Equiv

variable {A} {X : Type*} [MulAction Γ X] [Finite X] {F : Type*} (D : FixedData K A X F)
  {Y : Type*} [AddCommGroup Y] [Module K Y] (σ : Representation K Γ Y)

/-- `F →₀ del A Y ≃ del A (X →₀ Y)`. -/
noncomputable def psiEquiv : (F →₀ del A σ) ≃ₗ[K] del A (twist (X := X) σ) :=
  LinearEquiv.ofBijective (psi A σ D.j D.fix) (psi_bijective A σ D.j D.fix D.inj D.orb)

theorem psiEquiv_single (f : F) (y : Y) (hy : y ∈ inv A σ) :
    psiEquiv D σ (Finsupp.single f (delMk A σ y hy)) =
      delMk A (twist σ) (Finsupp.single (D.j f) y)
        (map_mem_inv (lsingle_aequivariant A σ D.j D.fix f) hy) :=
  psi_single A σ D.j D.fix f y hy

theorem psiEquiv_symm_apply (d : del A (twist (X := X) σ)) (f : F) :
    (psiEquiv D σ).symm d f =
      delMap (Finsupp.lapply (D.j f)) (lapply_aequivariant A σ D.j D.fix f) d := by
  have h := LinearMap.congr_fun (eval_psi A σ D.j D.fix D.inj f) ((psiEquiv D σ).symm d)
  rw [LinearMap.comp_apply, Finsupp.lapply_apply] at h
  rw [← h]
  congr 1
  exact (psiEquiv D σ).apply_symm_apply d

theorem psiEquiv_symm_delMk (m : X →₀ Y) (hm : m ∈ inv A (twist (X := X) σ)) (f : F) :
    (psiEquiv D σ).symm (delMk A _ m hm) f =
      delMk A σ (m (D.j f)) (map_mem_inv (lapply_aequivariant A σ D.j D.fix f) hm) := by
  rw [psiEquiv_symm_apply]
  rfl

end Equiv

/-! ### The trivial representation on `K` -/

section Trivial

variable (K Γ)

theorem aug_trivial : aug A (Representation.trivial K Γ K) = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  rintro _ ⟨a, _, v, rfl⟩
  rw [Representation.trivial_apply, sub_self]
  exact Submodule.zero_mem _

theorem mem_inv_trivial (c : K) : c ∈ inv A (Representation.trivial K Γ K) :=
  fun _ _ => by rw [Representation.trivial_apply]

/-- `del A K ≃ K` for the trivial representation. -/
noncomputable def delTrivEquiv : K ≃ₗ[K] del A (Representation.trivial K Γ K) :=
  LinearEquiv.ofBijective
    { toFun := fun c => delMk A _ c (mem_inv_trivial K Γ A c)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      have h : c ∈ aug A (Representation.trivial K Γ K) :=
        (delMk_eq_zero_iff A _ c (mem_inv_trivial K Γ A c)).mp hc
      rw [aug_trivial] at h
      exact (Submodule.mem_bot K).mp h,
    fun d => by
      obtain ⟨c, hc, rfl⟩ := del_induction A _ d
      exact ⟨c, rfl⟩⟩

theorem delTrivEquiv_apply (c : K) :
    delTrivEquiv K Γ A c = delMk A _ c (mem_inv_trivial K Γ A c) := rfl

end Trivial

/-! ### Permutation modules -/

section Perm

variable {A} {X : Type*} [MulAction Γ X] [Finite X] {F : Type*} (D : FixedData K A X F)

omit [Finite X] in
/-- The permutation representation is the twisted action with trivial coefficients. -/
theorem ofMulAction_aequivariant :
    AEquivariant A (Representation.ofMulAction K Γ X)
      (twist (X := X) (Representation.trivial K Γ K)) LinearMap.id := fun a _ m => by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add, map_add]
  | single x c =>
    rw [LinearMap.id_apply, LinearMap.id_apply, Representation.ofMulAction_single, twist_single,
      Representation.trivial_apply]

/-- **The deletion of a permutation module is the permutation module on the fixed points.** -/
noncomputable def permDelEquiv : del A (Representation.ofMulAction K Γ X) ≃ₗ[K] (F →₀ K) :=
  delEquiv (LinearEquiv.refl K (X →₀ K)) (ofMulAction_aequivariant (K := K)) ≪≫ₗ
    (psiEquiv D (Representation.trivial K Γ K)).symm ≪≫ₗ
    (Finsupp.mapRange.linearEquiv (delTrivEquiv K Γ A)).symm

theorem permDelEquiv_delMk (m : X →₀ K) (hm : m ∈ inv A (Representation.ofMulAction K Γ X))
    (f : F) : permDelEquiv D (delMk A _ m hm) f = m (D.j f) := by
  have hm' : m ∈ inv A (twist (X := X) (Representation.trivial K Γ K)) :=
    map_mem_inv (ofMulAction_aequivariant (K := K)) hm
  show (delTrivEquiv K Γ A).symm
    ((psiEquiv D (Representation.trivial K Γ K)).symm (delMk A _ m hm') f) = m (D.j f)
  rw [psiEquiv_symm_delMk]
  apply (delTrivEquiv K Γ A).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [Finite X] in
theorem single_mem_inv (f : F) (c : K) :
    Finsupp.single (D.j f) c ∈ inv A (Representation.ofMulAction K Γ X) := fun a ha => by
  rw [Representation.ofMulAction_single, D.fix f a ha]

theorem permDelEquiv_symm_single (f : F) (c : K) :
    (permDelEquiv D).symm (Finsupp.single f c) =
      delMk A _ (Finsupp.single (D.j f) c) (single_mem_inv D f c) := by
  classical
  apply (permDelEquiv D).injective
  rw [LinearEquiv.apply_symm_apply]
  ext f'
  rw [permDelEquiv_delMk, Finsupp.single_apply, Finsupp.single_apply]
  exact if_congr D.inj.eq_iff.symm rfl rfl

/-- Naturality: an `A`-equivariant map between permutation modules induces, on fixed points,
the map with the restricted matrix. -/
theorem permDelEquiv_natural {X' : Type*} [MulAction Γ X'] [Finite X'] {F' : Type*}
    (D' : FixedData K A X' F') (T : (X →₀ K) →ₗ[K] (X' →₀ K))
    (hT : AEquivariant A (Representation.ofMulAction K Γ X)
      (Representation.ofMulAction K Γ X') T)
    (T' : (F →₀ K) →ₗ[K] (F' →₀ K))
    (h : ∀ f f', T (Finsupp.single (D.j f) 1) (D'.j f') = T' (Finsupp.single f 1) f') :
    (permDelEquiv D').toLinearMap ∘ₗ delMap T hT = T' ∘ₗ (permDelEquiv D).toLinearMap := by
  apply LinearMap.ext
  intro d
  obtain ⟨v, rfl⟩ := (permDelEquiv D).symm.surjective d
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single f c =>
    have hc : Finsupp.single f c = c • Finsupp.single f (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hc]
    simp only [map_smul]
    congr 1
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, permDelEquiv_symm_single, delMap_delMk]
    ext f'
    rw [permDelEquiv_delMk, h]

end Perm

/-! ### Tensoring with a permutation module -/

section Tens

variable {A} {X : Type*} [MulAction Γ X] [DecidableEq X] {Y : Type*} [AddCommGroup Y]
  [Module K Y] (σ : Representation K Γ Y)

theorem fsl_single_tmul (x : X) (c : K) (y : Y) :
    finsuppScalarLeft K Y X (Finsupp.single x c ⊗ₜ[K] y) = Finsupp.single x (c • y) := by
  rw [finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index]
  rw [zero_smul, Finsupp.single_zero]

/-- `K[X] ⊗ Y ≃ (X →₀ Y)` is equivariant for the whole group. -/
theorem fsl_equivariant (γ : Γ) (t : (X →₀ K) ⊗[K] Y) :
    finsuppScalarLeft K Y X (((Representation.ofMulAction K Γ X).tprod σ) γ t) =
      twist (X := X) σ γ (finsuppScalarLeft K Y X t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul p y =>
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p p' hp hp' => rw [TensorProduct.add_tmul, map_add, map_add, hp, hp', map_add, map_add]
    | single x c =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single,
        fsl_single_tmul, fsl_single_tmul, twist_single, map_smul]

theorem fsl_aequivariant :
    AEquivariant A (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ)
      (twist (X := X) σ)
      (finsuppScalarLeft K Y X).toLinearMap := fun a _ t => fsl_equivariant σ a t

variable [Finite X] {F : Type*} [DecidableEq F] (D : FixedData K A X F)

/-- **The deletion commutes with tensoring by a permutation module.** -/
noncomputable def tensDelEquiv :
    del A (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ) ≃ₗ[K]
      (F →₀ K) ⊗[K] del A σ :=
  delEquiv (finsuppScalarLeft K Y X) (fsl_aequivariant σ) ≪≫ₗ (psiEquiv D σ).symm ≪≫ₗ
    (finsuppScalarLeft K (del A σ) F).symm

omit [Finite X] [DecidableEq X] [DecidableEq F] in
theorem tmul_mem_inv (f : F) (c : K) {y : Y} (hy : y ∈ inv A σ) :
    Finsupp.single (D.j f) c ⊗ₜ[K] y ∈
      inv A (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ) :=
  fun a ha => by
    rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single,
      D.fix f a ha, hy a ha]

theorem tensDelEquiv_symm_tmul (f : F) (y : Y) (hy : y ∈ inv A σ) :
    (tensDelEquiv σ D).symm (Finsupp.single f 1 ⊗ₜ[K] delMk A σ y hy) =
      delMk A _ (Finsupp.single (D.j f) 1 ⊗ₜ[K] y) (tmul_mem_inv σ D f 1 hy) := by
  unfold tensDelEquiv
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.symm_symm, fsl_single_tmul, one_smul, psiEquiv_single]
  apply Subtype.ext
  show (aug A _).mkQ ((finsuppScalarLeft K Y X).symm (Finsupp.single (D.j f) y)) = _
  rw [finsuppScalarLeft_symm_apply_single]
  rfl

end Tens

/-! ### The residual action and naturality -/

section Equivariance

variable {A} {X : Type*} [MulAction Γ X] [Finite X] [DecidableEq X] {F : Type*}
  [DecidableEq F] (D : FixedData K A X F)
  {G₀ : Type*} [Group G₀] (i : G₀ →* Γ) (hcomm : ∀ g, ∀ a ∈ A, i g * a = a * i g)
  [MulAction G₀ F] (hj : ∀ (g : G₀) (f : F), D.j (g • f) = i g • D.j f)

omit [DecidableEq X] [DecidableEq F] in
include hj in
/-- `K[F] ≃ del A K[X]` commutes with the residual action. -/
theorem permDelEquiv_symm_equivariant (g : G₀) (v : F →₀ K) :
    (permDelEquiv D).symm (Representation.ofMulAction K G₀ F g v) =
      delRep A (Representation.ofMulAction K Γ X) i hcomm g ((permDelEquiv D).symm v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single f c =>
    rw [Representation.ofMulAction_single, permDelEquiv_symm_single, permDelEquiv_symm_single,
      delRep_delMk]
    apply Subtype.ext
    rw [coe_delMk, coe_delMk, Representation.ofMulAction_single, hj]

variable {Y : Type*} [AddCommGroup Y] [Module K Y] (σ : Representation K Γ Y)

include hj in
/-- `K[F] ⊗ del A Y ≃ del A (K[X] ⊗ Y)` commutes with the residual action. -/
theorem tensDelEquiv_symm_equivariant (g : G₀) (t : (F →₀ K) ⊗[K] del A σ) :
    (tensDelEquiv σ D).symm
        (((Representation.ofMulAction K G₀ F).tprod (delRep A σ i hcomm)) g t) =
      delRep A (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ) i hcomm g
        ((tensDelEquiv σ D).symm t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul v d =>
    obtain ⟨y, hy, rfl⟩ := del_induction A σ d
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [TensorProduct.add_tmul, map_add, hv, hw]
    | single f c =>
      have hc : Finsupp.single f c = c • Finsupp.single f (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hc, ← TensorProduct.smul_tmul']
      simp only [map_smul]
      congr 1
      rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single,
        delRep_delMk, tensDelEquiv_symm_tmul, tensDelEquiv_symm_tmul, delRep_delMk]
      apply Subtype.ext
      rw [coe_delMk, coe_delMk, Representation.tprod_apply, TensorProduct.map_tmul,
        Representation.ofMulAction_single, hj]

omit [Finite X] [DecidableEq X] [DecidableEq F] in
theorem lTensor_aequivariant {Y' : Type*} [AddCommGroup Y'] [Module K Y']
    (σ' : Representation K Γ Y') (φ : Y →ₗ[K] Y') (hφ : AEquivariant A σ σ' φ) :
    AEquivariant A (V := (X →₀ K) ⊗[K] Y) (W := (X →₀ K) ⊗[K] Y')
      ((Representation.ofMulAction K Γ X).tprod σ)
      ((Representation.ofMulAction K Γ X).tprod σ') (LinearMap.lTensor (X →₀ K) φ) :=
  fun a ha t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul v y =>
      rw [Representation.tprod_apply, Representation.tprod_apply, TensorProduct.map_tmul,
        LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul, hφ a ha]

/-- Naturality of `K[F] ⊗ del A Y ≃ del A (K[X] ⊗ Y)` in `Y`. -/
theorem tensDelEquiv_symm_natural {Y' : Type*} [AddCommGroup Y'] [Module K Y']
    (σ' : Representation K Γ Y') (φ : Y →ₗ[K] Y') (hφ : AEquivariant A σ σ' φ)
    (t : (F →₀ K) ⊗[K] del A σ) :
    (tensDelEquiv σ' D).symm (LinearMap.lTensor (F →₀ K) (delMap φ hφ) t) =
      delMap (LinearMap.lTensor (X →₀ K) φ) (lTensor_aequivariant σ σ' φ hφ)
        ((tensDelEquiv σ D).symm t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul v d =>
    obtain ⟨y, hy, rfl⟩ := del_induction A σ d
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [TensorProduct.add_tmul, map_add, hv, hw]
    | single f c =>
      have hc : Finsupp.single f c = c • Finsupp.single f (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hc, ← TensorProduct.smul_tmul']
      simp only [map_smul]
      congr 1
      rw [LinearMap.lTensor_tmul, delMap_delMk, tensDelEquiv_symm_tmul, tensDelEquiv_symm_tmul,
        delMap_delMk]
      apply Subtype.ext
      rw [coe_delMk, coe_delMk, LinearMap.lTensor_tmul]

end Equivariance

end DegreeProfilesReview.Del
