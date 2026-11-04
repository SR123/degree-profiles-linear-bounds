/-
Stage 5, step 4: the two identifications needed for the narrowed M5, for the shifted cyclic
construction `sc` (linear algebra level).  This is the analogue of `DeletionTensor.lean`.

Setting: `Γ` acts on a finite set `X`; `s : ι → Γ`, `c : ι → K`; `j : F → X` is an injection into
the points fixed by every `s i`, and the complement of its image is acyclic for `z`
(`ShiftFixedData`; the acyclicity is a THEOREM in the intended situation, see
`ShiftedElemAb.nonfixedAcyclic`).

* `permScEquiv : sc K[X] ≃ K[F]`
      — hom:  the class of `m ∈ ker z` goes to its restriction `f ↦ m (j f)`;
      — inv:  `f ↦ [j f]`.
* `tensScEquiv σ : sc (K[X] ⊗ Y) ≃ K[F] ⊗ sc Y`
      — inv:  `f ⊗ [y] ↦ [j f ⊗ y]`.

Both are compatible with the residual action of a group `G₀` commuting with every `s i`, and
natural.  Everything here is proved; there is no external hypothesis.
-/
import DegreeProfilesReview.ShiftedLinear
import DegreeProfilesReview.DeletionTensor

open TensorProduct

namespace DegreeProfilesReview.Shifted

open DegreeProfilesReview.Del

universe u

variable {K : Type u} [Field K] {Γ : Type*} [Group Γ] {ι : Type*} [Fintype ι]
  (s : ι → Γ) (c : ι → K)

/-- The data of the fixed points for the shifted cyclic construction: an injection `j` into the
points fixed by every `s i`, such that the rest of `X` is acyclic for `z` with arbitrary
coefficients. -/
structure ShiftFixedData (X : Type*) [MulAction Γ X] (F : Type*) where
  j : F → X
  inj : Function.Injective j
  fix : ∀ f k, s k • j f = j f
  acyc : ∀ (Y : Type u) [AddCommGroup Y] [Module K Y] (σ : Representation K Γ Y),
    NonfixedAcyclic s c σ j

section Equiv

variable {s c} {X : Type*} [MulAction Γ X] [Finite X] {F : Type*} (D : ShiftFixedData s c X F)
  {Y : Type u} [AddCommGroup Y] [Module K Y] (σ : Representation K Γ Y)

/-- `F →₀ sc Y ≃ sc (X →₀ Y)`. -/
noncomputable def psiEquiv : (F →₀ sc s c σ) ≃ₗ[K] sc s c (twist (X := X) σ) :=
  LinearEquiv.ofBijective (psi s c σ D.j D.fix)
    (psi_bijective s c σ D.j D.fix D.inj (D.acyc Y σ))

theorem psiEquiv_single (f : F) (y : Y) (hy : y ∈ LinearMap.ker (zOp s c σ)) :
    psiEquiv D σ (Finsupp.single f (scMk s c σ y hy)) =
      scMk s c (twist σ) (Finsupp.single (D.j f) y)
        (map_mem_ker c (lsingle_sequivariant s σ D.j D.fix f) hy) :=
  psi_single s c σ D.j D.fix f y hy

theorem psiEquiv_symm_apply (d : sc s c (twist (X := X) σ)) (f : F) :
    (psiEquiv D σ).symm d f =
      scMap c (Finsupp.lapply (D.j f)) (lapply_sequivariant s σ D.j D.fix f) d := by
  have h := LinearMap.congr_fun (eval_psi s c σ D.j D.fix D.inj f) ((psiEquiv D σ).symm d)
  rw [LinearMap.comp_apply, Finsupp.lapply_apply] at h
  rw [← h]
  congr 1
  exact (psiEquiv D σ).apply_symm_apply d

theorem psiEquiv_symm_scMk (m : X →₀ Y) (hm : m ∈ LinearMap.ker (zOp s c (twist (X := X) σ)))
    (f : F) :
    (psiEquiv D σ).symm (scMk s c _ m hm) f =
      scMk s c σ (m (D.j f)) (map_mem_ker c (lapply_sequivariant s σ D.j D.fix f) hm) := by
  rw [psiEquiv_symm_apply]
  rfl

end Equiv

/-! ### The trivial representation on `K` -/

section Trivial

variable (K Γ)

theorem zOp_trivial : zOp s c (Representation.trivial K Γ K) = 0 := by
  apply LinearMap.ext
  intro v
  rw [zOp_apply, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Representation.trivial_apply, sub_self, smul_zero]

theorem mem_ker_trivial (a : K) : a ∈ LinearMap.ker (zOp s c (Representation.trivial K Γ K)) := by
  rw [LinearMap.mem_ker, zOp_trivial, LinearMap.zero_apply]

/-- `sc K ≃ K` for the trivial representation. -/
noncomputable def scTrivEquiv : K ≃ₗ[K] sc s c (Representation.trivial K Γ K) :=
  LinearEquiv.ofBijective
    { toFun := fun a => scMk s c _ a (mem_ker_trivial K Γ s c a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      have h : a ∈ LinearMap.range (zOp s c (Representation.trivial K Γ K)) :=
        (scMk_eq_zero_iff s c _ a (mem_ker_trivial K Γ s c a)).mp ha
      rw [zOp_trivial, LinearMap.range_zero] at h
      exact (Submodule.mem_bot K).mp h,
    fun d => by
      obtain ⟨a, ha, rfl⟩ := sc_induction s c _ d
      exact ⟨a, rfl⟩⟩

theorem scTrivEquiv_apply (a : K) :
    scTrivEquiv K Γ s c a = scMk s c _ a (mem_ker_trivial K Γ s c a) := rfl

end Trivial

/-! ### Permutation modules -/

section Perm

variable {s c} {X : Type*} [MulAction Γ X] [Finite X] {F : Type*} (D : ShiftFixedData s c X F)

omit [Fintype ι] [Finite X] in
/-- The permutation representation is the twisted action with trivial coefficients. -/
theorem ofMulAction_sequivariant :
    SEquivariant s (Representation.ofMulAction K Γ X)
      (twist (X := X) (Representation.trivial K Γ K)) LinearMap.id := fun i m => by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add, map_add]
  | single x a =>
    rw [LinearMap.id_apply, LinearMap.id_apply, Representation.ofMulAction_single, twist_single,
      Representation.trivial_apply]

/-- **`sc` of a permutation module is the permutation module on the fixed points.** -/
noncomputable def permScEquiv : sc s c (Representation.ofMulAction K Γ X) ≃ₗ[K] (F →₀ K) :=
  scEquiv c (LinearEquiv.refl K (X →₀ K)) (ofMulAction_sequivariant (K := K)) ≪≫ₗ
    (psiEquiv D (Representation.trivial K Γ K)).symm ≪≫ₗ
    (Finsupp.mapRange.linearEquiv (scTrivEquiv K Γ s c)).symm

theorem permScEquiv_scMk (m : X →₀ K)
    (hm : m ∈ LinearMap.ker (zOp s c (Representation.ofMulAction K Γ X))) (f : F) :
    permScEquiv D (scMk s c _ m hm) f = m (D.j f) := by
  have hm' : m ∈ LinearMap.ker (zOp s c (twist (X := X) (Representation.trivial K Γ K))) :=
    map_mem_ker c (ofMulAction_sequivariant (K := K)) hm
  show (scTrivEquiv K Γ s c).symm
    ((psiEquiv D (Representation.trivial K Γ K)).symm (scMk s c _ m hm') f) = m (D.j f)
  rw [psiEquiv_symm_scMk]
  apply (scTrivEquiv K Γ s c).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [Finite X] in
theorem single_mem_ker (f : F) (a : K) :
    Finsupp.single (D.j f) a ∈ LinearMap.ker (zOp s c (Representation.ofMulAction K Γ X)) := by
  rw [LinearMap.mem_ker]
  apply zOp_eq_zero_of_fixed
  intro i
  rw [Representation.ofMulAction_single, D.fix f i]

theorem permScEquiv_symm_single (f : F) (a : K) :
    (permScEquiv D).symm (Finsupp.single f a) =
      scMk s c _ (Finsupp.single (D.j f) a) (single_mem_ker D f a) := by
  classical
  apply (permScEquiv D).injective
  rw [LinearEquiv.apply_symm_apply]
  ext f'
  rw [permScEquiv_scMk, Finsupp.single_apply, Finsupp.single_apply]
  exact if_congr D.inj.eq_iff.symm rfl rfl

/-- Naturality: a linear map between permutation modules commuting with every `s i` induces, on
fixed points, the map with the restricted matrix. -/
theorem permScEquiv_natural {X' : Type*} [MulAction Γ X'] [Finite X'] {F' : Type*}
    (D' : ShiftFixedData s c X' F') (T : (X →₀ K) →ₗ[K] (X' →₀ K))
    (hT : SEquivariant s (Representation.ofMulAction K Γ X)
      (Representation.ofMulAction K Γ X') T)
    (T' : (F →₀ K) →ₗ[K] (F' →₀ K))
    (h : ∀ f f', T (Finsupp.single (D.j f) 1) (D'.j f') = T' (Finsupp.single f 1) f') :
    (permScEquiv D').toLinearMap ∘ₗ scMap c T hT = T' ∘ₗ (permScEquiv D).toLinearMap := by
  apply LinearMap.ext
  intro d
  obtain ⟨v, rfl⟩ := (permScEquiv D).symm.surjective d
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single f a =>
    have ha : Finsupp.single f a = a • Finsupp.single f (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [ha]
    simp only [map_smul]
    congr 1
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, permScEquiv_symm_single, scMap_scMk]
    ext f'
    rw [permScEquiv_scMk, h]

end Perm

/-! ### Tensoring with a permutation module -/

section Tens

variable {s c} {X : Type*} [MulAction Γ X] [DecidableEq X] {Y : Type u} [AddCommGroup Y]
  [Module K Y] (σ : Representation K Γ Y)

omit [Fintype ι] in
theorem fsl_sequivariant :
    SEquivariant s (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ)
      (twist (X := X) σ)
      (finsuppScalarLeft K Y X).toLinearMap := fun i t => fsl_equivariant σ (s i) t

variable [Finite X] {F : Type*} [DecidableEq F] (D : ShiftFixedData s c X F)

/-- **`sc` commutes with tensoring by a permutation module.** -/
noncomputable def tensScEquiv :
    sc s c (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ) ≃ₗ[K]
      (F →₀ K) ⊗[K] sc s c σ :=
  scEquiv c (finsuppScalarLeft K Y X) (fsl_sequivariant σ) ≪≫ₗ (psiEquiv D σ).symm ≪≫ₗ
    (finsuppScalarLeft K (sc s c σ) F).symm

omit [Finite X] [DecidableEq X] [DecidableEq F] in
theorem tmul_mem_ker (f : F) (a : K) {y : Y} (hy : y ∈ LinearMap.ker (zOp s c σ)) :
    Finsupp.single (D.j f) a ⊗ₜ[K] y ∈
      LinearMap.ker (zOp s c (V := (X →₀ K) ⊗[K] Y)
        ((Representation.ofMulAction K Γ X).tprod σ)) := by
  rw [LinearMap.mem_ker, zOp_apply]
  have h : ∀ i, c i • (((Representation.ofMulAction K Γ X).tprod σ) (s i)
      (Finsupp.single (D.j f) a ⊗ₜ[K] y) - Finsupp.single (D.j f) a ⊗ₜ[K] y) =
      Finsupp.single (D.j f) a ⊗ₜ[K] (c i • (σ (s i) y - y)) := by
    intro i
    rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single,
      D.fix f i, ← TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  rw [Finset.sum_congr rfl (fun i _ => h i), ← TensorProduct.tmul_sum, ← zOp_apply,
    LinearMap.mem_ker.mp hy, TensorProduct.tmul_zero]

theorem tensScEquiv_symm_tmul (f : F) (y : Y) (hy : y ∈ LinearMap.ker (zOp s c σ)) :
    (tensScEquiv σ D).symm (Finsupp.single f 1 ⊗ₜ[K] scMk s c σ y hy) =
      scMk s c _ (Finsupp.single (D.j f) 1 ⊗ₜ[K] y) (tmul_mem_ker σ D f 1 hy) := by
  unfold tensScEquiv
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    LinearEquiv.symm_symm, fsl_single_tmul, one_smul, psiEquiv_single]
  apply Subtype.ext
  show (LinearMap.range _).mkQ ((finsuppScalarLeft K Y X).symm (Finsupp.single (D.j f) y)) = _
  rw [finsuppScalarLeft_symm_apply_single]
  rfl

end Tens

/-! ### The residual action and naturality -/

section Equivariance

variable {s c} {X : Type*} [MulAction Γ X] [Finite X] [DecidableEq X] {F : Type*}
  [DecidableEq F] (D : ShiftFixedData s c X F)
  {G₀ : Type*} [Group G₀] (i : G₀ →* Γ) (hcomm : ∀ g k, i g * s k = s k * i g)
  [MulAction G₀ F] (hj : ∀ (g : G₀) (f : F), D.j (g • f) = i g • D.j f)

omit [DecidableEq X] [DecidableEq F] in
include hj in
/-- `K[F] ≃ sc K[X]` commutes with the residual action. -/
theorem permScEquiv_symm_equivariant (g : G₀) (v : F →₀ K) :
    (permScEquiv D).symm (Representation.ofMulAction K G₀ F g v) =
      scRep s c (Representation.ofMulAction K Γ X) i hcomm g ((permScEquiv D).symm v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single f a =>
    rw [Representation.ofMulAction_single, permScEquiv_symm_single, permScEquiv_symm_single,
      scRep_scMk]
    apply scMk_congr
    rw [Representation.ofMulAction_single, hj]

variable {Y : Type u} [AddCommGroup Y] [Module K Y] (σ : Representation K Γ Y)

include hj in
/-- `K[F] ⊗ sc Y ≃ sc (K[X] ⊗ Y)` commutes with the residual action. -/
theorem tensScEquiv_symm_equivariant (g : G₀) (t : (F →₀ K) ⊗[K] sc s c σ) :
    (tensScEquiv σ D).symm
        (((Representation.ofMulAction K G₀ F).tprod (scRep s c σ i hcomm)) g t) =
      scRep s c (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ) i hcomm g
        ((tensScEquiv σ D).symm t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul v d =>
    obtain ⟨y, hy, rfl⟩ := sc_induction s c σ d
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [TensorProduct.add_tmul, map_add, hv, hw]
    | single f a =>
      have ha : Finsupp.single f a = a • Finsupp.single f (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [ha, ← TensorProduct.smul_tmul']
      simp only [map_smul]
      congr 1
      have hy' := map_mem_ker c (sequivariant_of_comm s σ i hcomm g) hy
      have hstep : ((Representation.ofMulAction K G₀ F).tprod (scRep s c σ i hcomm)) g
          (Finsupp.single f 1 ⊗ₜ[K] scMk s c σ y hy) =
          Finsupp.single (g • f) 1 ⊗ₜ[K] scMk s c σ (σ (i g) y) hy' := by
        rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single]
        rfl
      have hvec : Finsupp.single (D.j (g • f)) (1 : K) ⊗ₜ[K] σ (i g) y =
          ((Representation.ofMulAction K Γ X).tprod σ) (i g)
            (Finsupp.single (D.j f) 1 ⊗ₜ[K] y) := by
        rw [Representation.tprod_apply, TensorProduct.map_tmul,
          Representation.ofMulAction_single, hj]
      calc (tensScEquiv σ D).symm (((Representation.ofMulAction K G₀ F).tprod
              (scRep s c σ i hcomm)) g (Finsupp.single f 1 ⊗ₜ[K] scMk s c σ y hy))
          = (tensScEquiv σ D).symm (Finsupp.single (g • f) 1 ⊗ₜ[K] scMk s c σ (σ (i g) y) hy') :=
            congrArg _ hstep
        _ = scMk s c _ (Finsupp.single (D.j (g • f)) 1 ⊗ₜ[K] σ (i g) y)
              (tmul_mem_ker σ D (g • f) 1 hy') := tensScEquiv_symm_tmul σ D (g • f) _ hy'
        _ = scMk s c _ (((Representation.ofMulAction K Γ X).tprod σ) (i g)
              (Finsupp.single (D.j f) 1 ⊗ₜ[K] y))
              (map_mem_ker c (sequivariant_of_comm s _ i hcomm g) (tmul_mem_ker σ D f 1 hy)) :=
            scMk_congr s c _ hvec _ _
        _ = scRep s c (V := (X →₀ K) ⊗[K] Y) ((Representation.ofMulAction K Γ X).tprod σ) i hcomm g
              (scMk s c _ (Finsupp.single (D.j f) 1 ⊗ₜ[K] y) (tmul_mem_ker σ D f 1 hy)) := rfl
        _ = _ := congrArg _ (tensScEquiv_symm_tmul σ D f y hy).symm

omit [Fintype ι] [Finite X] [DecidableEq X] in
theorem lTensor_sequivariant {Y' : Type u} [AddCommGroup Y'] [Module K Y']
    (σ' : Representation K Γ Y') (φ : Y →ₗ[K] Y') (hφ : SEquivariant s σ σ' φ) :
    SEquivariant s (V := (X →₀ K) ⊗[K] Y) (W := (X →₀ K) ⊗[K] Y')
      ((Representation.ofMulAction K Γ X).tprod σ)
      ((Representation.ofMulAction K Γ X).tprod σ') (LinearMap.lTensor (X →₀ K) φ) :=
  fun k t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul v y =>
      rw [Representation.tprod_apply, Representation.tprod_apply, TensorProduct.map_tmul,
        LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul, hφ k]

/-- Naturality of `K[F] ⊗ sc Y ≃ sc (K[X] ⊗ Y)` in `Y`. -/
theorem tensScEquiv_symm_natural {Y' : Type u} [AddCommGroup Y'] [Module K Y']
    (σ' : Representation K Γ Y') (φ : Y →ₗ[K] Y') (hφ : SEquivariant s σ σ' φ)
    (t : (F →₀ K) ⊗[K] sc s c σ) :
    (tensScEquiv σ' D).symm (LinearMap.lTensor (F →₀ K) (scMap c φ hφ) t) =
      scMap c (LinearMap.lTensor (X →₀ K) φ) (lTensor_sequivariant σ σ' φ hφ)
        ((tensScEquiv σ D).symm t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul v d =>
    obtain ⟨y, hy, rfl⟩ := sc_induction s c σ d
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [TensorProduct.add_tmul, map_add, hv, hw]
    | single f a =>
      have ha : Finsupp.single f a = a • Finsupp.single f (1 : K) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [ha, ← TensorProduct.smul_tmul']
      simp only [map_smul]
      congr 1
      have hy' := map_mem_ker c hφ hy
      have hstep : LinearMap.lTensor (F →₀ K) (scMap c φ hφ)
          (Finsupp.single f 1 ⊗ₜ[K] scMk s c σ y hy) =
          Finsupp.single f 1 ⊗ₜ[K] scMk s c σ' (φ y) hy' := by
        rw [LinearMap.lTensor_tmul]
        rfl
      have hvec : Finsupp.single (D.j f) (1 : K) ⊗ₜ[K] φ y =
          LinearMap.lTensor (X →₀ K) φ (Finsupp.single (D.j f) 1 ⊗ₜ[K] y) := by
        rw [LinearMap.lTensor_tmul]
      calc (tensScEquiv σ' D).symm (LinearMap.lTensor (F →₀ K) (scMap c φ hφ)
              (Finsupp.single f 1 ⊗ₜ[K] scMk s c σ y hy))
          = (tensScEquiv σ' D).symm (Finsupp.single f 1 ⊗ₜ[K] scMk s c σ' (φ y) hy') :=
            congrArg _ hstep
        _ = scMk s c _ (Finsupp.single (D.j f) 1 ⊗ₜ[K] φ y) (tmul_mem_ker σ' D f 1 hy') :=
            tensScEquiv_symm_tmul σ' D f _ hy'
        _ = scMk s c _ (LinearMap.lTensor (X →₀ K) φ (Finsupp.single (D.j f) 1 ⊗ₜ[K] y))
              (map_mem_ker c (lTensor_sequivariant σ σ' φ hφ) (tmul_mem_ker σ D f 1 hy)) :=
            scMk_congr s c _ hvec _ _
        _ = scMap c (LinearMap.lTensor (X →₀ K) φ) (lTensor_sequivariant σ σ' φ hφ)
              (scMk s c _ (Finsupp.single (D.j f) 1 ⊗ₜ[K] y) (tmul_mem_ker σ D f 1 hy)) := rfl
        _ = _ := congrArg _ (tensScEquiv_symm_tmul σ D f y hy).symm

end Equivariance

end DegreeProfilesReview.Shifted
