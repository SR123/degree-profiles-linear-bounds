/-
Agent B, round 3 (26 Sep 2026).  Bridge between Stage 5's tuple modules and the uniform
representation of `BLemmaD`.

Stage 5: `permRep K (injTuples b) N` has underlying space `(injTuples b).Rk N →₀ K`, the
injective maps `Fin b → Fin N`, with `S_N = Sfin N` acting by `(g f)(τ) = f (g⁻¹ • τ)`.
Here: rows `Fin b`, labels `Fin N`, `Fn K (Fin b) (Fin N)`, and `P univ univ` is `P_b(N)`.

* `toFn`, `ofFn` : mutually inverse linear maps between `(injTuples b).Rk N →₀ K` and
  `P univ univ` (`ofFn_toFn`, `toFn_ofFn`, `toFn_mem_P`).
* `finPerm g` : the permutation of `Fin N` induced by `g ∈ Sfin N`; `finPerm` is a monoid hom.
* `toFn_rho` : `toFn (ρ g f) = labAct (finPerm g) (toFn f)` — the Stage 5 action is the label
  action of `BLabel`.
-/
import BLabel
import DegreeProfilesReview.PermFromTuples

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4

variable {K : Type} [Field K] {b N : ℕ}

noncomputable instance fintypeRk : Fintype ((injTuples b).Rk N) := Fintype.ofFinite _

/-- An injective tuple as a partial tuple with all rows present. -/
def embT (τ : (injTuples b).Rk N) : Fin b → Option (Fin N) := fun i => some (τ.1 i)

theorem embT_injective : Function.Injective (embT (b := b) (N := N)) := by
  intro τ τ' h
  apply Subtype.ext
  funext i
  have := congrFun h i
  simpa [embT] using this

theorem embT_good (τ : (injTuples b).Rk N) : Good (univ : Finset (Fin b)) univ (embT τ) := by
  refine ⟨fun j => by simp [embT], fun j y _ => mem_univ y, fun j k y hj hk => ?_⟩
  simp only [embT, Option.some.injEq] at hj hk
  apply τ.2
  show (τ.1 j).val = (τ.1 k).val
  rw [hj, hk]

/-- `K[Inj] → Fn`. -/
noncomputable def toFn : ((injTuples b).Rk N →₀ K) →ₗ[K] Fn K (Fin b) (Fin N) where
  toFun f t := ∑ τ, if embT τ = t then f τ else 0
  map_add' f g := by
    funext t
    simp only [Finsupp.add_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp
  map_smul' c f := by
    funext t
    simp only [Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    split_ifs <;> simp

theorem toFn_apply (f : (injTuples b).Rk N →₀ K) (t : Fin b → Option (Fin N)) :
    toFn f t = ∑ τ, if embT τ = t then f τ else 0 := rfl

theorem toFn_embT (f : (injTuples b).Rk N →₀ K) (τ : (injTuples b).Rk N) :
    toFn f (embT τ) = f τ := by
  rw [toFn_apply, Finset.sum_eq_single τ]
  · simp
  · intro τ' _ h
    rw [if_neg (fun h' => h (embT_injective h'))]
  · intro h
    exact absurd (mem_univ τ) h

theorem toFn_eq_zero (f : (injTuples b).Rk N →₀ K) {t : Fin b → Option (Fin N)}
    (ht : ∀ τ, embT τ ≠ t) : toFn f t = 0 := by
  rw [toFn_apply]
  exact Finset.sum_eq_zero fun τ _ => by rw [if_neg (ht τ)]

/-- `Fn → K[Inj]`. -/
noncomputable def ofFn : Fn K (Fin b) (Fin N) →ₗ[K] ((injTuples b).Rk N →₀ K) :=
  (Finsupp.linearEquivFunOnFinite K K ((injTuples b).Rk N)).symm.toLinearMap ∘ₗ
    LinearMap.funLeft K K embT

theorem ofFn_apply (F : Fn K (Fin b) (Fin N)) (τ : (injTuples b).Rk N) : ofFn F τ = F (embT τ) :=
  rfl

theorem ofFn_toFn (f : (injTuples b).Rk N →₀ K) : ofFn (toFn f) = f := by
  ext τ
  rw [ofFn_apply, toFn_embT]

theorem toFn_mem_P (f : (injTuples b).Rk N →₀ K) :
    toFn f ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N)) := by
  intro t ht
  by_contra hg
  apply ht
  apply toFn_eq_zero
  rintro τ rfl
  exact hg (embT_good τ)

/-- A total injective partial tuple is some `embT τ`. -/
theorem exists_embT {t : Fin b → Option (Fin N)} (ht : Good (univ : Finset (Fin b)) univ t) :
    ∃ τ : (injTuples b).Rk N, embT τ = t := by
  have hs : ∀ i, (t i).isSome := fun i => by
    have := (ht.dom i).mpr (mem_univ i)
    exact Option.isSome_iff_ne_none.mpr this
  let x : Fin b → Fin N := fun i => (t i).get (hs i)
  have hx : ∀ i, t i = some (x i) := fun i => (Option.some_get (hs i)).symm
  refine ⟨⟨x, ?_⟩, ?_⟩
  · intro i j hij
    have hij' : x i = x j := Fin.ext hij
    exact ht.inj i j (x i) (hx i) (by rw [hij']; exact hx j)
  · funext i
    exact (hx i).symm

theorem toFn_ofFn {F : Fn K (Fin b) (Fin N)}
    (hF : F ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N))) : toFn (ofFn F) = F := by
  funext t
  by_cases ht : Good (univ : Finset (Fin b)) univ t
  · obtain ⟨τ, rfl⟩ := exists_embT ht
    rw [toFn_embT, ofFn_apply]
  · rw [toFn_eq_zero]
    · by_contra h
      exact ht (hF t (Ne.symm h))
    · rintro τ rfl
      exact ht (embT_good τ)

/-- The permutation of `Fin N` induced by `g ∈ S_N`. -/
def finPerm (g : Sfin N) : Equiv.Perm (Fin N) where
  toFun x := ⟨g.1 x.val, Sfin_lt g.2 x.2⟩
  invFun x := ⟨(g⁻¹).1 x.val, Sfin_lt (g⁻¹).2 x.2⟩
  left_inv x := by
    apply Fin.ext
    show (g⁻¹ : Sfin N).1 (g.1 x.val) = x.val
    rw [Subgroup.coe_inv, Equiv.Perm.inv_apply_self]
  right_inv x := by
    apply Fin.ext
    show g.1 ((g⁻¹ : Sfin N).1 x.val) = x.val
    rw [Subgroup.coe_inv, Equiv.Perm.apply_inv_self]

theorem finPerm_val (g : Sfin N) (x : Fin N) : (finPerm g x).val = g.1 x.val := rfl

theorem finPerm_symm (g : Sfin N) : (finPerm g).symm = finPerm g⁻¹ := rfl

theorem finPerm_mul (g h : Sfin N) : finPerm (g * h) = finPerm g * finPerm h := by
  ext x
  rfl

/-- The Stage 5 action is the label action. -/
theorem toFn_rho (g : Sfin N) (f : (injTuples b).Rk N →₀ K) :
    toFn ((permRep K (injTuples b) N).ρ g f) = labAct (finPerm g) (toFn f) := by
  have key : ∀ τ : (injTuples b).Rk N,
      (fun i => (embT τ i).map (finPerm g).symm) = embT (g⁻¹ • τ) := by
    intro τ
    funext i
    simp only [embT, Option.map_some, finPerm_symm, Option.some.injEq]
    apply Fin.ext
    rw [finPerm_val]
    exact (tupleVal_smul g⁻¹ τ i).symm
  funext t
  rw [labAct_apply]
  by_cases ht : ∃ τ : (injTuples b).Rk N, embT τ = t
  · obtain ⟨τ, rfl⟩ := ht
    rw [toFn_embT, key, toFn_embT]
    exact Representation.ofMulAction_apply g f τ
  · push_neg at ht
    rw [toFn_eq_zero _ ht, toFn_eq_zero]
    intro τ h
    apply ht (g • τ)
    have h2 := congrArg (fun s => fun i => (s i).map (finPerm g)) h
    have h3 : (fun i => (embT τ i).map (finPerm g)) = t := by
      refine h2.trans ?_
      funext i
      simp [Option.map_map]
    rw [← h3]
    funext i
    simp only [embT, Option.map_some, Option.some.injEq]
    apply Fin.ext
    rw [finPerm_val]
    exact tupleVal_smul g τ i

/-! ### The group algebra acting on `Fn` -/

theorem finPerm_one : finPerm (1 : Sfin N) = 1 := by
  ext x
  rfl

section GroupAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `S_N` acting on labels, as a monoid hom. -/
def labHom : Sfin N →* Module.End K (Fn K ι (Fin N)) where
  toFun g := labAct (finPerm g)
  map_one' := by rw [finPerm_one, labAct_one]
  map_mul' g h := by rw [finPerm_mul, labAct_mul]

/-- `K S_N` acting on `Fn` through the label action. -/
noncomputable def rhoFn : MonoidAlgebra K (Sfin N) →ₐ[K] Module.End K (Fn K ι (Fin N)) :=
  MonoidAlgebra.lift K (Sfin N) _ labHom

theorem rhoFn_single (g : Sfin N) (c : K) :
    rhoFn (ι := ι) (MonoidAlgebra.single g c) = c • labAct (finPerm g) := by
  rw [rhoFn, MonoidAlgebra.lift_single]
  rfl

/-- `rhoFn x` commutes with every endomorphism commuting with all label permutations. -/
theorem rhoFn_comm (T : Module.End K (Fn K ι (Fin N)))
    (hT : ∀ π : Equiv.Perm (Fin N), T * labAct π = labAct π * T)
    (x : MonoidAlgebra K (Sfin N)) : T * rhoFn x = rhoFn x * T := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    rw [MonoidAlgebra.of_apply, rhoFn_single, one_smul, hT]
  | hadd x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
  | hsmul c x hx => rw [map_smul, mul_smul_comm, smul_mul_assoc, hx]

theorem rowAct_rhoFn (σ : Equiv.Perm ι) (x : MonoidAlgebra K (Sfin N)) :
    rowAct σ * rhoFn x = rhoFn x * rowAct σ :=
  rhoFn_comm _ (fun π => (labAct_rowAct π σ).symm) x

theorem del_rhoFn (i : ι) (x : MonoidAlgebra K (Sfin N)) :
    del i * rhoFn x = rhoFn x * del i :=
  rhoFn_comm _ (fun π => (labAct_del π i).symm) x

end GroupAlgebra

/-- The Stage 5 action of `K S_N` on `P_b(N)` is `rhoFn` on `Fn`. -/
theorem toFn_asAlgebraHom (x : MonoidAlgebra K (Sfin N)) (f : (injTuples b).Rk N →₀ K) :
    toFn ((permRep K (injTuples b) N).ρ.asAlgebraHom x f) = rhoFn x (toFn f) := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, rhoFn_single, one_smul]
    exact toFn_rho g f
  | hadd x y hx hy =>
    rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, LinearMap.add_apply]
  | hsmul c x hx =>
    rw [map_smul, LinearMap.smul_apply, map_smul, hx, map_smul, LinearMap.smul_apply]

/-- Vanishing transfers along the bridge. -/
theorem asAlgebraHom_eq_zero_iff (x : MonoidAlgebra K (Sfin N)) :
    (permRep K (injTuples b) N).ρ.asAlgebraHom x = 0 ↔
      ∀ F ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N)), rhoFn x F = 0 := by
  constructor
  · intro h F hF
    rw [← toFn_ofFn hF, ← toFn_asAlgebraHom, h, LinearMap.zero_apply, map_zero]
  · intro h
    apply LinearMap.ext
    intro f
    rw [LinearMap.zero_apply, ← ofFn_toFn ((permRep K (injTuples b) N).ρ.asAlgebraHom x f),
      toFn_asAlgebraHom, h _ (toFn_mem_P f), map_zero]

end BExact
