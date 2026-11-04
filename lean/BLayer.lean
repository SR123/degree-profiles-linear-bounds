/-
Agent B, round 3 (26 Sep 2026).  Concrete layer objects on `P_b(N) = permRep K (injTuples b) N`,
via the bridge `BBridge`, and the reduction of `LayerData` (BThm7) to the genuinely hard
conditions.

* `SocV b N`  : the top cycles `Soc_b(N)` (preimage of `Soc univ univ univ` under `toFn`).
* `VpV b N`   : `V' = Σ_i range del_iᵀ` (preimage of `VpFn`, spanned by `delT i (P (univ \ i) univ)`).
* `GV b N`    : the row permutations `S_b`, transported to `P_b(N)`.
Unconditional facts (`b ≥ 1`, `x ∈ TupleRelations (b-1)`): `ρ_b x` maps `P_b(N)` into `SocV`
(`rel_mem_SocV`) and kills `VpV` (`rel_kills_VpV`); the row permutations commute with `K S_N`
(`GV_comm`).  Hence `LayerConditions` (DCP_b, (P1), (P2), T′_soc, T′_top for these concrete
objects) is all that `layer_step` still needs: `layerData_of_conditions`,
`topWitnessHypothesis_of_layerConditions` (CONDITIONAL stepping stone).
-/
import BBridge
import BThm7

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4
open SelfContainedCycle003 ClaudeCP DegreeProfilesReview.Shifted

variable {K : Type} [Field K] {N : ℕ}

/-! ### Transporting fewer rows -/

section Rows

variable {b b' : ℕ}

/-- Put a `b'`-row function on the rows `e(Fin b')` of `Fin b`. -/
def rowsUp (e : Fin b' ↪ Fin b) : Fn K (Fin b') (Fin N) →ₗ[K] Fn K (Fin b) (Fin N) where
  toFun F t := if (∀ i, i ∉ univ.map e → t i = none) then F (t ∘ e) else 0
  map_add' F G := by
    funext t
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c F := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem rowsUp_apply (e : Fin b' ↪ Fin b) (F : Fn K (Fin b') (Fin N)) (t : Fin b → Option (Fin N)) :
    rowsUp e F t = if (∀ i, i ∉ univ.map e → t i = none) then F (t ∘ e) else 0 := rfl

theorem labAct_rowsUp (e : Fin b' ↪ Fin b) (π : Equiv.Perm (Fin N)) :
    labAct π ∘ₗ rowsUp (K := K) e = rowsUp e ∘ₗ labAct π := by
  apply LinearMap.ext
  intro F
  funext t
  simp only [LinearMap.comp_apply, labAct_apply, rowsUp_apply, Option.map_eq_none_iff]
  rfl

theorem rowsUp_rhoFn (e : Fin b' ↪ Fin b) (x : MonoidAlgebra K (Sfin N)) :
    rhoFn x ∘ₗ rowsUp (K := K) e = rowsUp e ∘ₗ rhoFn x := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    rw [MonoidAlgebra.of_apply, rhoFn_single, rhoFn_single, one_smul, one_smul]
    exact labAct_rowsUp e _
  | hadd x y hx hy => rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hx, hy]
  | hsmul c x hx =>
    rw [map_smul, map_smul, LinearMap.smul_comp, LinearMap.comp_smul, hx]

/-- Every function in `P (e(Fin b')) univ` comes from `P univ univ` on `b'` rows. -/
theorem exists_rowsUp (e : Fin b' ↪ Fin b) {G : Fn K (Fin b) (Fin N)}
    (hG : G ∈ P (univ.map e) (univ : Finset (Fin N))) :
    ∃ F ∈ P (univ : Finset (Fin b')) (univ : Finset (Fin N)), rowsUp e F = G := by
  let F : Fn K (Fin b') (Fin N) := fun s => G (Function.extend e s (fun _ => none))
  have hext : ∀ s : Fin b' → Option (Fin N), ∀ j, Function.extend e s (fun _ => none) (e j) = s j :=
    fun s j => e.injective.extend_apply _ _ _
  have hext' : ∀ s : Fin b' → Option (Fin N), ∀ i, i ∉ univ.map e →
      Function.extend e s (fun _ => none) i = none := by
    intro s i hi
    rw [Function.extend_apply']
    rintro ⟨j, rfl⟩
    exact hi (Finset.mem_map_of_mem e (mem_univ j))
  refine ⟨F, fun s hs => ?_, ?_⟩
  · have g := hG _ hs
    refine ⟨fun j => ?_, fun j y _ => mem_univ y, fun j k y hj hk => ?_⟩
    · simp only [mem_univ, iff_true]
      rw [← hext s j]
      exact (g.dom (e j)).mpr (Finset.mem_map_of_mem e (mem_univ j))
    · apply e.injective
      exact g.inj (e j) (e k) y (by rw [hext]; exact hj) (by rw [hext]; exact hk)
  · funext t
    rw [rowsUp_apply]
    split_ifs with h
    · show G (Function.extend e (t ∘ e) (fun _ => none)) = G t
      congr 1
      funext i
      by_cases hi : i ∈ univ.map e
      · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
        exact hext _ j
      · rw [hext' _ i hi, h i hi]
    · push_neg at h
      obtain ⟨i, hi, hti⟩ := h
      by_contra h0
      exact hi (((hG t (Ne.symm h0)).dom i).mp hti)

/-- A group-algebra element killing `P_{b'}(N)` kills every `P_S(N)` with `|S| = b'`. -/
theorem rhoFn_kill_P {S : Finset (Fin b)} {x : MonoidAlgebra K (Sfin N)}
    (hx : (permRep K (injTuples S.card) N).ρ.asAlgebraHom x = 0) :
    ∀ G ∈ P S (univ : Finset (Fin N)), rhoFn x G = 0 := by
  intro G hG
  let e : Fin S.card ↪ Fin b :=
    ⟨fun j => (S.equivFin.symm j).1, fun j k h => S.equivFin.symm.injective (Subtype.ext h)⟩
  have hS : univ.map e = S := by
    ext i
    constructor
    · intro h
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp h
      exact (S.equivFin.symm j).2
    · intro h
      refine Finset.mem_map.mpr ⟨S.equivFin ⟨i, h⟩, mem_univ _, ?_⟩
      show (S.equivFin.symm (S.equivFin ⟨i, h⟩)).1 = i
      rw [Equiv.symm_apply_apply]
  rw [← hS] at hG
  obtain ⟨F, hF, rfl⟩ := exists_rowsUp e hG
  rw [← LinearMap.comp_apply, rowsUp_rhoFn, LinearMap.comp_apply,
    (asAlgebraHom_eq_zero_iff x).mp hx F hF, map_zero]

end Rows

/-! ### The transposed deletion -/

section DelT

variable {b : ℕ}

/-- `del_iᵀ`: `(delT i w)(t) = w(t without row i)` on injective total tuples `t`. -/
noncomputable def delT (i : Fin b) : Module.End K (Fn K (Fin b) (Fin N)) where
  toFun w t := by
    classical
    exact if Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t then w (update t i none) else 0
  map_add' w w' := by
    classical
    funext t
    by_cases h : Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t <;> simp [h]
  map_smul' c w := by
    classical
    funext t
    by_cases h : Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t <;> simp [h]

theorem delT_apply (i : Fin b) (w : Fn K (Fin b) (Fin N)) (t : Fin b → Option (Fin N)) :
    delT i w t = by
      classical
      exact if Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t then w (update t i none)
        else 0 := rfl

theorem good_map_iff (π : Equiv.Perm (Fin N)) (t : Fin b → Option (Fin N)) :
    Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) (fun j => (t j).map π.symm) ↔
      Good (univ : Finset (Fin b)) (univ : Finset (Fin N)) t := by
  constructor
  · intro g
    have := g.labAct π
    simpa using this
  · intro g
    refine ⟨fun j => ?_, fun j y _ => mem_univ y, fun j k y hj hk => ?_⟩
    · rw [← g.dom j]
      simp
    · obtain ⟨y1, hy1, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨y2, hy2, h2⟩ := Option.map_eq_some_iff.mp hk
      have : y2 = y1 := π.symm.injective h2
      subst this
      exact g.inj j k y2 hy1 hy2

theorem labAct_delT (i : Fin b) (π : Equiv.Perm (Fin N)) :
    labAct π * delT i = (delT i * labAct π : Module.End K (Fn K (Fin b) (Fin N))) := by
  classical
  apply LinearMap.ext
  intro w
  funext t
  simp only [Module.End.mul_apply, labAct_apply, delT_apply]
  rw [good_map_iff]
  split_ifs
  · rw [map_update]
    rfl
  · rfl

theorem rhoFn_delT (i : Fin b) (x : MonoidAlgebra K (Sfin N)) :
    delT i * rhoFn x = rhoFn x * delT i :=
  rhoFn_comm _ (fun π => (labAct_delT i π).symm) x

/-- `V' = Σ_i range del_iᵀ` inside `Fn`. -/
noncomputable def VpFn (b N : ℕ) : Submodule K (Fn K (Fin b) (Fin N)) :=
  Submodule.span K {F | ∃ i, ∃ w ∈ P (univ.erase i) (univ : Finset (Fin N)), F = delT i w}

end DelT

/-! ### The concrete layer objects -/

section Objects

variable (K) (b N : ℕ)

/-- `Soc_b(N)` inside `P_b(N)`. -/
noncomputable def SocV : Submodule K (permRep K (injTuples b) N).V :=
  (Soc (univ : Finset (Fin b)) univ (univ : Finset (Fin N))).comap toFn

/-- `V' = Σ_i range del_iᵀ` inside `P_b(N)`. -/
noncomputable def VpV : Submodule K (permRep K (injTuples b) N).V :=
  (VpFn (K := K) b N).comap toFn

/-- The row permutation `σ ∈ S_b`, transported to `P_b(N)`. -/
noncomputable def rowV (σ : Equiv.Perm (Fin b)) : Module.End K (permRep K (injTuples b) N).V :=
  ofFn ∘ₗ rowAct σ ∘ₗ toFn

/-- `S_b` acting on `P_b(N)`. -/
def GV : Set (Module.End K (permRep K (injTuples b) N).V) := {g | ∃ σ, g = rowV K b N σ}

end Objects

variable {b : ℕ}

theorem rhoFn_mem_P {x : MonoidAlgebra K (Sfin N)} {F : Fn K (Fin b) (Fin N)}
    (hF : F ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N))) :
    rhoFn x F ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N)) := by
  rw [← toFn_ofFn hF, ← toFn_asAlgebraHom]
  exact toFn_mem_P _

theorem rowAct_mem_P (σ : Equiv.Perm (Fin b)) {F : Fn K (Fin b) (Fin N)}
    (hF : F ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N))) :
    rowAct σ F ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N)) := by
  intro t ht
  have g := hF _ ht
  refine ⟨fun j => ?_, fun j y _ => mem_univ y, fun j k y hj hk => ?_⟩
  · simp only [mem_univ, iff_true]
    have := (g.dom (σ.symm j)).mpr (mem_univ _)
    simpa [comp_apply] using this
  · exact σ.symm.injective (g.inj (σ.symm j) (σ.symm k) y (by simpa using hj)
      (by simpa using hk))

/-- The row permutations commute with `K S_N`. -/
theorem GV_comm (g : Module.End K (permRep K (injTuples b) N).V) (hg : g ∈ GV K b N)
    (x : MonoidAlgebra K (Sfin N)) :
    g * (permRep K (injTuples b) N).ρ.asAlgebraHom x =
      (permRep K (injTuples b) N).ρ.asAlgebraHom x * g := by
  obtain ⟨σ, rfl⟩ := hg
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, rowV, LinearMap.comp_apply]
  apply (show Function.Injective (toFn (K := K) (b := b) (N := N)) from
    fun f g h => by rw [← ofFn_toFn f, h, ofFn_toFn])
  have h1 : toFn ((permRep K (injTuples b) N).ρ.asAlgebraHom x f) = rhoFn x (toFn f) :=
    toFn_asAlgebraHom x f
  have h2 : toFn ((permRep K (injTuples b) N).ρ.asAlgebraHom x (ofFn (rowAct σ (toFn f)))) =
      rhoFn x (rowAct σ (toFn f)) := by
    rw [toFn_asAlgebraHom, toFn_ofFn (rowAct_mem_P σ (toFn_mem_P f))]
  rw [h1, h2, toFn_ofFn (rowAct_mem_P σ (rhoFn_mem_P (toFn_mem_P f))),
    ← Module.End.mul_apply (rowAct σ), rowAct_rhoFn, Module.End.mul_apply]

/-- Tuple relations of support `b-1` map `P_b(N)` into `Soc_b(N)`. -/
theorem rel_mem_SocV {x : MonoidAlgebra K (Sfin N)}
    (hx : x ∈ TupleRelations K (b - 1) N) (v : (permRep K (injTuples b) N).V) :
    (permRep K (injTuples b) N).ρ.asAlgebraHom x v ∈ SocV K b N := by
  rw [SocV, Submodule.mem_comap, toFn_asAlgebraHom]
  refine ⟨rhoFn_mem_P (toFn_mem_P v), fun i _ => ?_⟩
  rw [← Module.End.mul_apply, del_rhoFn, Module.End.mul_apply]
  have hcard : (univ.erase i).card = b - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hx' : (permRep K (injTuples (univ.erase i).card) N).ρ.asAlgebraHom x = 0 := by
    rw [hcard]
    exact hx (b - 1) le_rfl
  exact rhoFn_kill_P hx' _ (del_mem_P' (toFn_mem_P v) i)
where
  del_mem_P' {F : Fn K (Fin b) (Fin N)} (hF : F ∈ P (univ : Finset (Fin b)) (univ : Finset (Fin N)))
      (i : Fin b) : del i F ∈ P (univ.erase i) (univ : Finset (Fin N)) := by
    rw [del, LinearMap.sum_apply]
    exact sum_mem fun x _ => P_mono (Finset.erase_subset x _) (part_mem_P hF i x)

/-- Tuple relations of support `b-1` kill `V'`. -/
theorem rel_kills_VpV {x : MonoidAlgebra K (Sfin N)}
    (hx : x ∈ TupleRelations K (b - 1) N) (v : (permRep K (injTuples b) N).V)
    (hv : v ∈ VpV K b N) : (permRep K (injTuples b) N).ρ.asAlgebraHom x v = 0 := by
  have hkill : ∀ F ∈ VpFn (K := K) b N, rhoFn x F = 0 := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨i, w, hw, rfl⟩ := hF
      have hcard : (univ.erase i).card = b - 1 := by
        rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
      have hx' : (permRep K (injTuples (univ.erase i).card) N).ρ.asAlgebraHom x = 0 := by
        rw [hcard]
        exact hx (b - 1) le_rfl
      rw [← Module.End.mul_apply, ← rhoFn_delT, Module.End.mul_apply, rhoFn_kill_P hx' w hw,
        map_zero]
    | zero => exact map_zero _
    | add F G _ _ hF hG => rw [map_add, hF, hG, add_zero]
    | smul c F _ hF => rw [map_smul, hF, smul_zero]
  rw [← ofFn_toFn ((permRep K (injTuples b) N).ρ.asAlgebraHom x v), toFn_asAlgebraHom,
    hkill _ hv, map_zero]

/-! ### The remaining (hard) layer conditions -/

section Conditions

variable (p : ℕ) [Fact p.Prime]

/-- **Hard layer conditions at level `b`** (a CONDITIONAL package): DCP_b (Prop. 8, from
Bowman–Doty–Martin in the paper), (P1), (P2), T′_soc, T′_top (Cor. 6, elementary in the paper, from
Thm. 5), for the concrete `Soc_b(N)`, `V'` and `S_b` of this file, `u = z^(p-1)`. -/
structure LayerConditions (a n : ℕ) (c : Fin a → K) (b : ℕ) where
  hDCP : ∀ φ : Module.End K (permRep K (injTuples b) (n + p ^ a)).V,
    (∀ v, φ v ∈ SocV K b (n + p ^ a)) → (∀ v ∈ VpV K b (n + p ^ a), φ v = 0) →
    (∀ g ∈ GV K b (n + p ^ a), g * φ = φ * g) →
    ∃ x ∈ TupleRelations K (b - 1) (n + p ^ a),
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom x = φ
  hP1 : ∀ v, (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
      SocV K b (n + p ^ a) → ∃ s ∈ SocV K b (n + p ^ a),
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v =
        (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s
  hP2 : ∀ v, (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
      VpV K b (n + p ^ a) → ∃ v' ∈ VpV K b (n + p ^ a),
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v =
        (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v'
  wS : Module.End K (permRep K (injTuples b) (n + p ^ a)).V
  hwS : ∀ s ∈ SocV K b (n + p ^ a), wS s ∈ SocV K b (n + p ^ a)
  hwSu : ∀ s ∈ SocV K b (n + p ^ a),
    (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1))
      (wS ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s)) =
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s
  hwSG : ∀ g ∈ GV K b (n + p ^ a), ∀ s ∈ SocV K b (n + p ^ a), g (wS s) = wS (g s)
  wT : Module.End K (permRep K (injTuples b) (n + p ^ a)).V
  hwT : ∀ v ∈ VpV K b (n + p ^ a), wT v ∈ VpV K b (n + p ^ a)
  hwTu : ∀ v,
    (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1))
      (wT ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v)) -
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
        VpV K b (n + p ^ a)
  hwTG : ∀ g ∈ GV K b (n + p ^ a), ∀ v, g (wT v) - wT (g v) ∈ VpV K b (n + p ^ a)

/-- The hard conditions and the (proved) easy facts give the full `LayerData`. -/
noncomputable def LayerConditions.toLayerData {a n : ℕ} {c : Fin a → K} {b : ℕ}
    (C : LayerConditions p a n c b) : LayerData p a n c b where
  Soc := SocV K b (n + p ^ a)
  V' := VpV K b (n + p ^ a)
  G := GV K b (n + p ^ a)
  hGA := GV_comm
  hJSoc := fun _ hx v => rel_mem_SocV hx v
  hJV' := fun _ hx v hv => rel_kills_VpV hx v hv
  hDCP := C.hDCP
  hP1 := C.hP1
  hP2 := C.hP2
  wS := C.wS
  hwS := C.hwS
  hwSu := C.hwSu
  hwSG := C.hwSG
  wT := C.wT
  hwT := C.hwT
  hwTu := C.hwTu
  hwTG := C.hwTG

/-- **Theorem A modulo the hard layer conditions** (CONDITIONAL stepping stone): if DCP_b, (P1),
(P2), T′ hold at every level `1 ≤ b ≤ r` for every generic `c` whenever `r < p^a` and `n ≥ W r`,
then `TopWitnessHypothesis p L W`. -/
theorem topWitnessHypothesis_of_layerConditions (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (W : ℕ → ℕ)
    (H : ∀ r a n : ℕ, r < p ^ a → W r ≤ n → ∀ c : Fin a → L, Generic p c →
      ∀ b, 1 ≤ b → b ≤ r → Nonempty (LayerConditions p a n c b)) :
    TopWitnessHypothesis p L W :=
  topWitnessHypothesis_of_layerData p L W fun r a n hr hn c hc b hb hbr =>
    ⟨(H r a n hr hn c hc b hb hbr).some.toLayerData p⟩

end Conditions

end BExact
