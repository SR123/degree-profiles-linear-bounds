/-
Agent B, round 3 (26 Sep 2026).  Label permutations on `Fn R ι α` (the `S_N`-action of the
paper), and their compatibility with the row operators of `BLemmaD`.

`labAct π F t = F (π⁻¹ ∘ t)` (labels relabelled by `π`).  It commutes with row permutations and
with the marginals `del i`, and it conjugates `part i x`, `put i x` to `part i (π x)`,
`put i (π x)`.  It maps `P_S(L)` and `Soc_Rr^S(L)` onto `P_S(πL)`, `Soc_Rr^S(πL)`.
-/
import BLemmaD

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace BExact

open Function Finset

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
  {α : Type} [Fintype α] [DecidableEq α]

/-- Label permutations. -/
def labAct (π : Equiv.Perm α) : Module.End R (Fn R ι α) where
  toFun F t := F (fun i => (t i).map π.symm)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem labAct_apply (π : Equiv.Perm α) (F : Fn R ι α) (t : ι → Option α) :
    labAct π F t = F (fun i => (t i).map π.symm) := rfl

theorem labAct_one : labAct (1 : Equiv.Perm α) = (1 : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro F
  funext t
  simp [labAct_apply]

theorem labAct_mul (π₁ π₂ : Equiv.Perm α) :
    labAct (π₁ * π₂) = (labAct π₁ * labAct π₂ : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro F
  funext t
  simp only [labAct_apply, Module.End.mul_apply, Option.map_map]
  congr 1

theorem map_update (f : α → α) (t : ι → Option α) (i : ι) (v : Option α) :
    (fun j => (update t i v j).map f) = update (fun j => (t j).map f) i (v.map f) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [update_of_ne h]

theorem labAct_part (π : Equiv.Perm α) (i : ι) (x : α) :
    labAct π * part i x = (part i (π x) * labAct π : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro F
  funext t
  simp only [Module.End.mul_apply, labAct_apply, part_apply, Option.map_eq_none_iff]
  rw [map_update]
  simp

theorem labAct_put (π : Equiv.Perm α) (i : ι) (x : α) :
    labAct π * put i x = (put i (π x) * labAct π : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro F
  funext t
  simp only [Module.End.mul_apply, labAct_apply, put_apply]
  rw [map_update]
  have : (t i).map π.symm = some x ↔ t i = some (π x) := by
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.mp h
      rw [hy, ← hyx, Equiv.apply_symm_apply]
    · intro h
      rw [h]
      simp
  by_cases h : t i = some (π x)
  · rw [if_pos (this.mpr h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

theorem labAct_del (π : Equiv.Perm α) (i : ι) :
    labAct π * del i = (del i * labAct π : Module.End R (Fn R ι α)) := by
  simp only [del, Finset.mul_sum, Finset.sum_mul, labAct_part]
  exact Equiv.sum_comp π (fun x => part i x * labAct π)

theorem labAct_rowAct (π : Equiv.Perm α) (σ : Equiv.Perm ι) :
    labAct π * rowAct σ = (rowAct σ * labAct π : Module.End R (Fn R ι α)) := by
  apply LinearMap.ext
  intro F
  funext t
  rfl

theorem Good.labAct {S : Finset ι} {L : Finset α} {t : ι → Option α} (π : Equiv.Perm α)
    (g : Good S L (fun i => (t i).map π.symm)) : Good S (L.map π.toEmbedding) t := by
  refine ⟨fun j => ?_, fun j y hy => ?_, fun j k y hj hk => ?_⟩
  · rw [← g.dom j]
    simp
  · have := g.val j (π.symm y) (by rw [hy]; rfl)
    rw [Finset.mem_map_equiv]
    exact this
  · exact g.inj j k (π.symm y) (by rw [hj]; rfl) (by rw [hk]; rfl)

theorem labAct_mem_P {S : Finset ι} {L : Finset α} {F : Fn R ι α} (hF : F ∈ P S L)
    (π : Equiv.Perm α) : labAct π F ∈ P S (L.map π.toEmbedding) := by
  intro t ht
  exact (hF _ ht).labAct π

theorem labAct_mem_Soc {Rr S : Finset ι} {L : Finset α} {F : Fn R ι α} (hF : F ∈ Soc Rr S L)
    (π : Equiv.Perm α) : labAct π F ∈ Soc Rr S (L.map π.toEmbedding) := by
  refine ⟨labAct_mem_P hF.1 π, fun i hi => ?_⟩
  rw [← Module.End.mul_apply, ← labAct_del, Module.End.mul_apply, hF.2 i hi, map_zero]

end BExact
