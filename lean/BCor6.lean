/-
Agent B, round 3 (26 Sep 2026).  The formal parts of Thm. 5 / Cor. 6 of `work/TPRIME_PROOF.md`,
in abstract form (ambient module `M`, nilpotent `z` with `z^p = 0`, `u = z^(p-1)`).

* `nilSection_spec` (Lemma 5, nilpotent form): if `Q = ⊕_{i<p} z^i Q₀` (as the image of an
  injective map), `f : E → Q` commutes with `z`, and `σ` is a section of `f` on `Q`, then
  `τ(Σ z^i q_i) = Σ z^i σ(q_i)` is a `z`-linear section which commutes with every `γ` commuting
  with `z`, preserving `Q₀` and intertwined by `σ` (so `S_b`-linearity is kept).
* `P1_of_decomp` ((P1) of Cor. 6): if `P = P₀ ⊕ P_B`, `z P₀ = 0`, `z P ⊆ P_B`, and the socle is
  `S = S₀ ⊕ X` with `S₀ ⊆ P₀`, `z S₀ = 0` and `X = ⊕_{i<p} z^i C`, then `uP ∩ S ⊆ uS`.
* `Tsoc_of_decomp` ((T′_soc) of Cor. 6): under the same decomposition of `S` there is `w_S` with
  `w_S S ⊆ S`, `u w_S u = u` on `S`, commuting on `S` with every `g` that commutes with `z` and
  preserves `S₀` and `C`.
All unconditional.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

namespace BExact

open Finset

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- `v ↦ Σ_{i<p} z^i v_i` on `Fin p → C`. -/
def zSum (p : ℕ) (z : Module.End K M) (C : Submodule K M) : (Fin p → C) →ₗ[K] M :=
  ∑ i : Fin p, (z ^ (i : ℕ)) ∘ₗ C.subtype ∘ₗ LinearMap.proj i

theorem zSum_apply (p : ℕ) (z : Module.End K M) (C : Submodule K M) (v : Fin p → C) :
    zSum p z C v = ∑ i : Fin p, (z ^ (i : ℕ)) (v i) := by
  rw [zSum, LinearMap.sum_apply]
  rfl

/-- Multiplying by `z` shifts the coefficients (using `z^p = 0` on `C`). -/
theorem z_zSum (p : ℕ) (z : Module.End K M) (C : Submodule K M)
    (hzp : ∀ c ∈ C, (z ^ (p + 1)) c = 0) (v : Fin (p + 1) → C) :
    z (zSum (p + 1) z C v) = zSum (p + 1) z C (Fin.cons 0 (fun i => v i.castSucc)) := by
  rw [zSum_apply, zSum_apply, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, ZeroMemClass.coe_zero, map_zero, zero_add, Fin.cons_succ,
    Fin.coe_castSucc, Fin.val_last, Fin.val_succ]
  have hlast : z ((z ^ p) (v (Fin.last p))) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hzp _ (v (Fin.last p)).2
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.mul_apply, ← pow_succ']

/-! ### (P1) -/

theorem pow_mem_of_mem (z : Module.End K M) (P : Submodule K M) (hPz : ∀ v ∈ P, z v ∈ P) :
    ∀ k : ℕ, ∀ v ∈ P, (z ^ k) v ∈ P := by
  intro k
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ', Module.End.mul_apply]
    exact hPz _ (ih v hv)

/-- **(P1) of Cor. 6, abstract.** -/
theorem P1_of_decomp (p : ℕ) (hp : 2 ≤ p) (z : Module.End K M)
    (P P₀ PB S S₀ C : Submodule K M)
    (hP₀B : ∀ v ∈ P₀, v ∈ PB → v = 0)
    (hzP₀ : ∀ v ∈ P₀, z v = 0) (hzP : ∀ v ∈ P, z v ∈ PB) (hPz : ∀ v ∈ P, z v ∈ P)
    (hzpP : ∀ v ∈ P, (z ^ p) v = 0)
    (hS : ∀ s ∈ S, ∃ s₀ ∈ S₀, ∃ x ∈ LinearMap.range (zSum p z C), s = s₀ + x)
    (hS₀P : S₀ ≤ P₀) (hCS : C ≤ S) (hSP : S ≤ P)
    (hinj : Function.Injective (zSum p z C)) :
    ∀ v ∈ P, (z ^ (p - 1)) v ∈ S → ∃ s ∈ S, (z ^ (p - 1)) v = (z ^ (p - 1)) s := by
  intro v hv hw
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hw ⊢
  have hzC : ∀ c ∈ C, (z ^ (q + 1)) c = 0 := fun c hc => hzpP c (hSP (hCS hc))
  obtain ⟨s₀, hs₀, x, ⟨c, rfl⟩, hsx⟩ := hS _ hw
  -- `z w = 0`, hence `z x = 0`
  have hzw : z ((z ^ q) v) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hzpP v hv
  have hzx : z (zSum (q + 1) z C c) = 0 := by
    have h1 := congrArg z hsx
    rw [hzw, map_add, hzP₀ _ (hS₀P hs₀), zero_add] at h1
    exact h1.symm
  -- so all coefficients but the last vanish
  have hshift := z_zSum q z C hzC c
  rw [hzx] at hshift
  have h0 : (Fin.cons 0 (fun i => c i.castSucc) : Fin (q + 1) → C) = 0 :=
    hinj (by rw [← hshift, map_zero])
  have hc : ∀ i : Fin q, c i.castSucc = 0 := fun i => by
    have := congrFun h0 i.succ
    simpa using this
  have hx : zSum (q + 1) z C c = (z ^ q) (c (Fin.last q)) := by
    rw [zSum_apply, Fin.sum_univ_castSucc]
    simp [hc]
  -- the retained component vanishes
  have hq1 : 1 ≤ q := by omega
  have hwB : (z ^ q) v ∈ PB := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [pow_succ', Module.End.mul_apply]
    exact hzP _ (pow_mem_of_mem z P hPz q' v hv)
  have hxB : (z ^ q) (c (Fin.last q)) ∈ PB := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [pow_succ', Module.End.mul_apply]
    exact hzP _ (pow_mem_of_mem z P hPz q' _ (hSP (hCS (c _).2)))
  have hs₀0 : s₀ = 0 := by
    apply hP₀B s₀ (hS₀P hs₀)
    have : s₀ = (z ^ q) v - (z ^ q) (c (Fin.last q)) := by
      rw [← hx]
      exact eq_sub_of_add_eq hsx.symm
    rw [this]
    exact PB.sub_mem hwB hxB
  refine ⟨c (Fin.last q), hCS (c _).2, ?_⟩
  rw [hsx, hs₀0, zero_add, hx]

/-! ### Helpers on `zSum` -/

theorem zSum_single (p : ℕ) (z : Module.End K M) (C : Submodule K M) (j : Fin p) (c : C) :
    zSum p z C (Pi.single j c) = (z ^ (j : ℕ)) c := by
  rw [zSum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

theorem pow_zSum_top (q : ℕ) (z : Module.End K M) (C : Submodule K M)
    (hzC : ∀ c ∈ C, (z ^ (q + 1)) c = 0) (c : Fin (q + 1) → C) :
    (z ^ q) (zSum (q + 1) z C c) = (z ^ q) (c 0) := by
  rw [zSum_apply, map_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Module.End.one_apply, Fin.val_succ]
  rw [Finset.sum_eq_zero, add_zero]
  intro i _
  rw [← Module.End.mul_apply, ← pow_add, show q + (i + 1) = i + (q + 1) by omega, pow_add,
    Module.End.mul_apply, hzC _ (c _).2, map_zero]

theorem comm_zSum (p : ℕ) (z g : Module.End K M) (hg : g * z = z * g) (C : Submodule K M)
    (hgC : ∀ c ∈ C, g c ∈ C) (c : Fin p → C) :
    g (zSum p z C c) = zSum p z C (fun i => ⟨g (c i), hgC _ (c i).2⟩) := by
  rw [zSum_apply, zSum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.mul_apply, (Commute.pow_right hg (i : ℕ)).eq, Module.End.mul_apply]

theorem C_le_range (p : ℕ) (hp : 1 ≤ p) (z : Module.End K M) (C : Submodule K M) :
    C ≤ LinearMap.range (zSum p z C) := by
  intro c hc
  refine ⟨Pi.single ⟨0, hp⟩ ⟨c, hc⟩, ?_⟩
  rw [zSum_single]
  simp

/-- The coefficient map `X = range (zSum) → (Fin p → C)`, extended to `M` through complements. -/
theorem exists_coeff (p : ℕ) (z : Module.End K M) (C S₀ S : Submodule K M)
    (hinj : Function.Injective (zSum p z C))
    (hS : ∀ s ∈ S, ∃ s₀ ∈ S₀, ∃ x ∈ LinearMap.range (zSum p z C), s = s₀ + x)
    (hSind : ∀ s₀ ∈ S₀, ∀ x ∈ LinearMap.range (zSum p z C), s₀ + x = 0 → s₀ = 0)
    (hS₀S : S₀ ≤ S) (hXS : LinearMap.range (zSum p z C) ≤ S) :
    ∃ co : M →ₗ[K] (Fin p → C), ∀ s₀ ∈ S₀, ∀ c : Fin p → C, co (s₀ + zSum p z C c) = c := by
  set X := LinearMap.range (zSum p z C)
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl S
  have hc : IsCompl X (S₀ ⊔ W) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp hx'
      have hwS : w ∈ S := by
        have : w = x - y := by rw [← hyw]; abel
        rw [this]
        exact S.sub_mem (hXS hx) (hS₀S hy)
      have hw0 : w = 0 := (Submodule.disjoint_def.mp hW.disjoint) w hwS hw
      rw [hw0, add_zero] at hyw
      have hy0 : y = 0 := hSind y hy (-x) (X.neg_mem hx) (by rw [hyw, add_neg_cancel])
      rw [← hyw, hy0]
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro m
      have hm : m ∈ S ⊔ W := by rw [hW.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp hm
      obtain ⟨s₀, hs₀, x, hx, rfl⟩ := hS s hs
      have e1 : s₀ + x + w = x + (s₀ + w) := by abel
      rw [e1]
      exact Submodule.add_mem_sup hx (Submodule.add_mem_sup hs₀ hw)
  let e := LinearEquiv.ofInjective (zSum p z C) hinj
  refine ⟨e.symm.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl X (S₀ ⊔ W) hc, fun s₀ hs₀ c => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_add]
  have h1 : Submodule.linearProjOfIsCompl X (S₀ ⊔ W) hc s₀ = 0 :=
    Submodule.linearProjOfIsCompl_apply_right' hc s₀ (Submodule.mem_sup_left hs₀)
  have h2 : Submodule.linearProjOfIsCompl X (S₀ ⊔ W) hc (zSum p z C c) = e c := by
    have : (zSum p z C c) = ((e c : X) : M) := (LinearEquiv.ofInjective_apply _ _).symm
    rw [this, Submodule.linearProjOfIsCompl_apply_left]
  rw [h1, h2, map_zero, zero_add, LinearEquiv.symm_apply_apply]

/-! ### (T′_soc) -/

/-- **(T′_soc) of Cor. 6, abstract** (`p = q + 1`, `u = z^q`). -/
theorem Tsoc_of_decomp (q : ℕ) (hq : 1 ≤ q) (z : Module.End K M) (S S₀ C : Submodule K M)
    (hS : ∀ s ∈ S, ∃ s₀ ∈ S₀, ∃ x ∈ LinearMap.range (zSum (q + 1) z C), s = s₀ + x)
    (hSind : ∀ s₀ ∈ S₀, ∀ x ∈ LinearMap.range (zSum (q + 1) z C), s₀ + x = 0 → s₀ = 0)
    (hS₀S : S₀ ≤ S) (hXS : LinearMap.range (zSum (q + 1) z C) ≤ S)
    (hzS₀ : ∀ s ∈ S₀, z s = 0) (hzC : ∀ c ∈ C, (z ^ (q + 1)) c = 0)
    (hinj : Function.Injective (zSum (q + 1) z C)) :
    ∃ wS : Module.End K M, (∀ s ∈ S, wS s ∈ S) ∧
      (∀ s ∈ S, (z ^ q) (wS ((z ^ q) s)) = (z ^ q) s) ∧
      (∀ g : Module.End K M, g * z = z * g → (∀ s ∈ S₀, g s ∈ S₀) → (∀ c ∈ C, g c ∈ C) →
        ∀ s ∈ S, g (wS s) = wS (g s)) := by
  obtain ⟨co, hco⟩ := exists_coeff (q + 1) z C S₀ S hinj hS hSind hS₀S hXS
  let wS : Module.End K M := C.subtype ∘ₗ LinearMap.proj (Fin.last q) ∘ₗ co
  have hwS : ∀ s₀ ∈ S₀, ∀ c : Fin (q + 1) → C, wS (s₀ + zSum (q + 1) z C c) = c (Fin.last q) := by
    intro s₀ hs₀ c
    show ((co (s₀ + zSum (q + 1) z C c)) (Fin.last q) : M) = _
    rw [hco s₀ hs₀ c]
  have hCS : C ≤ S := le_trans (C_le_range (q + 1) (by omega) z C) hXS
  have hzqS₀ : ∀ s ∈ S₀, (z ^ q) s = 0 := by
    intro s hs
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply, hzS₀ s hs, map_zero]
  refine ⟨wS, fun s _ => hCS (C.subtype_apply _ ▸ (co s (Fin.last q)).2), fun s hs => ?_,
    fun g hg hgS₀ hgC s hs => ?_⟩
  · obtain ⟨s₀, hs₀, x, ⟨c, rfl⟩, rfl⟩ := hS s hs
    have hus : (z ^ q) (s₀ + zSum (q + 1) z C c) =
        0 + zSum (q + 1) z C (Pi.single (Fin.last q) (c 0)) := by
      rw [map_add, hzqS₀ s₀ hs₀, pow_zSum_top q z C hzC, zSum_single, Fin.val_last]
    rw [hus, hwS 0 S₀.zero_mem, Pi.single_eq_same, ← hus]
    rw [map_add, hzqS₀ s₀ hs₀, zero_add, pow_zSum_top q z C hzC]
  · obtain ⟨s₀, hs₀, x, ⟨c, rfl⟩, rfl⟩ := hS s hs
    rw [hwS s₀ hs₀ c, map_add, comm_zSum (q + 1) z g hg C hgC c, hwS _ (hgS₀ s₀ hs₀)]

/-! ### Lemma 5, nilpotent form -/

/-- **Lemma 5 (relative splitting), nilpotent form.**  `Q = ⊕_{i ≤ q} z^i Q₀`. -/
theorem nilSection_spec (q : ℕ) (z : Module.End K M) (E Q Q₀ : Submodule K M)
    (f σ : Module.End K M) (hσ : ∀ x ∈ Q, σ x ∈ E ∧ f (σ x) = x)
    (hfz : ∀ e ∈ E, f (z e) = z (f e)) (hzE : ∀ e ∈ E, z e ∈ E)
    (hzpE : ∀ e ∈ E, (z ^ (q + 1)) e = 0)
    (hQ : LinearMap.range (zSum (q + 1) z Q₀) = Q) (hinj : Function.Injective (zSum (q + 1) z Q₀))
    (hzQ₀ : ∀ c ∈ Q₀, (z ^ (q + 1)) c = 0) :
    ∃ τ : Module.End K M, (∀ x ∈ Q, τ x ∈ E ∧ f (τ x) = x) ∧ (∀ x ∈ Q, τ (z x) = z (τ x)) ∧
      (∀ γ : Module.End K M, γ * z = z * γ → (∀ c ∈ Q₀, γ c ∈ Q₀) →
        (∀ c ∈ Q₀, σ (γ c) = γ (σ c)) → ∀ x ∈ Q, τ (γ x) = γ (τ x)) := by
  obtain ⟨co, hco⟩ := exists_coeff (q + 1) z Q₀ ⊥ Q hinj
    (fun s hs => ⟨0, Submodule.zero_mem _, s, hQ ▸ hs, (zero_add s).symm⟩)
    (fun s₀ hs₀ _ _ _ => (Submodule.mem_bot K).mp hs₀) bot_le hQ.le
  have hco' : ∀ c : Fin (q + 1) → Q₀, co (zSum (q + 1) z Q₀ c) = c := fun c => by
    have := hco 0 (Submodule.zero_mem _) c
    rwa [zero_add] at this
  let τ : Module.End K M :=
    ∑ i : Fin (q + 1), (z ^ (i : ℕ)) ∘ₗ σ ∘ₗ Q₀.subtype ∘ₗ LinearMap.proj i ∘ₗ co
  have hτ : ∀ c : Fin (q + 1) → Q₀,
      τ (zSum (q + 1) z Q₀ c) = ∑ i : Fin (q + 1), (z ^ (i : ℕ)) (σ (c i)) := by
    intro c
    show (∑ i : Fin (q + 1), (z ^ (i : ℕ)) ∘ₗ σ ∘ₗ Q₀.subtype ∘ₗ LinearMap.proj i ∘ₗ co)
      (zSum (q + 1) z Q₀ c) = _
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.comp_apply, hco']
    rfl
  have hQ₀Q : ∀ c ∈ Q₀, c ∈ Q := fun c hc => hQ ▸ C_le_range (q + 1) (by omega) z Q₀ hc
  have hzkE : ∀ k : ℕ, ∀ e ∈ E, (z ^ k) e ∈ E := pow_mem_of_mem z E hzE
  have hfzk : ∀ k : ℕ, ∀ e ∈ E, f ((z ^ k) e) = (z ^ k) (f e) := by
    intro k
    induction k with
    | zero => intro e _; rfl
    | succ k ih =>
      intro e he
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, hfz _ (hzkE k e he), ih e he]
  refine ⟨τ, fun x hx => ?_, fun x hx => ?_, fun γ hγ hγQ₀ hσγ x hx => ?_⟩
  · rw [← hQ] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [hτ]
    refine ⟨sum_mem fun i _ => hzkE _ _ (hσ _ (hQ₀Q _ (c i).2)).1, ?_⟩
    rw [map_sum, zSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfzk _ _ (hσ _ (hQ₀Q _ (c i).2)).1, (hσ _ (hQ₀Q _ (c i).2)).2]
  · rw [← hQ] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [z_zSum q z Q₀ hzQ₀ c, hτ, hτ, map_sum, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.cons_zero, ZeroMemClass.coe_zero, map_zero, zero_add, Fin.cons_succ,
      Fin.val_succ, Fin.coe_castSucc, Fin.val_last]
    have hlast : z ((z ^ q) (σ (c (Fin.last q)))) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hzpE _ (hσ _ (hQ₀Q _ (c _).2)).1
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pow_succ', Module.End.mul_apply]
  · rw [← hQ] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [comm_zSum (q + 1) z γ hγ Q₀ hγQ₀ c, hτ, hτ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (z ^ (i : ℕ)) (σ (γ (c i))) = γ ((z ^ (i : ℕ)) (σ (c i)))
    rw [hσγ _ (c i).2, ← Module.End.mul_apply (z ^ (i : ℕ)) γ,
      ← (Commute.pow_right hγ (i : ℕ)).eq, Module.End.mul_apply]

/-! ### Theorem 5, abstract step -/

theorem zSum_mem (p : ℕ) (z : Module.End K M) (C F : Submodule K M) (hzF : ∀ e ∈ F, z e ∈ F)
    (hCF : C ≤ F) (c : Fin p → C) : zSum p z C c ∈ F := by
  rw [zSum_apply]
  exact sum_mem fun i _ => pow_mem_of_mem z F hzF _ _ (hCF (c i).2)

/-- **Theorem 5, one filtration step (abstract).**  Let `F ⊆ F'` with `f : F' → Q` having kernel
`F`, `Q = ⊕_{i ≤ q} z^i Q₀`, a section `σ`, and `F = S₀ ⊕ (⊕_i z^i C)`.  Then
`F' = S₀ ⊕ (⊕_i z^i C')` for some `C' ⊇ C`, and `C'` is stable under every `γ` commuting with `z`,
preserving `C` and `Q₀`, and intertwined by `σ` on `Q₀`. -/
theorem thm5_step (q : ℕ) (z : Module.End K M) (F F' Q Q₀ S₀ C : Submodule K M)
    (f σ : Module.End K M) (hFF' : F ≤ F') (hker : ∀ e ∈ F', f e = 0 → e ∈ F)
    (hfF : ∀ e ∈ F, f e = 0) (hfQ : ∀ e ∈ F', f e ∈ Q)
    (hσ : ∀ x ∈ Q, σ x ∈ F' ∧ f (σ x) = x) (hfz : ∀ e ∈ F', f (z e) = z (f e))
    (hzF' : ∀ e ∈ F', z e ∈ F') (hzpF' : ∀ e ∈ F', (z ^ (q + 1)) e = 0)
    (hQ : LinearMap.range (zSum (q + 1) z Q₀) = Q) (hinjQ : Function.Injective (zSum (q + 1) z Q₀))
    (hzQ₀ : ∀ c ∈ Q₀, (z ^ (q + 1)) c = 0)
    (hF : ∀ s ∈ F, ∃ s₀ ∈ S₀, ∃ x ∈ LinearMap.range (zSum (q + 1) z C), s = s₀ + x)
    (hFind : ∀ s₀ ∈ S₀, ∀ x ∈ LinearMap.range (zSum (q + 1) z C), s₀ + x = 0 → s₀ = 0)
    (hS₀F : S₀ ≤ F) (hCF : C ≤ F) (hinjC : Function.Injective (zSum (q + 1) z C)) :
    ∃ C' : Submodule K M, C ≤ C' ∧ C' ≤ F' ∧
      (∀ s ∈ F', ∃ s₀ ∈ S₀, ∃ x ∈ LinearMap.range (zSum (q + 1) z C'), s = s₀ + x) ∧
      (∀ s₀ ∈ S₀, ∀ x ∈ LinearMap.range (zSum (q + 1) z C'), s₀ + x = 0 → s₀ = 0) ∧
      Function.Injective (zSum (q + 1) z C') ∧
      (∀ γ : Module.End K M, γ * z = z * γ → (∀ c ∈ C, γ c ∈ C) → (∀ c ∈ Q₀, γ c ∈ Q₀) →
        (∀ c ∈ Q₀, σ (γ c) = γ (σ c)) → ∀ c ∈ C', γ c ∈ C') := by
  obtain ⟨τ, hτ1, hτz, hτγ⟩ := nilSection_spec q z F' Q Q₀ f σ hσ hfz hzF' hzpF' hQ hinjQ hzQ₀
  have hQ₀Q : ∀ c ∈ Q₀, c ∈ Q := fun c hc => hQ ▸ C_le_range (q + 1) (by omega) z Q₀ hc
  have hzQ : ∀ x ∈ Q, z x ∈ Q := by
    intro x hx
    rw [← hQ] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    rw [z_zSum q z Q₀ hzQ₀ c]
    exact LinearMap.mem_range_self _ _
  have hτpow : ∀ k : ℕ, ∀ x ∈ Q, τ ((z ^ k) x) = (z ^ k) (τ x) := by
    intro k
    induction k with
    | zero => intro x _; rfl
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        hτz _ (pow_mem_of_mem z Q hzQ k x hx), ih x hx]
  have hfpow : ∀ k : ℕ, ∀ e ∈ F', f ((z ^ k) e) = (z ^ k) (f e) := by
    intro k
    induction k with
    | zero => intro e _; rfl
    | succ k ih =>
      intro e he
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        hfz _ (pow_mem_of_mem z F' hzF' k e he), ih e he]
  have hzF : ∀ e ∈ F, z e ∈ F := fun e he => hker _ (hzF' e (hFF' he)) (by
    rw [hfz e (hFF' he), hfF e he, map_zero])
  set D := Q₀.map τ
  let C' := C ⊔ D
  -- splitting an element of `C'`
  have hsplit : ∀ c ∈ C', ∃ a ∈ C, ∃ b ∈ Q₀, c = a + τ b := by
    intro c hc
    obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.mp hc
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hd
    exact ⟨a, ha, b, hb, rfl⟩
  -- the key computation: a vanishing combination has vanishing parts
  have hkey : ∀ s₀ ∈ S₀, ∀ c : Fin (q + 1) → C', s₀ + zSum (q + 1) z C' c = 0 →
      s₀ = 0 ∧ ∀ i, (c i : M) = 0 := by
    intro s₀ hs₀ c h0
    choose a ha b hb hab using fun i => hsplit (c i) (c i).2
    have hsum : zSum (q + 1) z C' c =
        zSum (q + 1) z C (fun i => ⟨a i, ha i⟩) + τ (zSum (q + 1) z Q₀ (fun i => ⟨b i, hb i⟩)) := by
      rw [zSum_apply, zSum_apply, zSum_apply, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hab i, map_add, hτpow _ _ (hQ₀Q _ (hb i))]
    have hQmem : zSum (q + 1) z Q₀ (fun i => ⟨b i, hb i⟩) ∈ Q := hQ ▸ LinearMap.mem_range_self _ _
    have haF : zSum (q + 1) z C (fun i => ⟨a i, ha i⟩) ∈ F := zSum_mem _ z C F hzF hCF _
    -- apply `f`
    have hf0 := congrArg f h0
    rw [hsum, map_add, map_add, hfF _ (hS₀F hs₀), hfF _ haF, (hτ1 _ hQmem).2, zero_add,
      zero_add, map_zero] at hf0
    have hb0 : (fun i => (⟨b i, hb i⟩ : Q₀)) = 0 := hinjQ (by rw [hf0, map_zero])
    have hb0' : ∀ i, b i = 0 := fun i => by
      have := congrFun hb0 i
      simpa using this
    have hbz : zSum (q + 1) z Q₀ (fun i => ⟨b i, hb i⟩) = 0 := by rw [hb0, map_zero]
    rw [hsum, hbz, map_zero, add_zero] at h0
    have hs₀0 : s₀ = 0 := hFind s₀ hs₀ _ (LinearMap.mem_range_self _ _) h0
    rw [hs₀0, zero_add] at h0
    have ha0 : (fun i => (⟨a i, ha i⟩ : C)) = 0 := hinjC (by rw [h0, map_zero])
    refine ⟨hs₀0, fun i => ?_⟩
    have := congrFun ha0 i
    rw [hab i, hb0' i, map_zero, add_zero]
    simpa using this
  refine ⟨C', le_sup_left, ?_, fun s hs => ?_, fun s₀ hs₀ x hx h0 => ?_, ?_, ?_⟩
  · refine sup_le (le_trans hCF hFF') ?_
    intro d hd
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hd
    exact (hτ1 b (hQ₀Q b hb)).1
  · -- decompose `s ∈ F'`
    have hfs := hfQ s hs
    rw [← hQ] at hfs
    obtain ⟨d, hd⟩ := hfs
    have hrest : s - τ (f s) ∈ F := by
      refine hker _ (F'.sub_mem hs (hτ1 _ (hfQ s hs)).1) ?_
      rw [map_sub, (hτ1 _ (hfQ s hs)).2, sub_self]
    obtain ⟨s₀, hs₀, x, ⟨c, rfl⟩, hx⟩ := hF _ hrest
    let c' : Fin (q + 1) → C' := fun i =>
      ⟨c i + τ (d i), C'.add_mem (le_sup_left (a := C) (c i).2)
        (le_sup_right (a := C) (Submodule.mem_map_of_mem (d i).2))⟩
    refine ⟨s₀, hs₀, zSum (q + 1) z C' c', LinearMap.mem_range_self _ _, ?_⟩
    have hτd : τ (f s) = ∑ i : Fin (q + 1), (z ^ (i : ℕ)) (τ (d i)) := by
      rw [← hd, zSum_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => hτpow _ _ (hQ₀Q _ (d i).2)
    have : s = s₀ + zSum (q + 1) z C c + τ (f s) := by rw [← hx]; abel
    rw [this, hτd, zSum_apply, zSum_apply, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_add]
  · obtain ⟨c, rfl⟩ := hx
    exact (hkey s₀ hs₀ c h0).1
  · intro c c' hcc
    have h0 : (0 : M) + zSum (q + 1) z C' (c - c') = 0 := by
      rw [zero_add, map_sub, hcc, sub_self]
    have := (hkey 0 S₀.zero_mem _ h0).2
    funext i
    have hi := this i
    simp only [Pi.sub_apply, Submodule.coe_sub, sub_eq_zero] at hi
    exact Subtype.ext hi
  · intro γ hγ hγC hγQ₀ hσγ c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit c hc
    rw [map_add, ← hτγ γ hγ hγQ₀ hσγ b (hQ₀Q b hb)]
    exact C'.add_mem (le_sup_left (a := C) (hγC a ha))
      (le_sup_right (a := C) (Submodule.mem_map_of_mem (hγQ₀ b hb)))

end BExact
