/-
Agent B, round 3 (26 Sep 2026).  Theorem 7 of `work/TPRIME_PROOF.md` (layer induction), in an
abstract form, and the conditional assembly of the support-`r` top witness from per-layer data.

STATUS: `layer_step` is unconditional linear algebra.  `topWitness_of_layerData` and
`topWitnessHypothesis_of_layerData` are CONDITIONAL stepping stones: they assume the per-layer
package `LayerData` ((P1), (P2), (T'_soc), (T'_top), DCP_b at level `b`), which the paper proves
from Thm. 5 / Cor. 6 (elementary, not yet in Lean) and Prop. 8 (DCP_b, from Bowman–Doty–Martin).

Abstract setting of `layer_step`: `ρ : A → End V` (here `A = K S_N`, `V = P_b(N)`), a two-sided
ideal-like set `J ⊆ A` (here `TupleRelations (b-1)`), subspaces `Soc` and `V'` of `V`, and a set
`G` of endomorphisms commuting with `ρ(A)` (here the row permutations `S_b`).
Endomorphisms of `Top = V/V'` are represented by endomorphisms of `V` preserving `V'`, and their
equivariance is only required modulo `V'`; this is all the proof uses.
-/
import PInduction
import PFinal

set_option autoImplicit false

namespace BExact

section Abstract

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {V : Type*} [AddCommGroup V]
  [Module K V]

/-- **Theorem 7 (layer step), abstract form.**  If `u w₀ u - u ∈ J` and the layer conditions hold,
then some `j ∈ J` gives `u (w₀ + j) u - u ∈ J` and `ρ (u (w₀ + j) u - u) = 0`. -/
theorem layer_step (ρ : A →ₐ[K] Module.End K V) (J : Set A)
    (hJadd : ∀ x ∈ J, ∀ y ∈ J, x + y ∈ J) (hJmul : ∀ x ∈ J, ∀ y z : A, y * x * z ∈ J)
    (Soc V' : Submodule K V) (G : Set (Module.End K V))
    (hGA : ∀ g ∈ G, ∀ a : A, g * ρ a = ρ a * g)
    (hJSoc : ∀ x ∈ J, ∀ v, ρ x v ∈ Soc) (hJV' : ∀ x ∈ J, ∀ v ∈ V', ρ x v = 0)
    (hDCP : ∀ φ : Module.End K V, (∀ v, φ v ∈ Soc) → (∀ v ∈ V', φ v = 0) →
      (∀ g ∈ G, g * φ = φ * g) → ∃ x ∈ J, ρ x = φ)
    (u : A)
    (hP1 : ∀ v, ρ u v ∈ Soc → ∃ s ∈ Soc, ρ u v = ρ u s)
    (hP2 : ∀ v, ρ u v ∈ V' → ∃ v' ∈ V', ρ u v = ρ u v')
    (wS : Module.End K V) (hwS : ∀ s ∈ Soc, wS s ∈ Soc)
    (hwSu : ∀ s ∈ Soc, ρ u (wS (ρ u s)) = ρ u s)
    (hwSG : ∀ g ∈ G, ∀ s ∈ Soc, g (wS s) = wS (g s))
    (wT : Module.End K V) (hwT : ∀ v ∈ V', wT v ∈ V')
    (hwTu : ∀ v, ρ u (wT (ρ u v)) - ρ u v ∈ V')
    (hwTG : ∀ g ∈ G, ∀ v, g (wT v) - wT (g v) ∈ V')
    (w₀ : A) (hw₀ : u * w₀ * u - u ∈ J) :
    ∃ j ∈ J, u * (w₀ + j) * u - u ∈ J ∧ ρ (u * (w₀ + j) * u - u) = 0 := by
  set E := ρ (u * w₀ * u - u) with hE
  have hEsoc : ∀ v, E v ∈ Soc := hJSoc _ hw₀
  have hEV' : ∀ v ∈ V', E v = 0 := hJV' _ hw₀
  have hEform : ∀ v, E v = ρ u (ρ w₀ (ρ u v)) - ρ u v := by
    intro v
    rw [hE, map_sub, map_mul, map_mul]
    rfl
  -- `E` kills every `v` with `u v ∈ V'` (uses (P2))
  have hEker : ∀ v, ρ u v ∈ V' → E v = 0 := by
    intro v hv
    obtain ⟨v', hv', he⟩ := hP2 v hv
    have h1 : E v = E v' := by rw [hEform, hEform, he]
    rw [h1, hEV' v' hv']
  -- `u w_S` is the identity on the image of `E` (uses (P1), (T'_soc))
  have hEu : ∀ v, ρ u (wS (E v)) = E v := by
    intro v
    have h1 : E v = ρ u (ρ w₀ (ρ u v) - v) := by rw [hEform, map_sub]
    obtain ⟨s, hs, hus⟩ := hP1 _ (h1 ▸ hEsoc v)
    rw [h1, hus, hwSu s hs]
  -- `E w_T u = E` (uses (T'_top))
  have hEwT : ∀ v, E (wT (ρ u v)) = E v := by
    intro v
    have h1 : ρ u (wT (ρ u v) - v) ∈ V' := by rw [map_sub]; exact hwTu v
    have h2 := hEker _ h1
    rwa [map_sub, sub_eq_zero] at h2
  -- the map handed to DCP
  let φ : Module.End K V := -(wS * E * wT)
  have hφ : ∀ v, φ v = -wS (E (wT v)) := fun v => rfl
  obtain ⟨x, hxJ, hx⟩ := hDCP φ
    (fun v => by rw [hφ]; exact Soc.neg_mem (hwS _ (hEsoc _)))
    (fun v hv => by rw [hφ, hEV' _ (hwT v hv), map_zero, neg_zero])
    (fun g hg => by
      apply LinearMap.ext
      intro v
      rw [Module.End.mul_apply, Module.End.mul_apply, hφ, hφ, map_neg,
        hwSG g hg _ (hEsoc _), ← Module.End.mul_apply g E, hGA g hg, Module.End.mul_apply]
      have h1 : g (wT v) = wT (g v) + (g (wT v) - wT (g v)) := by abel
      rw [h1, map_add, hEV' _ (hwTG g hg v), add_zero])
  refine ⟨x, hxJ, ?_, ?_⟩
  · have : u * (w₀ + x) * u - u = (u * w₀ * u - u) + u * x * u := by noncomm_ring
    rw [this]
    exact hJadd _ hw₀ _ (hJmul x hxJ u u)
  · have : u * (w₀ + x) * u - u = (u * w₀ * u - u) + u * x * u := by noncomm_ring
    rw [this, map_add]
    apply LinearMap.ext
    intro v
    rw [LinearMap.add_apply, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx,
      hφ, hEwT, map_neg, hEu, ← hE, add_neg_cancel]
    rfl

end Abstract

section Concrete

open DegreeProfilesReview.SymRep DegreeProfilesReview.ConcreteM4 SelfContainedCycle003 ClaudeCP
open DegreeProfilesReview.Shifted

variable {K : Type} [Field K] (p : ℕ) [Fact p.Prime]

theorem tupleRelations_add {r t : ℕ} {x y : MonoidAlgebra K (Sfin t)}
    (hx : x ∈ TupleRelations K r t) (hy : y ∈ TupleRelations K r t) :
    x + y ∈ TupleRelations K r t := fun b hb => by
  rw [map_add, hx b hb, hy b hb, add_zero]

theorem tupleRelations_mul {r t : ℕ} {x : MonoidAlgebra K (Sfin t)}
    (hx : x ∈ TupleRelations K r t) (y z : MonoidAlgebra K (Sfin t)) :
    y * x * z ∈ TupleRelations K r t := fun b hb => by
  rw [map_mul, map_mul, hx b hb, mul_zero, zero_mul]

/-- **Per-layer data at level `b`** (a CONDITIONAL package, see the header): subspaces `Soc`,
`V'` of `P_b(N)`, a set `G` commuting with `K S_N`, and the layer conditions of Thm. 7 for
`u = z^(p-1)` and `J = TupleRelations (b-1)`. -/
structure LayerData (a n : ℕ) (c : Fin a → K) (b : ℕ) where
  Soc : Submodule K (permRep K (injTuples b) (n + p ^ a)).V
  V' : Submodule K (permRep K (injTuples b) (n + p ^ a)).V
  G : Set (Module.End K (permRep K (injTuples b) (n + p ^ a)).V)
  hGA : ∀ g ∈ G, ∀ x : MonoidAlgebra K (Sfin (n + p ^ a)),
    g * (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom x =
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom x * g
  hJSoc : ∀ x ∈ TupleRelations K (b - 1) (n + p ^ a), ∀ v,
    (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom x v ∈ Soc
  hJV' : ∀ x ∈ TupleRelations K (b - 1) (n + p ^ a), ∀ v ∈ V',
    (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom x v = 0
  hDCP : ∀ φ : Module.End K (permRep K (injTuples b) (n + p ^ a)).V, (∀ v, φ v ∈ Soc) →
    (∀ v ∈ V', φ v = 0) → (∀ g ∈ G, g * φ = φ * g) →
    ∃ x ∈ TupleRelations K (b - 1) (n + p ^ a),
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom x = φ
  hP1 : ∀ v, (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
      Soc → ∃ s ∈ Soc,
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v =
        (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s
  hP2 : ∀ v, (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈
      V' → ∃ v' ∈ V',
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v =
        (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v'
  wS : Module.End K (permRep K (injTuples b) (n + p ^ a)).V
  hwS : ∀ s ∈ Soc, wS s ∈ Soc
  hwSu : ∀ s ∈ Soc,
    (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1))
      (wS ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s)) =
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) s
  hwSG : ∀ g ∈ G, ∀ s ∈ Soc, g (wS s) = wS (g s)
  wT : Module.End K (permRep K (injTuples b) (n + p ^ a)).V
  hwT : ∀ v ∈ V', wT v ∈ V'
  hwTu : ∀ v,
    (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1))
      (wT ((permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v)) -
      (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom (zEltP p a n c ^ (p - 1)) v ∈ V'
  hwTG : ∀ g ∈ G, ∀ v, g (wT v) - wT (g v) ∈ V'

/-- One layer: a support-`(b-1)` witness and the layer data at level `b ≥ 1` give a support-`b`
witness. -/
theorem topWitness_step {a n : ℕ} {c : Fin a → K} {b : ℕ} (hb : 1 ≤ b)
    {w₀ : MonoidAlgebra K (Sfin (n + p ^ a))} (hw₀ : IsTopWitness p (b - 1) a n c w₀)
    (D : LayerData p a n c b) : ∃ w, IsTopWitness p b a n c w := by
  obtain ⟨j, -, hJ, h0⟩ := layer_step (permRep K (injTuples b) (n + p ^ a)).ρ.asAlgebraHom
    (TupleRelations K (b - 1) (n + p ^ a)) (fun x hx y hy => tupleRelations_add hx hy)
    (fun x hx y z => tupleRelations_mul hx y z) D.Soc D.V' D.G D.hGA D.hJSoc D.hJV' D.hDCP
    (zEltP p a n c ^ (p - 1)) D.hP1 D.hP2 D.wS D.hwS D.hwSu D.hwSG D.wT D.hwT D.hwTu D.hwTG
    w₀ hw₀
  refine ⟨w₀ + j, fun b' hb' => ?_⟩
  rcases Nat.lt_or_ge b' b with h | h
  · exact hJ b' (by omega)
  · obtain rfl : b' = b := le_antisymm hb' h
    exact h0

/-- **Conditional assembly.**  Layer data at every level `1 ≤ b ≤ r` give a support-`r`
top witness. -/
theorem topWitness_of_layerData {a n : ℕ} {c : Fin a → K} (r : ℕ)
    (D : ∀ b, 1 ≤ b → b ≤ r → LayerData p a n c b) : ∃ w, IsTopWitness p r a n c w := by
  induction r with
  | zero => exact ⟨0, base_top_witness a n c⟩
  | succ r ih =>
    obtain ⟨w₀, hw₀⟩ := ih (fun b hb hbr => D b hb (by omega))
    exact topWitness_step p (b := r + 1) (by omega) hw₀ (D (r + 1) (by omega) le_rfl)

/-- Generic parameters exist over an algebraically closed field of characteristic `p`. -/
theorem exists_generic' (L : Type) [Field L] [IsAlgClosed L] [CharP L p] (a : ℕ) :
    ∃ c : Fin a → L, Generic p c := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨Fin.elim0, ?_⟩
    intro g _
    funext i
    exact i.elim0
  · letI : Algebra (ZMod p) L := ZMod.algebra L p
    obtain ⟨c, hc⟩ := exists_generic_galoisP p a (by omega)
    let φ : GaloisField p a →+* L :=
      (IsAlgClosed.lift : GaloisField p a →ₐ[ZMod p] L).toRingHom
    exact ⟨φ ∘ c, generic_mapP φ hc⟩

/-- **Conditional assembly with a budget.**  If layer data exist at every level `1 ≤ b ≤ r` for
every generic `c` whenever `r < p^a` and `n ≥ W r`, then `TopWitnessHypothesis p L W`.  (With
`W r = 2r - 1` this is Theorem A modulo the layer data.) -/
theorem topWitnessHypothesis_of_layerData (L : Type) [Field L] [IsAlgClosed L] [CharP L p]
    (W : ℕ → ℕ)
    (H : ∀ r a n : ℕ, r < p ^ a → W r ≤ n → ∀ c : Fin a → L, Generic p c →
      ∀ b, 1 ≤ b → b ≤ r → Nonempty (LayerData p a n c b)) :
    TopWitnessHypothesis p L W := by
  intro r a n hr hn
  obtain ⟨c, hc⟩ := exists_generic' p L a
  exact ⟨c, hc, topWitness_of_layerData p r (fun b hb hbr => (H r a n hr hn c hc b hb hbr).some)⟩

end Concrete

end BExact
