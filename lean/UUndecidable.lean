/-
Claude, 27 Sep 2026.  Undecidability, part H1: the published every-union theorem
(LICS 2008, Theorem 1 scope; manuscript `thm:undecidable`, first form).

Fix a prime `p` and any field `K` of characteristic `p` (for instance `ZMod p`).  Inputs are
normalized first-order sentences, coded by Mathlib's `Primcodable` instance.  The *promise* is:
`φ` is well formed and has no model of any size `n ≥ 1` (equivalently, by `hasRoot_iff`, no
nonempty instance of its translation has a common root).

**Theorem** (`undecidable_union_NS`, `undecidable_union_PC`).  For every nonempty proper subset
`A` of `{1, 2, 3, 4}`, there is no partial computable `D : Sentence →. Bool` that, on every
promised input `φ`, halts and returns `true` exactly when the NS (resp. ordinary-PC) type of the
translation of `φ` over `K` belongs to `A`.  Outside the promise `D` may do anything, including
diverge.  (Total computable deciders are a special case.)

The type is the actual type of the actual profile (`NSType`, `PCType`, relative to the linear
onset of `LinearFinal`; see `UWitCommon`).

Proof.  From Mathlib's `ComputablePred.halting_problem 0`.  For a code `c`, the machine
`univProg (encode c)` halts iff `c` halts on `0` (`UUniversal`).  The sentence
`ψ_τ ∧ θ_{univProg (encode c)}` is promised; it has type T1 if the machine halts and type `τ`
otherwise (`UTypes`); the map `c ↦ ψ_τ ∧ θ_{…}` is primitive recursive (`UComputable`).  Choose
`τ ∉ A` if `1 ∈ A`, and `τ ∈ A` if `1 ∉ A`.  Since every output of the reduction is promised,
`D` halts on all of them, and the composite is total computable (`decides_of_promise`).
-/
import UTypes
import UComputable

set_option autoImplicit false

namespace ClaudeUndec
open Nat.Partrec

section Final
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
include hp

/-- The promise: well formed, and no model of any size `n ≥ 1`. -/
def Promised (φ : Sentence) : Prop := WF φ ∧ ∀ n, 0 < n → ¬ HasModelOfSize φ n

/-- The reduction `c ↦ ψ_τ ∧ θ_{U(c)}`. -/
noncomputable def red (τ : ℕ) (c : Code) : Sentence :=
  conj (wit p τ) (theta (univProg (Encodable.encode c)))

omit hp in
theorem red_primrec (τ : ℕ) : Primrec (red p τ) :=
  (conj_primrec _).comp (theta_primrec.comp (univProg_primrec.comp Primrec.encode))

omit hp in
theorem red_promised (τ : ℕ) (c : Code) : Promised (red p τ c) :=
  ⟨conj_WF (wit_WF p τ) (theta_WF _),
    fun _ hn => conj_no_model _ (wit_WF p τ) (fun _ h => wit_no_model p τ h) _ hn⟩

omit hp [CharP K p] in
theorem red_halt (τ : ℕ) (c : Code) (h : (Code.eval c 0).Dom) :
    NSType (template (red p τ c) K) 1 :=
  conj_type_halt K _ _ ((eval_dom_iff_halts c).mp h)

theorem red_nonhalt (τ : ℕ) (hτ : τ ∈ ({1, 2, 3, 4} : Set ℕ)) (c : Code)
    (h : ¬ (Code.eval c 0).Dom) : NSType (template (red p τ c) K) τ :=
  (conj_type_nonhalt p K _ (wit_WF p τ) _ (fun h' => h ((eval_dom_iff_halts c).mpr h')) τ).mpr
    (wit_type p K τ hτ)

omit hp in
/-- A partial computable `D` that halts with the correct answer to `Q` on every promised input,
composed with a computable reduction into the promise class, decides `Q ∘ f`.  (The composite
halts everywhere, so it is a total computable function by `Partrec.of_eq_tot`.) -/
theorem decides_of_promise {α : Type} [Primcodable α] {D : Sentence →. Bool} (hD : Partrec D)
    {Q : Sentence → Prop} (hcorr : ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ Q φ))
    (f : α → Sentence) (hf : Computable f) (hprom : ∀ c, Promised (f c)) :
    ComputablePred fun c => Q (f c) := by
  have hdom : ∀ c, (D (f c)).Dom := fun c => by
    obtain ⟨b, hb, -⟩ := hcorr _ (hprom c)
    exact Part.dom_iff_mem.mpr ⟨b, hb⟩
  have hg : Computable fun c => (D (f c)).get (hdom c) :=
    Partrec.of_eq_tot (hD.comp hf) (fun c => Part.get_mem _)
  refine ComputablePred.computable_iff.mpr ⟨_, hg, funext fun c => propext ?_⟩
  obtain ⟨b, hb, hiff⟩ := hcorr _ (hprom c)
  rw [Part.mem_unique (Part.get_mem (hdom c)) hb]
  exact hiff.symm

/-- **Undecidability of every union of NS types** (published LICS 2008 scope, in the
all-finite-unsatisfiable promise form, for total-product-degree NS over `K`).  The algorithm is
partial computable and need only halt, with the correct answer, on promised inputs. -/
theorem undecidable_union_NS (A : Set ℕ) (hA : A ⊆ {1, 2, 3, 4}) (hne : A.Nonempty)
    (hprop : ∃ τ ∈ ({1, 2, 3, 4} : Set ℕ), τ ∉ A) :
    ¬ ∃ D : Sentence →. Bool, Partrec D ∧
      ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ ∃ τ ∈ A, NSType (template φ K) τ) := by
  rintro ⟨D, hD, hcorr⟩
  have hdec : ∀ τ, ComputablePred fun c : Code => ∃ τ' ∈ A, NSType (template (red p τ c) K) τ' :=
    fun τ => decides_of_promise hD hcorr (red p τ) (red_primrec p τ).to_comp (red_promised p τ)
  by_cases h1 : (1 : ℕ) ∈ A
  · -- choose `τ ∉ A`: the composite decides halting
    obtain ⟨τ, hτ, hτA⟩ := hprop
    refine ComputablePred.halting_problem 0 ((hdec τ).of_eq fun c => ?_)
    constructor
    · rintro ⟨τ', hτ'A, hty⟩
      by_contra hdom
      have := nsType_unique p _ hty (red_nonhalt p K τ hτ c hdom)
      subst this; exact hτA hτ'A
    · intro hdom; exact ⟨1, h1, red_halt p K τ c hdom⟩
  · -- choose `τ ∈ A`: the composite decides non-halting
    obtain ⟨τ, hτA⟩ := hne
    have hτ := hA hτA
    have hnot : ComputablePred fun c : Code => ¬ (Code.eval c 0).Dom := (hdec τ).of_eq fun c => by
      constructor
      · rintro ⟨τ', hτ'A, hty⟩ hdom
        have := nsType_unique p _ hty (red_halt p K τ c hdom)
        subst this; exact h1 hτ'A
      · intro hdom; exact ⟨τ, hτA, red_nonhalt p K τ hτ c hdom⟩
    exact ComputablePred.halting_problem 0 (by simpa only [not_not] using hnot.not)

/-- **Undecidability of every union of ordinary-PC types** (maximum-line-degree PC over `K`),
from the NS theorem and the agreement of types (`pcType_iff_nsType`); a proof without the
agreement of types is `undecidable_union_PC_direct` (part L). -/
theorem undecidable_union_PC (A : Set ℕ) (hA : A ⊆ {1, 2, 3, 4}) (hne : A.Nonempty)
    (hprop : ∃ τ ∈ ({1, 2, 3, 4} : Set ℕ), τ ∉ A) :
    ¬ ∃ D : Sentence →. Bool, Partrec D ∧
      ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ ∃ τ ∈ A, PCType (template φ K) τ) := by
  simp only [pcType_iff_nsType p]
  exact undecidable_union_NS p K A hA hne hprop

end Final

end ClaudeUndec
