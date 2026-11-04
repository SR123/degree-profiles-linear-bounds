/- Cycle 008: construct a group-algebra inner inverse from a polynomial relation. -/
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false
namespace SelfContainedCycle008
open Polynomial

variable {K A : Type} [Field K] [Ring A] [Algebra K A]

/-- The witness is a polynomial expression in the same two algebra elements. -/
noncomputable def polynomialInverse (z a : A) (P : Polynomial K) : A :=
  -(P.coeff 0)⁻¹ • (a * aeval (z * a) P.divX)

theorem polynomial_innerInverse (z a : A) (P : Polynomial K) (h0 : P.coeff 0 ≠ 0)
    (hP : aeval (z * a) P * z = 0) :
    z * polynomialInverse z a P * z = z := by
  have he := congrArg (fun Q : Polynomial K => aeval (z * a) Q * z) (X_mul_divX_add P)
  simp only [map_add, map_mul, aeval_X, aeval_C, add_mul, hP] at he
  have hmul : z * (a * aeval (z * a) P.divX) * z = -(P.coeff 0) • z := by
    rw [← mul_assoc]
    rw [neg_smul]
    apply eq_neg_of_add_eq_zero_left
    simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, neg_smul] using he
  unfold polynomialInverse
  rw [mul_smul_comm, smul_mul_assoc, hmul, smul_smul]
  simp [h0]

variable {V : Type} [AddCommGroup V] [Module K V]

/-- z*a maps image(z) to itself, without any square-zero hypothesis. -/
def imageStep (z a : Module.End K V) : Module.End K (LinearMap.range z) where
  toFun x := ⟨z (a x), ⟨a x, rfl⟩⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp

theorem imageStep_pow (z a : Module.End K V) (k : ℕ) (x : LinearMap.range z) :
    ((imageStep z a ^ k) x : V) = ((z * a)^k) x := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [pow_succ', pow_succ']
    change z (a ((imageStep z a ^ k) x : V)) = z (a (((z * a)^k) x))
    rw [hk]

theorem imageStep_aeval (z a : Module.End K V) (P : Polynomial K)
    (x : LinearMap.range z) :
    (aeval (imageStep z a) P x : V) = aeval (z * a) P x := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simpa only [map_add, LinearMap.add_apply, Submodule.coe_add] using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      LinearMap.smul_apply, Submodule.coe_smul, imageStep_pow]

/-- Finite-dimensional injectivity supplies a polynomial certificate with nonzero constant. -/
theorem imageStep_polynomial [FiniteDimensional K V] (z a : Module.End K V)
    (hi : Function.Injective (imageStep z a)) :
    ∃ P : Polynomial K, P.coeff 0 ≠ 0 ∧ aeval (z * a) P * z = 0 := by
  let P := minpoly K (imageStep z a)
  refine ⟨P, LinearMap.minpoly_coeff_zero_of_injective hi, ?_⟩
  apply LinearMap.ext
  intro v
  have hh := congrArg (fun L : Module.End K (LinearMap.range z) => (L ⟨z v, ⟨v, rfl⟩⟩ : V))
    (minpoly.aeval K (imageStep z a))
  dsimp only at hh
  rw [imageStep_aeval] at hh
  exact hh

/-- A faithful finite-dimensional action suffices: the inverse remains inside A. -/
theorem innerInverse_of_imageStep [FiniteDimensional K V]
    (ρ : A →ₐ[K] Module.End K V) (hρ : Function.Injective ρ) (z a : A)
    (hi : Function.Injective (imageStep (ρ z) (ρ a))) : ∃ b : A, z * b * z = z := by
  obtain ⟨P, h0, hP⟩ := imageStep_polynomial (ρ z) (ρ a) hi
  refine ⟨polynomialInverse z a P, polynomial_innerInverse z a P h0 ?_⟩
  apply hρ
  rw [map_zero, map_mul, ← Polynomial.aeval_algHom_apply, map_mul]
  exact hP

/-- The finite rank test is equivalent to existence of an algebra inner inverse. -/
theorem innerInverse_iff_imageStep [FiniteDimensional K V]
    (ρ : A →ₐ[K] Module.End K V) (hρ : Function.Injective ρ) (z : A) :
    (∃ b : A, z * b * z = z) ↔ ∃ a : A, Function.Injective (imageStep (ρ z) (ρ a)) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hid (x : LinearMap.range (ρ z)) : imageStep (ρ z) (ρ b) x = x := by
      obtain ⟨v, hv⟩ := x.2
      apply Subtype.ext
      change ρ z (ρ b x) = x
      rw [← hv]
      have hh := congrArg (fun w : A => ρ w v) hb
      simpa only [map_mul, Module.End.mul_apply] using hh
    intro x y hxy
    simpa only [hid] using hxy
  · rintro ⟨a, ha⟩
    exact innerInverse_of_imageStep ρ hρ z a ha

/-- Algebra homomorphisms preserve the explicit polynomial witness. -/
theorem polynomialInverse_map {B : Type} [Ring B] [Algebra K B]
    (ρ : A →ₐ[K] B) (z a : A) (P : Polynomial K) :
    ρ (polynomialInverse z a P) = polynomialInverse (ρ z) (ρ a) P := by
  simp only [polynomialInverse, map_smul, map_mul, ← Polynomial.aeval_algHom_apply]

/-- A relation on a module yields the same group-algebra witness, without faithfulness. -/
theorem polynomial_action_innerInverse {B : Type} [Ring B] [Algebra K B]
    (ρ : A →ₐ[K] B) (z a : A) (P : Polynomial K) (h0 : P.coeff 0 ≠ 0)
    (hP : aeval (ρ z * ρ a) P * ρ z = 0) :
    ρ z * ρ (polynomialInverse z a P) * ρ z = ρ z := by
  rw [polynomialInverse_map]
  exact polynomial_innerInverse (ρ z) (ρ a) P h0 hP

end SelfContainedCycle008
