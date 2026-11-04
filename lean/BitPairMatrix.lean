/- Cycle 009: a sound, kernel-reduced checker for sparse matrices over F4. -/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace SelfContainedCycle009

abbrev Bits := ℕ × ℕ

def addBits (x y : Bits) : Bits := (x.1 ^^^ y.1, x.2 ^^^ y.2)

def scaleBits (c : Fin 4) (x : Bits) : Bits :=
  if c = 0 then (0,0) else if c = 1 then x else
    if c = 2 then (x.2, x.1 ^^^ x.2) else (x.1 ^^^ x.2, x.1)

def combineBits {ι : Type} : List (ι × Fin 4) → (ι → Bits) → Bits
  | [], _ => (0,0)
  | (i,c) :: row, v => addBits (scaleBits c (v i)) (combineBits row v)

variable {K : Type} [Field K] [CharP K 2]

def boolValue (b : Bool) : K := if b then 1 else 0

def bitsValue (t : K) (x : Bits) (j : ℕ) : K :=
  boolValue (x.1.testBit j) + t * boolValue (x.2.testBit j)

def codeValue (t : K) (c : Fin 4) : K :=
  if c = 0 then 0 else if c = 1 then 1 else if c = 2 then t else 1+t

theorem boolValue_xor (x y : Bool) :
    boolValue (K := K) (x ^^ y) = boolValue x + boolValue y := by
  cases x <;> cases y <;> simp [boolValue, CharTwo.add_self_eq_zero]

theorem bitsValue_add (t : K) (x y : Bits) (j : ℕ) :
    bitsValue t (addBits x y) j = bitsValue t x j + bitsValue t y j := by
  simp only [bitsValue, addBits, Nat.testBit_xor, boolValue_xor]
  ring

omit [CharP K 2] in
theorem bitsValue_zero (t : K) (j : ℕ) : bitsValue t (0,0) j = 0 := by
  simp [bitsValue, boolValue]

theorem bitsValue_scale (t : K) (ht : t^2+t+1=0) (c : Fin 4) (x : Bits) (j : ℕ) :
    bitsValue t (scaleBits c x) j = codeValue t c * bitsValue t x j := by
  have ht2 : t*t = t+1 := by
    rw [← pow_two]
    apply CharTwo.add_eq_zero.mp
    simpa only [add_assoc] using ht
  fin_cases c
  · simp [scaleBits, codeValue, bitsValue_zero]
  · simp [scaleBits, codeValue]
  · change bitsValue t (x.2, x.1 ^^^ x.2) j = t * bitsValue t x j
    simp only [bitsValue, Nat.testBit_xor, boolValue_xor]
    simp only [mul_add, ← mul_assoc, ht2]
    ring
  · change bitsValue t (x.1 ^^^ x.2, x.1) j = (1+t) * bitsValue t x j
    simp only [bitsValue, Nat.testBit_xor, boolValue_xor]
    rw [add_mul, one_mul, mul_add, ← mul_assoc, ht2]
    simp only [add_mul, one_mul]
    have hc := CharTwo.add_self_eq_zero
      (t * boolValue (K := K) (x.2.testBit j))
    linear_combination -hc

def rowValue {ι : Type} (t : K) : List (ι × Fin 4) → (ι → K) → K
  | [], _ => 0
  | (i,c) :: row, v => codeValue t c * v i + rowValue t row v

theorem combineBits_sound {ι : Type} (t : K) (ht : t^2+t+1=0)
    (row : List (ι × Fin 4)) (v : ι → Bits) (j : ℕ) :
    bitsValue t (combineBits row v) j = rowValue t row (fun i => bitsValue t (v i) j) := by
  induction row with
  | nil => exact bitsValue_zero t j
  | cons a row ih =>
    rcases a with ⟨i,c⟩
    simp only [combineBits, rowValue, bitsValue_add, bitsValue_scale t ht, ih]

omit [CharP K 2] in
theorem bitsValue_unit (t : K) (i j : ℕ) :
    bitsValue t (2^i,0) j = if i=j then 1 else 0 := by
  simp [bitsValue, boolValue, Nat.testBit_two_pow]

def sparseMatrix {ι : Type} [DecidableEq ι] (t : K)
    (rows : ι → List (ι × Fin 4)) : Matrix ι ι K :=
  fun i j => rowValue t (rows i) (fun k => if k=j then 1 else 0)

def bitsMatrix {n : ℕ} (t : K) (rows : Fin n → Bits) : Matrix (Fin n) (Fin n) K :=
  fun i j => bitsValue t (rows i) j.val

omit [CharP K 2] in
theorem rowValue_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : K) (row : List (ι × Fin 4)) (v : ι → K) :
    (∑ j, rowValue t row (fun k => if k=j then 1 else 0) * v j) = rowValue t row v := by
  induction row with
  | nil => simp [rowValue]
  | cons a row ih =>
    rcases a with ⟨i,c⟩
    simp only [rowValue, add_mul, Finset.sum_add_distrib, ih]
    simp [mul_ite, ite_mul]

theorem inverse_certificate_sound {n : ℕ} (t : K) (ht : t^2+t+1=0)
    (rows : Fin n → List (Fin n × Fin 4)) (inv : Fin n → Bits)
    (h : ∀ i, combineBits (rows i) inv = (2^i.val,0)) :
    sparseMatrix t rows * bitsMatrix t inv = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑ k, rowValue t (rows i) (fun l => if l=k then 1 else 0) *
    bitsValue t (inv k) j.val) = _
  rw [rowValue_mul, ← combineBits_sound t ht, h i, bitsValue_unit]
  simp [Matrix.one_apply, Fin.val_inj]

end SelfContainedCycle009
