/- Cycle 006: exact seven-label certificate for the first support-two case.
The finite parity checks are kernel-reduced; no native_decide is used.
The final theorem is over every characteristic-two field containing a root of t²+t+1.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SelfContainedCycle006

abbrev Label := Fin 7
abbrev Pair := Label × Label
abbrev Map7 := Label → Label

def firstGen : Map7 := ![1, 0, 3, 2, 4, 5, 6]
def secondGen : Map7 := ![2, 3, 0, 1, 4, 5, 6]
def z0List : List Map7 := [id, firstGen]
def z1List : List Map7 := [id, secondGen]
def a0List : List Map7 := [
  ![0, 1, 2, 5, 4, 3, 6],
  ![0, 1, 2, 6, 4, 5, 3],
  ![0, 1, 6, 3, 4, 5, 2],
  ![0, 5, 2, 3, 4, 1, 6],
  ![0, 1, 2, 5, 3, 4, 6],
  ![0, 1, 2, 5, 4, 6, 3],
  ![0, 1, 3, 4, 2, 5, 6],
  ![0, 1, 3, 5, 4, 2, 6],
  ![0, 1, 4, 2, 3, 5, 6],
  ![0, 1, 5, 2, 4, 3, 6],
  ![0, 1, 5, 3, 2, 4, 6],
  ![0, 1, 5, 3, 4, 6, 2],
  ![0, 2, 4, 3, 1, 5, 6],
  ![0, 2, 5, 3, 4, 1, 6],
  ![0, 4, 1, 3, 2, 5, 6],
  ![0, 5, 1, 3, 4, 2, 6],
  ![0, 1, 2, 6, 5, 4, 3],
  ![0, 1, 4, 5, 2, 3, 6],
  ![0, 1, 5, 4, 3, 2, 6],
  ![0, 1, 6, 3, 5, 4, 2],
  ![0, 4, 2, 5, 1, 3, 6],
  ![0, 4, 2, 6, 1, 5, 3],
  ![0, 5, 2, 6, 4, 1, 3],
  ![0, 1, 2, 4, 5, 6, 3],
  ![0, 1, 4, 3, 5, 6, 2],
  ![0, 1, 4, 5, 3, 2, 6],
  ![0, 1, 4, 6, 3, 5, 2],
  ![0, 1, 5, 6, 4, 3, 2]]
def a1List : List Map7 := [
  ![0, 1, 3, 2, 4, 5, 6],
  ![0, 1, 4, 3, 2, 5, 6],
  ![0, 3, 2, 1, 4, 5, 6],
  ![0, 4, 2, 3, 1, 5, 6],
  ![0, 1, 2, 4, 5, 3, 6],
  ![0, 1, 2, 4, 6, 5, 3],
  ![0, 1, 2, 6, 3, 5, 4],
  ![0, 1, 2, 6, 4, 3, 5],
  ![0, 1, 3, 5, 4, 2, 6],
  ![0, 1, 4, 3, 5, 2, 6],
  ![0, 1, 5, 2, 4, 3, 6],
  ![0, 1, 5, 3, 4, 6, 2],
  ![0, 3, 2, 4, 1, 5, 6],
  ![0, 4, 2, 1, 3, 5, 6],
  ![0, 1, 2, 4, 3, 6, 5],
  ![0, 1, 2, 5, 6, 3, 4],
  ![0, 1, 4, 5, 2, 3, 6],
  ![0, 1, 4, 6, 2, 5, 3],
  ![0, 1, 5, 4, 3, 2, 6],
  ![0, 1, 5, 6, 4, 2, 3],
  ![0, 4, 2, 6, 1, 5, 3],
  ![0, 4, 5, 3, 1, 2, 6],
  ![0, 5, 2, 6, 4, 1, 3],
  ![0, 1, 2, 4, 5, 6, 3],
  ![0, 1, 4, 3, 5, 6, 2],
  ![0, 1, 4, 5, 3, 2, 6],
  ![0, 1, 4, 6, 3, 5, 2],
  ![0, 1, 5, 6, 4, 3, 2]]

def pairMap (s : Map7) (x : Pair) : Pair := (s x.1, s x.2)
def compList (L R : List Map7) : List Map7 :=
  L.flatMap (fun s => R.map (fun t => s ∘ t))
def triple (L M R : List Map7) : List Map7 := compList (compList L M) R

def even0 : List Map7 :=
  triple z0List a0List z0List ++ triple z1List a1List z0List ++
  triple z1List a0List z1List ++ triple z0List a1List z1List ++
  triple z1List a1List z1List ++ z0List

def even1 : List Map7 :=
  triple z1List a0List z0List ++ triple z0List a1List z0List ++
  triple z0List a0List z1List ++ triple z1List a1List z0List ++
  triple z1List a0List z1List ++ triple z0List a1List z1List ++ z1List

-- Check genuine permutations; arbitrary endomorphisms would not suffice for the application.
theorem certificate_bijective :
    ((a0List ++ a1List ++ z0List ++ z1List).all
      (fun s => decide (Function.Bijective s))) = true := by decide

def pairIndex (x : Pair) : ℕ := 7 * x.1.val + x.2.val

theorem pairIndex_injective : Function.Injective pairIndex := by
  intro x y h
  have hx := x.2.isLt
  have hy := y.2.isLt
  change 7 * x.1.val + x.2.val = 7 * y.1.val + y.2.val at h
  apply Prod.ext <;> apply Fin.ext <;> omega

def parityImage : List Map7 → Pair → ℕ
  | [], _ => 0
  | s :: L, y => (2 ^ pairIndex (pairMap s y)) ^^^ parityImage L y

-- Only 49 vector identities are reduced, not 2401 separately expanded matrix entries.
theorem certificate_bits0 : ∀ y : Pair, parityImage even0 y = 0 := by decide

theorem certificate_bits1 : ∀ y : Pair, parityImage even1 y = 0 := by decide

theorem parity_step (b : Bool) (n : ℕ) :
    (b ^^ decide (n % 2 = 1)) = decide ((n + if b then 1 else 0) % 2 = 1) := by
  cases b with
  | false => simp
  | true =>
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with hn | hn <;> simp [Nat.add_mod, hn]

theorem parityImage_bit (L : List Map7) (x y : Pair) :
    (parityImage L y).testBit (pairIndex x) =
      decide ((L.countP (fun s => decide (x = pairMap s y))) % 2 = 1) := by
  induction L with
  | nil => simp [parityImage]
  | cons s L ih =>
    rw [parityImage, Nat.testBit_xor, Nat.testBit_two_pow, ih]
    have he : pairIndex (pairMap s y) = pairIndex x ↔ x = pairMap s y :=
      ⟨fun h => (pairIndex_injective h).symm, fun h => congrArg pairIndex h.symm⟩
    simp only [he]
    simpa only [List.countP_cons] using
      parity_step (decide (x = pairMap s y)) (L.countP (fun s => decide (x = pairMap s y)))

theorem parity_count_even (L : List Map7) (h : ∀ y : Pair, parityImage L y = 0) :
    ∀ x y : Pair, (L.countP (fun s => decide (x = pairMap s y))) % 2 = 0 := by
  intro x y
  have hb := parityImage_bit L x y
  rw [h y, Nat.zero_testBit] at hb
  have hn : ¬ (L.countP (fun s => decide (x = pairMap s y))) % 2 = 1 := by
    simpa using hb.symm
  have hm := Nat.mod_lt (L.countP (fun s => decide (x = pairMap s y))) (by omega : 0 < 2)
  omega

theorem certificate_even0 :
    ∀ x y : Pair, (even0.countP (fun s => decide (x = pairMap s y))) % 2 = 0 :=
  parity_count_even even0 certificate_bits0

theorem certificate_even1 :
    ∀ x y : Pair, (even1.countP (fun s => decide (x = pairMap s y))) % 2 = 0 :=
  parity_count_even even1 certificate_bits1

variable {K : Type} [Field K]

def mapMatrix (s : Map7) : Matrix Pair Pair K :=
  fun x y => if x = pairMap s y then 1 else 0

def listMatrix : List Map7 → Matrix Pair Pair K
  | [] => 0
  | s :: L => mapMatrix s + listMatrix L

theorem listMatrix_append (L R : List Map7) :
    listMatrix (K := K) (L ++ R) = listMatrix L + listMatrix R := by
  induction L with
  | nil => simp [listMatrix]
  | cons s L ih => simp [listMatrix, ih, add_assoc]

theorem listMatrix_entry (L : List Map7) (x y : Pair) :
    listMatrix (K := K) L x y = (L.countP (fun s => decide (x = pairMap s y)) : K) := by
  induction L with
  | nil => simp [listMatrix]
  | cons s L ih =>
    rw [listMatrix, Matrix.add_apply, ih]
    by_cases h : x = pairMap s y
    · simp [mapMatrix, h, add_comm]
    · simp [mapMatrix, h]

variable [CharP K 2]

theorem even_list_zero (L : List Map7)
    (h : ∀ x y : Pair, (L.countP (fun s => decide (x = pairMap s y))) % 2 = 0) :
    listMatrix (K := K) L = 0 := by
  ext x y
  rw [listMatrix_entry]
  apply (CharP.cast_eq_zero_iff K 2 _).mpr
  exact Nat.dvd_of_mod_eq_zero (h x y)

theorem even0_matrix_zero : listMatrix (K := K) even0 = 0 := even_list_zero even0 certificate_even0

theorem even1_matrix_zero : listMatrix (K := K) even1 = 0 := even_list_zero even1 certificate_even1

end SelfContainedCycle006
