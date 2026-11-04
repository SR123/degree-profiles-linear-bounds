/- Cycle 010: the 1331 codes are exactly all ordered triples of eleven labels. -/
import RankThreeRowData
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace SelfContainedCycle010

abbrev Label := Fin 11
abbrev Triple := Fin 3 → Label

def encodeTriple (x : Triple) : Raw :=
  ⟨encode (x 0).val (x 1).val (x 2).val, by
    have h0 := (x 0).isLt; have h1 := (x 1).isLt; have h2 := (x 2).isLt
    dsimp [encode]; omega⟩

def decodeTriple (x : Raw) : Triple :=
  ![Fin.ofNat 11 (x.val/121), Fin.ofNat 11 (x.val/11), Fin.ofNat 11 x.val]

theorem decode_encode (x : Triple) : decodeTriple (encodeTriple x) = x := by
  funext i
  apply Fin.ext
  have h0 := (x 0).isLt; have h1 := (x 1).isLt; have h2 := (x 2).isLt
  fin_cases i
  · change ((121*(x 0).val+11*(x 1).val+(x 2).val)/121)%11 = (x 0).val
    omega
  · change ((121*(x 0).val+11*(x 1).val+(x 2).val)/11)%11 = (x 1).val
    omega
  · change (121*(x 0).val+11*(x 1).val+(x 2).val)%11 = (x 2).val
    omega

theorem encode_decode (x : Raw) : encodeTriple (decodeTriple x) = x := by
  apply Fin.ext
  have hx := x.isLt
  change 121*((x.val/121)%11)+11*((x.val/11)%11)+x.val%11 = x.val
  omega

def rawEquiv : Triple ≃ Raw where
  toFun := encodeTriple
  invFun := decodeTriple
  left_inv := decode_encode
  right_inv := encode_decode

theorem good_encode (x : Triple) (hx : Function.Injective x) : good (encodeTriple x).val = true := by
  have h := congrArg (fun f : Triple => ((f 0).val,(f 1).val,(f 2).val)) (decode_encode x)
  change digits (encodeTriple x).val = ((x 0).val,(x 1).val,(x 2).val) at h
  have h01 : (x 0).val ≠ (x 1).val := fun he => (by decide : (0 : Fin 3) ≠ 1) (hx (Fin.ext he))
  have h02 : (x 0).val ≠ (x 2).val := fun he => (by decide : (0 : Fin 3) ≠ 2) (hx (Fin.ext he))
  have h12 : (x 1).val ≠ (x 2).val := fun he => (by decide : (1 : Fin 3) ≠ 2) (hx (Fin.ext he))
  simp [good, h, h01, h02, h12]

end SelfContainedCycle010
