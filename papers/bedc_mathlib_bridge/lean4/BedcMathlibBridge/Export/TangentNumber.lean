import BedcMathlibBridge.Constructive.TangentNumber

/-!
Export witness for the tangent-number small-window readback correspondence.
-/

namespace BedcMathlibBridge.Export.TangentNumber

open BedcMathlibBridge.Constructive.TangentNumber

structure TangentNumberExportWitness where
  readback : Nat -> Nat
  readback_apply :
    forall n : Nat,
      readback n = BedcMathlibBridge.Constructive.TangentNumber.readback n
  bedc_apply :
    forall n : Nat, readback n = BEDC.Derived.TangentNumberUp.tangentNumberFn n
  one_apply : readback 1 = 1
  two_apply : readback 2 = 2
  three_apply : readback 3 = 16
  four_apply : readback 4 = 272
  nat_pow_small_values :
    BEDC.Derived.TangentNumberUp.tangentNumberFn 1 = Nat.pow 1 1 ∧
      BEDC.Derived.TangentNumberUp.tangentNumberFn 2 = Nat.pow 2 1 ∧
        BEDC.Derived.TangentNumberUp.tangentNumberFn 3 = Nat.pow 2 4 ∧
          BEDC.Derived.TangentNumberUp.tangentNumberFn 4 =
            Nat.pow 2 8 + Nat.pow 2 4
  odd_zigzag_small_values :
    (BEDC.Derived.TangentNumberUp.tangentNumber 1 (readback 1) ∧
        BEDC.Derived.ZigzagUp.ZigzagNumber 1 (readback 1)) ∧
      (BEDC.Derived.TangentNumberUp.tangentNumber 2 (readback 2) ∧
        BEDC.Derived.ZigzagUp.ZigzagNumber 3 (readback 2)) ∧
        (BEDC.Derived.TangentNumberUp.tangentNumber 3 (readback 3) ∧
          BEDC.Derived.ZigzagUp.ZigzagNumber 5 (readback 3)) ∧
          (BEDC.Derived.TangentNumberUp.tangentNumber 4 (readback 4) ∧
            BEDC.Derived.ZigzagUp.ZigzagNumber 7 (readback 4))
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def tangentNumberExport : TangentNumberExportWitness where
  readback := readback
  readback_apply := by
    intro n
    rfl
  bedc_apply := readback_apply
  one_apply := readback_one
  two_apply := readback_two
  three_apply := readback_three
  four_apply := readback_four
  nat_pow_small_values := small_values_nat_pow_anchor
  odd_zigzag_small_values := readback_odd_zigzag_small_values
  mathlib_anchor := mathlibPowAnchor

theorem tangentNumber_small_values_nat_pow_anchor
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibPowAnchor) :
    BEDC.Derived.TangentNumberUp.tangentNumberFn 1 = Nat.pow 1 1 ∧
      BEDC.Derived.TangentNumberUp.tangentNumberFn 2 = Nat.pow 2 1 ∧
        BEDC.Derived.TangentNumberUp.tangentNumberFn 3 = Nat.pow 2 4 ∧
          BEDC.Derived.TangentNumberUp.tangentNumberFn 4 =
            Nat.pow 2 8 + Nat.pow 2 4 :=
  BedcMathlibBridge.Constructive.TangentNumber.small_values_nat_pow_anchor

end BedcMathlibBridge.Export.TangentNumber
