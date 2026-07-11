import BedcMathlibBridge.Constructive.GenocchiNumber

/-!
Export witness for the Genocchi-number small-window integer readback.
-/

namespace BedcMathlibBridge.Export.GenocchiNumber

open BedcMathlibBridge.Constructive.GenocchiNumber

structure GenocchiNumberExportWitness where
  readback : Nat -> Int
  readback_apply :
    forall n : Nat,
      readback n = BedcMathlibBridge.Constructive.GenocchiNumber.readback n
  bedc_apply :
    forall n : Nat,
      readback n =
        BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue n
  one_apply : readback 1 = _root_.Int.ofNat 1
  two_apply : readback 2 = _root_.Int.negSucc 0
  four_apply : readback 4 = _root_.Int.ofNat 1
  six_apply : readback 6 = _root_.Int.negSucc 2
  eight_apply : readback 8 = _root_.Int.ofNat 17
  int_small_values :
    BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 1 =
        _root_.Int.ofNat 1 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 2 =
        _root_.Int.negSucc 0 ∧
        BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 4 =
          _root_.Int.ofNat 1 ∧
          BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 6 =
            _root_.Int.negSucc 2 ∧
            BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 8 =
              _root_.Int.ofNat 17
  raw_small_values :
    BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 0 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 1 =
        { num := 1, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 2 =
        { num := -1, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 3 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 4 =
        { num := 1, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 5 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 6 =
        { num := -3, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 7 =
        { num := 0, denMinusOne := 0 } ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumber 8 =
        { num := 17, denMinusOne := 0 }
  integral_small_values :
    BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 0 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 1 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 2 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 3 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 4 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 5 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 6 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 7 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntegralAt 8
  mathlib_anchor : _root_.Int.negSucc = _root_.Int.negSucc

def genocchiNumberExport : GenocchiNumberExportWitness where
  readback := readback
  readback_apply := by
    intro n
    rfl
  bedc_apply := readback_apply
  one_apply := readback_one
  two_apply := readback_two
  four_apply := readback_four
  six_apply := readback_six
  eight_apply := readback_eight
  int_small_values := small_values_int_anchor
  raw_small_values := raw_small_values
  integral_small_values := integral_small_values
  mathlib_anchor := mathlibIntAnchor

theorem genocchiNumber_small_values_int_anchor
    (_anchor : _root_.Int.negSucc = _root_.Int.negSucc := mathlibIntAnchor) :
    BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 1 =
        _root_.Int.ofNat 1 ∧
      BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 2 =
        _root_.Int.negSucc 0 ∧
        BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 4 =
          _root_.Int.ofNat 1 ∧
          BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 6 =
            _root_.Int.negSucc 2 ∧
            BEDC.Derived.GenocchiNumberUp.rawGenocchiNumberIntValue 8 =
              _root_.Int.ofNat 17 :=
  BedcMathlibBridge.Constructive.GenocchiNumber.small_values_int_anchor

end BedcMathlibBridge.Export.GenocchiNumber
