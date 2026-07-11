import BedcMathlibBridge.Constructive.KeithNumber

/-!
Export witness for the Keith-number window-sum readback.
-/

namespace BedcMathlibBridge.Export.KeithNumber

open BedcMathlibBridge.Constructive.KeithNumber

structure KeithNumberExportWitness where
  nextValue : List Nat -> Nat -> Nat
  nextValue_apply :
    forall digits : List Nat, forall fuel : Nat,
      nextValue digits fuel =
        BEDC.Derived.KeithNumberUp.keithNextValue digits fuel
  window_sum_apply :
    forall digits : List Nat, forall fuel : Nat,
      nextValue digits fuel =
        List.foldr Nat.add 0
          (BEDC.Derived.KeithNumberUp.keithWindowFuel digits fuel)
  digit_sum_apply :
    forall digits : List Nat,
      BEDC.Derived.KeithNumberUp.keithDigitSum digits =
        List.foldr Nat.add 0 digits
  fourteen_sequence :
    BEDC.Derived.KeithNumberUp.keithSequenceFuel [1, 4] 3 =
      [1, 4, 5, 9, 14]
  nineteen_sequence :
    BEDC.Derived.KeithNumberUp.keithSequenceFuel [1, 9] 2 =
      [1, 9, 10, 19]
  twentyEight_sequence :
    BEDC.Derived.KeithNumberUp.keithSequenceFuel [2, 8] 3 =
      [2, 8, 10, 18, 28]
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def keithNumberExport : KeithNumberExportWitness where
  nextValue := nextValueReadback
  nextValue_apply := nextValueReadback_apply
  window_sum_apply := nextValueReadback_eq_list_foldr_window
  digit_sum_apply := keithDigitSum_eq_list_foldr
  fourteen_sequence := BEDC.Derived.KeithNumberUp.keithSequence_digits_fourteen
  nineteen_sequence := BEDC.Derived.KeithNumberUp.keithSequence_digits_nineteen
  twentyEight_sequence := BEDC.Derived.KeithNumberUp.keithSequence_digits_twentyEight
  mathlib_anchor := mathlibNatListAnchor

theorem keithNextValue_eq_list_foldr_window
    (digits : List Nat) (fuel : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatListAnchor) :
    BEDC.Derived.KeithNumberUp.keithNextValue digits fuel =
      List.foldr Nat.add 0
        (BEDC.Derived.KeithNumberUp.keithWindowFuel digits fuel) :=
  BedcMathlibBridge.Constructive.KeithNumber.keithNextValue_eq_list_foldr_window
    digits fuel mathlibNatListAnchor

end BedcMathlibBridge.Export.KeithNumber
