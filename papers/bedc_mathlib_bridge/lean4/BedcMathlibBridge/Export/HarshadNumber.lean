import BedcMathlibBridge.Constructive.HarshadNumber

/-!
Export witness for the Harshad-number digit readback.
-/

namespace BedcMathlibBridge.Export.HarshadNumber

open BedcMathlibBridge.Constructive.HarshadNumber

structure HarshadNumberExportWitness where
  digitSumReadback : Nat -> List Nat -> Nat
  digitSum_apply :
    forall base : Nat, forall digits : List Nat,
      digitSumReadback base digits =
        BEDC.Derived.HarshadNumberUp.digitSum base digits
  list_foldr_apply :
    forall base : Nat, forall digits : List Nat,
      digitSumReadback base digits = List.foldr Nat.add 0 digits
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def harshadNumberExport : HarshadNumberExportWitness where
  digitSumReadback := digitSumReadback
  digitSum_apply := digitSumReadback_apply
  list_foldr_apply := digitSumReadback_eq_list_foldr
  mathlib_anchor := mathlibNatAnchor

theorem harshadNumber_mathlib_digit_surface
    {value : Nat}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.HarshadNumberUp.HarshadNumber value ->
      Exists fun digits : List Nat =>
        BEDC.Derived.HarshadNumberUp.DigitsInBase
            BEDC.Derived.HarshadNumberUp.decimalBase digits ∧
          0 < List.foldr Nat.add 0 digits ∧
            Exists fun factor : Nat =>
              value = List.foldr Nat.add 0 digits * factor :=
  BedcMathlibBridge.Constructive.HarshadNumber.harshadNumber_mathlib_digit_surface
    mathlibNatAnchor

end BedcMathlibBridge.Export.HarshadNumber
