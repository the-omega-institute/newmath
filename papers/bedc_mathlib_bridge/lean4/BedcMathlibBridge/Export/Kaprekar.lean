import BedcMathlibBridge.Constructive.Kaprekar

/-!
Export witness for the Kaprekar decimal split Nat arithmetic readback.
-/

namespace BedcMathlibBridge.Export.Kaprekar

open BedcMathlibBridge.Constructive.Kaprekar

structure KaprekarExportWitness where
  decimal_readback : Nat -> Prop
  decimal_apply :
    forall n : Nat,
      decimal_readback n = BEDC.Derived.KaprekarUp.KaprekarNumber 10 n
  kaprekar45_bedc : decimal_readback 45
  square_split_nat_pow_mod_div :
    Nat.mod (Nat.pow 45 2) (Nat.pow 10 2) +
        Nat.div (Nat.pow 45 2) (Nat.pow 10 2) =
      45
  combined :
    BEDC.Derived.KaprekarUp.KaprekarNumber 10 45 ∧
      Nat.mod (Nat.pow 45 2) (Nat.pow 10 2) +
          Nat.div (Nat.pow 45 2) (Nat.pow 10 2) =
        45
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def kaprekarExport : KaprekarExportWitness where
  decimal_readback := decimalKaprekarReadback
  decimal_apply := decimalKaprekarReadback_apply
  kaprekar45_bedc := decimalKaprekarReadback_45
  square_split_nat_pow_mod_div :=
    (kaprekar45_decimal_square_split_nat_pow_mod_div).right
  combined := kaprekar45_decimal_square_split_nat_pow_mod_div
  mathlib_anchor := mathlibNatArithmeticAnchor

theorem kaprekar45_decimal_square_split_nat_pow_mod_div
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatArithmeticAnchor) :
    BEDC.Derived.KaprekarUp.KaprekarNumber 10 45 ∧
      Nat.mod (Nat.pow 45 2) (Nat.pow 10 2) +
          Nat.div (Nat.pow 45 2) (Nat.pow 10 2) =
        45 :=
  BedcMathlibBridge.Constructive.Kaprekar.kaprekar45_decimal_square_split_nat_pow_mod_div

end BedcMathlibBridge.Export.Kaprekar
