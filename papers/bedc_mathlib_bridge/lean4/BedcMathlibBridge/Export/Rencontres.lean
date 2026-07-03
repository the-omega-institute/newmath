import BedcMathlibBridge.Constructive.Rencontres

namespace BedcMathlibBridge.Export.Rencontres

open BedcMathlibBridge.Constructive.Rencontres

structure RencontresNumberExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : forall n k : Nat,
    readback n k = BedcMathlibBridge.Constructive.Rencontres.readback n k
  bedc_apply : forall n k : Nat,
    readback n k = BEDC.Derived.RencontresNumberUp.rencontresNumber n k
  mathlib_formula : forall n k : Nat,
    readback n k = Nat.choose n k * numDerangements (n - k)
  fixed_all : forall n : Nat, readback n n = 1
  fixed_none : forall n : Nat, readback n 0 = numDerangements n
  above : forall n : Nat, readback n (Nat.succ n) = 0
  three_one : readback 3 1 = 3
  four_two : readback 4 2 = 6

def rencontresNumberExport : RencontresNumberExportWitness where
  readback := readback
  readback_apply := by
    intro n k
    rfl
  bedc_apply := readback_apply
  mathlib_formula := readback_eq_nat_choose_mul_numDerangements
  fixed_all := readback_fixed_all
  fixed_none := readback_fixed_none
  above := readback_above
  three_one := readback_three_one
  four_two := readback_four_two

theorem rencontresNumber_eq_nat_choose_mul_numDerangements (n k : Nat) :
    BEDC.Derived.RencontresNumberUp.rencontresNumber n k =
      Nat.choose n k * numDerangements (n - k) := by
  exact
    (BedcMathlibBridge.Constructive.Rencontres.readback_apply n k).symm.trans
      (BedcMathlibBridge.Constructive.Rencontres.readback_eq_nat_choose_mul_numDerangements n k)

end BedcMathlibBridge.Export.Rencontres
