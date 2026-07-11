import BedcMathlibBridge.Constructive.NarayanaCow

namespace BedcMathlibBridge.Export.NarayanaCow

open BedcMathlibBridge.Constructive.NarayanaCow

structure NarayanaCowExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = BedcMathlibBridge.Constructive.NarayanaCow.readback n
  bedc_apply : forall n : Nat, readback n = BEDC.Derived.NarayanaCowUp.narayanaCow n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 1
  two_apply : readback 2 = 1
  three_apply : readback 3 = 2
  four_apply : readback 4 = 3
  five_apply : readback 5 = 4
  recurrence_apply : forall n : Nat,
    readback (n + 3) = Nat.add (readback (n + 2)) (readback n)
  monotone_step_apply : forall n : Nat,
    Nat.le (readback (n + 2)) (readback (n + 3))
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def narayanaCowExport : NarayanaCowExportWitness where
  readback := readback
  readback_apply := by
    intro n
    rfl
  bedc_apply := readback_apply
  zero_apply := readback_zero
  one_apply := readback_one
  two_apply := readback_two
  three_apply := readback_three
  four_apply := readback_four
  five_apply := readback_five
  recurrence_apply := recurrence_nat_add
  monotone_step_apply := step_nat_le
  mathlib_anchor := mathlibNatAnchor

theorem narayanaCow_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.NarayanaCowUp.narayanaCow (n + 3) =
      Nat.add
        (BEDC.Derived.NarayanaCowUp.narayanaCow (n + 2))
        (BEDC.Derived.NarayanaCowUp.narayanaCow n) := by
  change readback (n + 3) = Nat.add (readback (n + 2)) (readback n)
  exact recurrence_nat_add n

end BedcMathlibBridge.Export.NarayanaCow
