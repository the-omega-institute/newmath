import BedcMathlibBridge.Constructive.LahNumber

namespace BedcMathlibBridge.Export.LahNumber

open BedcMathlibBridge.Constructive.LahNumber

structure LahNumberFirstColumnChooseExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = firstColumnChooseReadback n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) 1
  nat_choose_factorial_apply : ∀ n : Nat,
    readback n = Nat.choose n 0 * Nat.factorial (Nat.succ n)

def lahNumberFirstColumnChooseExport : LahNumberFirstColumnChooseExportWitness where
  readback := firstColumnChooseReadback
  readback_apply := by
    intro n
    rfl
  bedc_apply := firstColumnChooseReadback_apply
  nat_choose_factorial_apply := firstColumnChooseReadback_eq_nat_choose_factorial

theorem lahNumber_succ_one_eq_nat_choose_factorial (n : Nat) :
    BEDC.Derived.LahNumberUp.lahNumber (Nat.succ n) 1 =
      Nat.choose n 0 * Nat.factorial (Nat.succ n) := by
  change firstColumnChooseReadback n =
    Nat.choose n 0 * Nat.factorial (Nat.succ n)
  exact firstColumnChooseReadback_eq_nat_choose_factorial n

end BedcMathlibBridge.Export.LahNumber
