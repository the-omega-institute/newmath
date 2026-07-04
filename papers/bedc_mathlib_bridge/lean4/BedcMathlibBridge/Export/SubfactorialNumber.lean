import BedcMathlibBridge.Constructive.SubfactorialNumber

/-!
Export witness for the subfactorial-number readback correspondence.
-/

namespace BedcMathlibBridge.Export.SubfactorialNumber

open BedcMathlibBridge.Constructive.SubfactorialNumber

structure SubfactorialNumberExportWitness where
  readback : Nat -> Nat
  readback_apply :
    forall n : Nat,
      readback n =
        BedcMathlibBridge.Constructive.SubfactorialNumber.toNat n
  bedc_apply :
    forall n : Nat,
      readback n = BEDC.Derived.DerangementUp.subfactorialNumber n
  derangement_alias_apply :
    forall n : Nat,
      readback n = BEDC.Derived.DerangementUp.derangementNumber n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 0
  recurrence_apply :
    forall n : Nat,
      readback (n + 2) = (n + 1) * (readback (n + 1) + readback n)
  numDerangements_apply :
    forall n : Nat, readback n = numDerangements n

def subfactorialNumberExport : SubfactorialNumberExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  derangement_alias_apply := toNat_eq_derangementNumber
  zero_apply := toNat_zero
  one_apply := toNat_one
  recurrence_apply := toNat_two_step_recurrence
  numDerangements_apply := toNat_eq_numDerangements

theorem subfactorialNumber_eq_numDerangements (n : Nat) :
    BEDC.Derived.DerangementUp.subfactorialNumber n = numDerangements n :=
  BedcMathlibBridge.Constructive.SubfactorialNumber.subfactorialNumber_eq_numDerangements n

end BedcMathlibBridge.Export.SubfactorialNumber
