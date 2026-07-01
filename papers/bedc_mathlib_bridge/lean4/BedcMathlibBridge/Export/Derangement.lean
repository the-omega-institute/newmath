import BedcMathlibBridge.Constructive.Derangement

namespace BedcMathlibBridge.Export.Derangement

open BedcMathlibBridge.Constructive.Derangement

structure DerangementExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat, readback n = BEDC.Derived.DerangementUp.derangementNumber n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 0
  recurrence_apply : ∀ n : Nat,
    readback (n + 2) = (n + 1) * (readback (n + 1) + readback n)
  numDerangements_apply : ∀ n : Nat, readback n = numDerangements n

def derangementExport : DerangementExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  one_apply := toNat_one
  recurrence_apply := toNat_add_two
  numDerangements_apply := toNat_eq_numDerangements

theorem derangementNumber_eq_numDerangements (n : Nat) :
    BEDC.Derived.DerangementUp.derangementNumber n = numDerangements n :=
  BedcMathlibBridge.Constructive.Derangement.toNat_eq_numDerangements n

end BedcMathlibBridge.Export.Derangement
