import BedcMathlibBridge.Constructive.CakeNumber

/-!
Export witness for the cake number structural correspondence.
-/

namespace BedcMathlibBridge.Export.CakeNumber

open BedcMathlibBridge.Constructive.CakeNumber

structure CakeNumberExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat, readback n = BEDC.Derived.CakeNumberUp.cakeNumber n
  zero_apply : readback 0 = 1
  one_apply : readback 1 = 2
  succ_apply : ∀ n : Nat, readback (Nat.succ n) = readback n + Nat.succ n
  nat_choose_apply : ∀ n : Nat, readback n = Nat.choose (n + 1) 2 + 1

def cakeNumberExport : CakeNumberExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  one_apply := toNat_one
  succ_apply := toNat_succ
  nat_choose_apply := toNat_eq_nat_choose_add_one

theorem cakeNumber_eq_nat_choose_add_one (n : Nat) :
    BEDC.Derived.CakeNumberUp.cakeNumber n = Nat.choose (n + 1) 2 + 1 :=
  BedcMathlibBridge.Constructive.CakeNumber.toNat_eq_nat_choose_add_one n

end BedcMathlibBridge.Export.CakeNumber
