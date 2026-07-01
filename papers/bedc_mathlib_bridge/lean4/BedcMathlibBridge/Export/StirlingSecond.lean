import BedcMathlibBridge.Constructive.StirlingSecond

namespace BedcMathlibBridge.Export.StirlingSecond

open BedcMathlibBridge.Constructive.StirlingSecond

structure StirlingSecondExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ n k : Nat, readback n k = toNat n k
  zero_zero : readback 0 0 = 1
  zero_succ : ∀ k : Nat, readback 0 (Nat.succ k) = 0
  succ_zero : ∀ n : Nat, readback (Nat.succ n) 0 = 0
  recurrence_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      Nat.succ k * readback n (Nat.succ k) + readback n k
  nat_stirlingSecond_apply : ∀ n k : Nat, readback n k = Nat.stirlingSecond n k

def stirlingSecondExport : StirlingSecondExportWitness where
  readback := toNat
  readback_apply := by
    intro n k
    rfl
  zero_zero := toNat_zero_zero
  zero_succ := toNat_zero_succ
  succ_zero := toNat_succ_zero
  recurrence_apply := toNat_succ_succ
  nat_stirlingSecond_apply := toNat_eq_nat_stirlingSecond

theorem stirlingSecond_eq_nat_stirlingSecond (n k : Nat) :
    BEDC.Derived.StirlingUp.stirlingSecond n k = Nat.stirlingSecond n k :=
  BedcMathlibBridge.Constructive.StirlingSecond.toNat_eq_nat_stirlingSecond n k

end BedcMathlibBridge.Export.StirlingSecond
