import BedcMathlibBridge.Constructive.StirlingFirst

namespace BedcMathlibBridge.Export.StirlingFirst

open BedcMathlibBridge.Constructive.StirlingFirst

structure StirlingFirstExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ n k : Nat, readback n k = toNat n k
  zero_zero : readback 0 0 = 1
  zero_succ : ∀ k : Nat, readback 0 (Nat.succ k) = 0
  succ_zero : ∀ n : Nat, readback (Nat.succ n) 0 = 0
  recurrence_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      n * readback n (Nat.succ k) + readback n k
  nat_stirlingFirst_apply : ∀ n k : Nat, readback n k = Nat.stirlingFirst n k

def stirlingFirstExport : StirlingFirstExportWitness where
  readback := toNat
  readback_apply := by
    intro n k
    rfl
  zero_zero := toNat_zero_zero
  zero_succ := toNat_zero_succ
  succ_zero := toNat_succ_zero
  recurrence_apply := toNat_succ_succ
  nat_stirlingFirst_apply := toNat_eq_nat_stirlingFirst

theorem stirlingFirst_eq_nat_stirlingFirst (n k : Nat) :
    BEDC.Derived.StirlingFirstUp.stirlingFirst n k = Nat.stirlingFirst n k :=
  BedcMathlibBridge.Constructive.StirlingFirst.toNat_eq_nat_stirlingFirst n k

end BedcMathlibBridge.Export.StirlingFirst
