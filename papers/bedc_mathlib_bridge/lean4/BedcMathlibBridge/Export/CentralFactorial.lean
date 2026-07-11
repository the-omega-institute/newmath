import BedcMathlibBridge.Constructive.CentralFactorial

/-!
Export witness for the second-kind central factorial strip correspondence.
-/

namespace BedcMathlibBridge.Export.CentralFactorial

open BedcMathlibBridge.Constructive.CentralFactorial

structure CentralFactorialExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : forall n k : Nat, readback n k = toNat n k
  bedc_apply : forall n k : Nat,
    readback n k =
      BEDC.Derived.CentralFactorialUp.centralFactorialSecond n k
  diagonal_apply : forall n : Nat,
    readback n n = Nat.stirlingSecond n n
  above_diagonal_apply : forall n extra : Nat,
    readback n (Nat.succ (n + extra)) =
      Nat.stirlingSecond n (Nat.succ (n + extra))
  zero_row_apply : forall k : Nat,
    readback 0 k = Nat.stirlingSecond 0 k
  one_row_apply : forall k : Nat,
    readback 1 k = Nat.stirlingSecond 1 k

def centralFactorialExport : CentralFactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n k
    rfl
  bedc_apply := toNat_apply
  diagonal_apply := diagonal_eq_nat_stirlingSecond
  above_diagonal_apply := above_diagonal_eq_nat_stirlingSecond
  zero_row_apply := zero_row_eq_nat_stirlingSecond
  one_row_apply := one_row_eq_nat_stirlingSecond

theorem centralFactorialSecond_diagonal_eq_nat_stirlingSecond (n : Nat) :
    BEDC.Derived.CentralFactorialUp.centralFactorialSecond n n =
      Nat.stirlingSecond n n :=
  BedcMathlibBridge.Constructive.CentralFactorial.diagonal_eq_nat_stirlingSecond n

theorem centralFactorialSecond_above_diagonal_eq_nat_stirlingSecond
    (n extra : Nat) :
    BEDC.Derived.CentralFactorialUp.centralFactorialSecond n
        (Nat.succ (n + extra)) =
      Nat.stirlingSecond n (Nat.succ (n + extra)) :=
  BedcMathlibBridge.Constructive.CentralFactorial.above_diagonal_eq_nat_stirlingSecond
    n extra

end BedcMathlibBridge.Export.CentralFactorial
