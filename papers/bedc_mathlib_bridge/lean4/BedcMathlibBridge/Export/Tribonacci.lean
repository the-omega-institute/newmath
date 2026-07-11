import BedcMathlibBridge.Constructive.Tribonacci

/-!
Export witness for the Tribonacci recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.Tribonacci

open BedcMathlibBridge.Constructive.Tribonacci

structure TribonacciExportWitness where
  readback : Nat -> Nat
  readback_apply : forall n : Nat, readback n = toNat n
  bedc_apply : forall n : Nat, readback n = BEDC.Derived.TribonacciUp.tribonacci n
  zero_apply : readback 0 = 0
  one_apply : readback 1 = 1
  two_apply : readback 2 = 1
  recurrence_apply : forall n : Nat,
    readback (n + 3) =
      Nat.add (Nat.add (readback n) (readback (n + 1))) (readback (n + 2))
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def tribonacciExport : TribonacciExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  zero_apply := toNat_zero
  one_apply := toNat_one
  two_apply := toNat_two
  recurrence_apply := toNat_recurrence
  mathlib_anchor := mathlibNatAnchor

theorem tribonacci_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.TribonacciUp.tribonacci (n + 3) =
      Nat.add
        (Nat.add (BEDC.Derived.TribonacciUp.tribonacci n)
          (BEDC.Derived.TribonacciUp.tribonacci (n + 1)))
        (BEDC.Derived.TribonacciUp.tribonacci (n + 2)) :=
  BedcMathlibBridge.Constructive.Tribonacci.tribonacci_recurrence_nat_add n

end BedcMathlibBridge.Export.Tribonacci
