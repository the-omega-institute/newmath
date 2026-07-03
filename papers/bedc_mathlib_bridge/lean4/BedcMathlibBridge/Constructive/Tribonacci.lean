import BEDC.Derived.TribonacciUp
import Mathlib.Data.Nat.Basic

/-!
Tribonacci recurrence readback correspondence.

The BEDC object is the closed `Nat` recurrence
`BEDC.Derived.TribonacciUp.tribonacci`. The bridge records the direct readback
and the third-order recurrence using the host `Nat.add` operation.
-/

namespace BedcMathlibBridge.Constructive.Tribonacci

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.TribonacciUp.tribonacci n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.TribonacciUp.tribonacci n := by
  rfl

theorem toNat_zero :
    toNat 0 = 0 := by
  rfl

theorem toNat_one :
    toNat 1 = 1 := by
  rfl

theorem toNat_two :
    toNat 2 = 1 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem toNat_recurrence
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat (n + 3) =
      Nat.add (Nat.add (toNat n) (toNat (n + 1))) (toNat (n + 2)) := by
  change
    BEDC.Derived.TribonacciUp.tribonacci (n + 3) =
      Nat.add
        (Nat.add (BEDC.Derived.TribonacciUp.tribonacci n)
          (BEDC.Derived.TribonacciUp.tribonacci (n + 1)))
        (BEDC.Derived.TribonacciUp.tribonacci (n + 2))
  exact BEDC.Derived.TribonacciUp.tribonacci_recurrence n

theorem tribonacci_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.TribonacciUp.tribonacci (n + 3) =
      Nat.add
        (Nat.add (BEDC.Derived.TribonacciUp.tribonacci n)
          (BEDC.Derived.TribonacciUp.tribonacci (n + 1)))
        (BEDC.Derived.TribonacciUp.tribonacci (n + 2)) := by
  exact BEDC.Derived.TribonacciUp.tribonacci_recurrence n

end BedcMathlibBridge.Constructive.Tribonacci
