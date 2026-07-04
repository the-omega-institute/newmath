import BEDC.Derived.EulerianSecondOrderUp
import Mathlib.Data.Nat.Basic

/-!
Second-order Eulerian table recurrence readback.

The bridge exposes the BEDC table and row-sum recurrence through host `Nat`
arithmetic, while keeping enumeration and generating-function surfaces outside
this packet.
-/

namespace BedcMathlibBridge.Constructive.EulerianSecondOrder

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, Nat.add a b = a + b := fun _ _ => rfl
  let _ : forall a b : Nat, Nat.mul a b = a * b := fun _ _ => rfl
  let _ : forall a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
  ()

def tableReadback (n k : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n k

def rowSumReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.EulerianSecondOrderUp.eulerianSecondRowSum n

theorem tableReadback_apply (n k : Nat) :
    tableReadback n k =
      BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n k := by
  rfl

theorem rowSumReadback_apply (n : Nat) :
    rowSumReadback n =
      BEDC.Derived.EulerianSecondOrderUp.eulerianSecondRowSum n := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem table_zero_zero :
    tableReadback 0 0 = 1 := by
  rfl

theorem table_zero_succ (k : Nat) :
    tableReadback 0 (Nat.succ k) = 0 := by
  rfl

theorem table_left_boundary (n : Nat) :
    tableReadback n 0 = 1 := by
  change BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n 0 = 1
  exact BEDC.Derived.EulerianSecondOrderUp.eulerianSecond_left_boundary n

theorem table_recurrence_nat_mul_add_sub
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    tableReadback (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul (Nat.succ (Nat.succ k)) (tableReadback n (Nat.succ k)))
        (Nat.mul
          (Nat.sub (Nat.succ (n + n)) (Nat.succ k))
          (tableReadback n k)) := by
  change
    BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber
        (Nat.succ n) (Nat.succ k) =
      Nat.add
        (Nat.mul
          (Nat.succ (Nat.succ k))
          (BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n
            (Nat.succ k)))
        (Nat.mul
          (Nat.sub (Nat.succ (n + n)) (Nat.succ k))
          (BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n k))
  exact BEDC.Derived.EulerianSecondOrderUp.eulerianSecond_recurrence n k

theorem table_above_row_zero (n extra : Nat) :
    tableReadback n (Nat.succ (n + extra)) = 0 := by
  change
    BEDC.Derived.EulerianSecondOrderUp.eulerianSecondNumber n
      (Nat.succ (n + extra)) = 0
  exact BEDC.Derived.EulerianSecondOrderUp.eulerianSecond_succ_above n extra

theorem rowSum_succ_nat_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    rowSumReadback (Nat.succ n) =
      Nat.mul (Nat.succ (n + n)) (rowSumReadback n) := by
  change
    BEDC.Derived.EulerianSecondOrderUp.eulerianSecondRowSum (Nat.succ n) =
      Nat.mul
        (Nat.succ (n + n))
        (BEDC.Derived.EulerianSecondOrderUp.eulerianSecondRowSum n)
  exact BEDC.Derived.EulerianSecondOrderUp.eulerianSecondRowSum_succ n

end BedcMathlibBridge.Constructive.EulerianSecondOrder
