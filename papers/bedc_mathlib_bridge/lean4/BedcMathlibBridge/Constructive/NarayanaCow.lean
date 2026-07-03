import BEDC.Derived.NarayanaCowUp
import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.NarayanaCow

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, (a <= b) = Nat.le a b := fun _ _ => rfl
  ()

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

def readback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.NarayanaCowUp.narayanaCow n

theorem readback_apply (n : Nat) :
    readback n = BEDC.Derived.NarayanaCowUp.narayanaCow n := by
  rfl

theorem readback_zero :
    readback 0 = 1 := by
  rfl

theorem readback_one :
    readback 1 = 1 := by
  rfl

theorem readback_two :
    readback 2 = 1 := by
  rfl

theorem readback_three :
    readback 3 = 2 := by
  rfl

theorem readback_four :
    readback 4 = 3 := by
  rfl

theorem readback_five :
    readback 5 = 4 := by
  rfl

theorem recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    readback (n + 3) = Nat.add (readback (n + 2)) (readback n) := by
  change
    BEDC.Derived.NarayanaCowUp.narayanaCow (n + 3) =
      Nat.add
        (BEDC.Derived.NarayanaCowUp.narayanaCow (n + 2))
        (BEDC.Derived.NarayanaCowUp.narayanaCow n)
  exact BEDC.Derived.NarayanaCowUp.narayanaCow_recurrence n

theorem step_nat_le
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    Nat.le (readback (n + 2)) (readback (n + 3)) := by
  change
    Nat.le
      (BEDC.Derived.NarayanaCowUp.narayanaCow (n + 2))
      (BEDC.Derived.NarayanaCowUp.narayanaCow (n + 3))
  exact BEDC.Derived.NarayanaCowUp.narayanaCow_step_le n

end BedcMathlibBridge.Constructive.NarayanaCow
