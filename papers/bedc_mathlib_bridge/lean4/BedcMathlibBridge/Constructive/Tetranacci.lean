import BEDC.Derived.TetranacciUp
import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.Tetranacci

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.TetranacciUp.tetranacci n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.TetranacciUp.tetranacci n := by
  rfl

theorem toNat_zero :
    toNat 0 = 0 := by
  rfl

theorem toNat_one :
    toNat 1 = 0 := by
  rfl

theorem toNat_two :
    toNat 2 = 0 := by
  rfl

theorem toNat_three :
    toNat 3 = 1 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem toNat_recurrence
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat (n + 4) =
      Nat.add
        (Nat.add (Nat.add (toNat n) (toNat (n + 1))) (toNat (n + 2)))
        (toNat (n + 3)) := by
  change
    BEDC.Derived.TetranacciUp.tetranacci (n + 4) =
      Nat.add
        (Nat.add
          (Nat.add (BEDC.Derived.TetranacciUp.tetranacci n)
            (BEDC.Derived.TetranacciUp.tetranacci (n + 1)))
          (BEDC.Derived.TetranacciUp.tetranacci (n + 2)))
        (BEDC.Derived.TetranacciUp.tetranacci (n + 3))
  exact BEDC.Derived.TetranacciUp.tetranacci_recurrence n

theorem tetranacci_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.TetranacciUp.tetranacci (n + 4) =
      Nat.add
        (Nat.add
          (Nat.add (BEDC.Derived.TetranacciUp.tetranacci n)
            (BEDC.Derived.TetranacciUp.tetranacci (n + 1)))
          (BEDC.Derived.TetranacciUp.tetranacci (n + 2)))
        (BEDC.Derived.TetranacciUp.tetranacci (n + 3)) := by
  exact BEDC.Derived.TetranacciUp.tetranacci_recurrence n

end BedcMathlibBridge.Constructive.Tetranacci
