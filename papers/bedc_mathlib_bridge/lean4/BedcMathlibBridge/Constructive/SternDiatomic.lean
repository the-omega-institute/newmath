import BEDC.Derived.SternDiatomicUp
import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.SternDiatomic

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  ()

def fuelReadback (fuel n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.SternDiatomicUp.fuscFuel fuel n

def readback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.SternDiatomicUp.fusc n

theorem fuelReadback_apply (fuel n : Nat) :
    fuelReadback fuel n = BEDC.Derived.SternDiatomicUp.fuscFuel fuel n := by
  rfl

theorem readback_apply (n : Nat) :
    readback n = BEDC.Derived.SternDiatomicUp.fusc n := by
  rfl

theorem readback_zero :
    readback 0 = 0 := by
  rfl

theorem readback_one :
    readback 1 = 1 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem fuelReadback_even_positive
    (fuel n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    fuelReadback (fuel + 1)
        (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1)) =
      fuelReadback fuel (n + 1) := by
  change
    BEDC.Derived.SternDiatomicUp.fuscFuel (fuel + 1)
        (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1)) =
      BEDC.Derived.SternDiatomicUp.fuscFuel fuel (n + 1)
  exact BEDC.Derived.SternDiatomicUp.fuscFuel_even_positive fuel n

theorem fuelReadback_odd_positive_nat_add
    (fuel n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    fuelReadback (fuel + 1)
        (Nat.succ (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1))) =
      Nat.add (fuelReadback fuel (n + 1)) (fuelReadback fuel (n + 2)) := by
  change
    BEDC.Derived.SternDiatomicUp.fuscFuel (fuel + 1)
        (Nat.succ (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1))) =
      Nat.add
        (BEDC.Derived.SternDiatomicUp.fuscFuel fuel (n + 1))
        (BEDC.Derived.SternDiatomicUp.fuscFuel fuel (n + 2))
  exact BEDC.Derived.SternDiatomicUp.fuscFuel_odd_positive fuel n

theorem fuscFuel_odd_positive_nat_add
    (fuel n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.SternDiatomicUp.fuscFuel (fuel + 1)
        (Nat.succ (BEDC.Derived.SternDiatomicUp.sternDouble (n + 1))) =
      Nat.add
        (BEDC.Derived.SternDiatomicUp.fuscFuel fuel (n + 1))
        (BEDC.Derived.SternDiatomicUp.fuscFuel fuel (n + 2)) :=
  BEDC.Derived.SternDiatomicUp.fuscFuel_odd_positive fuel n

end BedcMathlibBridge.Constructive.SternDiatomic
