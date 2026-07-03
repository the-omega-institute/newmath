import BEDC.Derived.CentralTrinomialUp
import Mathlib.Data.Nat.Basic

/-!
Central trinomial recurrence readback correspondence.

The BEDC object is the closed `Nat` recurrence
`BEDC.Derived.CentralTrinomialUp.centralTrinomialNumber`. The bridge records
the direct readback and the diagonal recurrence through host `Nat.add`.
-/

namespace BedcMathlibBridge.Constructive.CentralTrinomial

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.CentralTrinomialUp.centralTrinomialNumber n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.CentralTrinomialUp.centralTrinomialNumber n := by
  rfl

theorem toNat_zero :
    toNat 0 = 1 := by
  rfl

theorem toNat_one :
    toNat 1 = 1 := by
  rfl

theorem toNat_two :
    toNat 2 = 3 := by
  rfl

theorem toNat_three :
    toNat 3 = 7 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem toNat_succ_succ_diagonal
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    toNat (Nat.succ (Nat.succ n)) =
      Nat.add
        (Nat.add
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ (Nat.succ n)))
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ n)))
        (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n) n) := by
  change
    BEDC.Derived.CentralTrinomialUp.centralTrinomialNumber
        (Nat.succ (Nat.succ n)) =
      BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
          (Nat.succ (Nat.succ n)) +
        BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
          (Nat.succ n) +
          BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n) n
  exact BEDC.Derived.CentralTrinomialUp.centralTrinomial_succ_succ_diagonal n

theorem centralTrinomial_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.CentralTrinomialUp.centralTrinomialNumber
        (Nat.succ (Nat.succ n)) =
      Nat.add
        (Nat.add
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ (Nat.succ n)))
          (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n)
            (Nat.succ n)))
        (BEDC.Derived.CentralTrinomialUp.trinomialCoeff (Nat.succ n) n) := by
  exact toNat_succ_succ_diagonal n

end BedcMathlibBridge.Constructive.CentralTrinomial
