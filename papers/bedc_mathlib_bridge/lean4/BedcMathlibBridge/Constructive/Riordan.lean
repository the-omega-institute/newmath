import BEDC.Derived.RiordanUp
import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.Riordan

open BEDC.FKernel.Hist

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  ()

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

def natRelationReadback (n value : Nat) : Prop :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.RiordanUp.RiordanNat n value

def relationReadback (n value : BHist) : Prop :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.RiordanUp.Riordan n value

def recurrenceReadback (n previous current next : Nat) : Prop :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.RiordanUp.riordanRecurrenceEq n previous current next

theorem natRelationReadback_apply {n value : Nat} :
    natRelationReadback n value ↔
      BEDC.Derived.RiordanUp.RiordanNat n value := by
  rfl

theorem relationReadback_apply {n value : BHist} :
    relationReadback n value ↔ BEDC.Derived.RiordanUp.Riordan n value := by
  rfl

theorem recurrenceReadback_apply {n previous current next : Nat} :
    recurrenceReadback n previous current next ↔
      BEDC.Derived.RiordanUp.riordanRecurrenceEq n previous current next := by
  rfl

theorem zero_value :
    natRelationReadback 0 1 := by
  exact BEDC.Derived.RiordanUp.riordanNat_zero

theorem one_value :
    natRelationReadback 1 0 := by
  exact BEDC.Derived.RiordanUp.riordanNat_one

theorem two_value :
    natRelationReadback 2 1 := by
  exact BEDC.Derived.RiordanUp.riordanNat_two

theorem three_value :
    natRelationReadback 3 1 := by
  exact BEDC.Derived.RiordanUp.riordanNat_three

theorem four_value :
    natRelationReadback 4 3 := by
  exact BEDC.Derived.RiordanUp.riordanNat_four

theorem five_value :
    natRelationReadback 5 6 := by
  exact BEDC.Derived.RiordanUp.riordanNat_five

theorem six_value :
    natRelationReadback 6 15 := by
  exact BEDC.Derived.RiordanUp.riordanNat_six

theorem seven_value :
    natRelationReadback 7 36 := by
  exact BEDC.Derived.RiordanUp.riordanNat_seven

theorem eight_value :
    natRelationReadback 8 91 := by
  exact BEDC.Derived.RiordanUp.riordanNat_eight

theorem step_nat_mul_add
    {n previous current next : Nat}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    natRelationReadback n previous ->
      natRelationReadback (Nat.add n 1) current ->
      Nat.mul (Nat.add n 3) next =
        Nat.mul (Nat.add n 1)
          (Nat.add (Nat.mul 2 current) (Nat.mul 3 previous)) ->
        natRelationReadback (Nat.add n 2) next := by
  intro previousRow currentRow recurrence
  exact
    BEDC.Derived.RiordanUp.riordanRecurrence
      previousRow currentRow recurrence

end BedcMathlibBridge.Constructive.Riordan
