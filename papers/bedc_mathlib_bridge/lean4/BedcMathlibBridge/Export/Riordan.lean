import BedcMathlibBridge.Constructive.Riordan

namespace BedcMathlibBridge.Export.Riordan

open BEDC.FKernel.Hist
open BedcMathlibBridge.Constructive.Riordan

structure RiordanExportWitness where
  natRelation : Nat -> Nat -> Prop
  relation : BHist -> BHist -> Prop
  recurrence : Nat -> Nat -> Nat -> Nat -> Prop
  nat_relation_apply : forall n value : Nat,
    natRelation n value ↔ natRelationReadback n value
  relation_apply : forall n value : BHist,
    relation n value ↔ relationReadback n value
  recurrence_apply : forall n previous current next : Nat,
    recurrence n previous current next ↔
      recurrenceReadback n previous current next
  zero_apply : natRelation 0 1
  one_apply : natRelation 1 0
  two_apply : natRelation 2 1
  three_apply : natRelation 3 1
  four_apply : natRelation 4 3
  five_apply : natRelation 5 6
  six_apply : natRelation 6 15
  seven_apply : natRelation 7 36
  eight_apply : natRelation 8 91
  step_apply : forall {n previous current next : Nat},
    natRelation n previous ->
      natRelation (Nat.add n 1) current ->
      Nat.mul (Nat.add n 3) next =
        Nat.mul (Nat.add n 1)
          (Nat.add (Nat.mul 2 current) (Nat.mul 3 previous)) ->
        natRelation (Nat.add n 2) next
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def riordanExport : RiordanExportWitness where
  natRelation := natRelationReadback
  relation := relationReadback
  recurrence := recurrenceReadback
  nat_relation_apply := by
    intro n value
    rfl
  relation_apply := by
    intro n value
    rfl
  recurrence_apply := by
    intro n previous current next
    rfl
  zero_apply := zero_value
  one_apply := one_value
  two_apply := two_value
  three_apply := three_value
  four_apply := four_value
  five_apply := five_value
  six_apply := six_value
  seven_apply := seven_value
  eight_apply := eight_value
  step_apply := by
    intro n previous current next previousRow currentRow recurrence
    exact step_nat_mul_add mathlibNatAnchor previousRow currentRow recurrence
  mathlib_anchor := mathlibNatAnchor

theorem riordan_step_nat_mul_add
    {n previous current next : Nat}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.RiordanUp.RiordanNat n previous ->
      BEDC.Derived.RiordanUp.RiordanNat (Nat.add n 1) current ->
      Nat.mul (Nat.add n 3) next =
        Nat.mul (Nat.add n 1)
          (Nat.add (Nat.mul 2 current) (Nat.mul 3 previous)) ->
        BEDC.Derived.RiordanUp.RiordanNat (Nat.add n 2) next :=
  BedcMathlibBridge.Constructive.Riordan.step_nat_mul_add

end BedcMathlibBridge.Export.Riordan
