import BedcMathlibBridge.Constructive.Motzkin

/-!
Export witness for the Motzkin relation recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.Motzkin

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BedcMathlibBridge.Constructive.Motzkin

structure MotzkinExportWitness where
  relation : BHist -> BHist -> Prop
  convolution : BHist -> BHist -> BHist -> Prop
  relation_apply : forall n value : BHist,
    relation n value ↔ relationReadback n value
  convolution_apply : forall left count sum : BHist,
    convolution left count sum ↔ convolutionReadback left count sum
  zero_apply : relation BHist.Empty BEDC.Derived.MotzkinUp.NatOne
  one_apply : relation BEDC.Derived.MotzkinUp.NatOne BEDC.Derived.MotzkinUp.NatOne
  two_apply : relation BEDC.Derived.MotzkinUp.NatTwo BEDC.Derived.MotzkinUp.NatTwo
  three_apply : relation BEDC.Derived.MotzkinUp.NatThree BEDC.Derived.MotzkinUp.NatFour
  four_apply : relation BEDC.Derived.MotzkinUp.NatFour BEDC.Derived.MotzkinUp.NatNine
  five_apply : relation BEDC.Derived.MotzkinUp.NatFive BEDC.Derived.MotzkinUp.NatTwentyOne
  constructor_step_apply :
    forall {n current conv next : BHist},
      relation n current ->
        convolution BHist.Empty n conv ->
        NatAdd current conv next ->
          relation (BHist.e1 n) next ∧
            bwordLength (BHist.e1 n) = Nat.succ (bwordLength n) ∧
            bwordLength next =
              Nat.add (bwordLength current) (bwordLength conv)
  convolution_step_apply :
    forall {left right a b head tail sum : BHist},
      relation left a ->
        relation right b ->
        NatMul a b head ->
        convolution (BHist.e1 left) right tail ->
        NatAdd head tail sum ->
          convolution left (BHist.e1 right) sum ∧
            bwordLength (BHist.e1 right) = Nat.succ (bwordLength right) ∧
            bwordLength head = Nat.mul (bwordLength a) (bwordLength b) ∧
            bwordLength sum = Nat.add (bwordLength head) (bwordLength tail)
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def motzkinExport : MotzkinExportWitness where
  relation := relationReadback
  convolution := convolutionReadback
  relation_apply := by
    intro n value
    rfl
  convolution_apply := by
    intro left count sum
    rfl
  zero_apply := zero_value
  one_apply := one_value
  two_apply := two_value
  three_apply := three_value
  four_apply := four_value
  five_apply := five_value
  constructor_step_apply := by
    intro n current conv next currentRow convRow addRow
    exact constructor_step mathlibNatAnchor currentRow convRow addRow
  convolution_step_apply := by
    intro left right a b head tail sum leftRow rightRow mulRow tailRow addRow
    exact convolution_step_readback mathlibNatAnchor leftRow rightRow mulRow tailRow addRow
  mathlib_anchor := mathlibNatAnchor

theorem motzkin_constructor_step_nat_add
    {n current conv next : BHist}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.MotzkinUp.Motzkin n current ->
      BEDC.Derived.MotzkinUp.MotzkinConv BHist.Empty n conv ->
      NatAdd current conv next ->
        BEDC.Derived.MotzkinUp.Motzkin (BHist.e1 n) next ∧
          bwordLength (BHist.e1 n) = Nat.succ (bwordLength n) ∧
          bwordLength next =
            Nat.add (bwordLength current) (bwordLength conv) :=
  BedcMathlibBridge.Constructive.Motzkin.constructor_step

theorem motzkin_convolution_step_nat_mul_add
    {left right a b head tail sum : BHist}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.MotzkinUp.Motzkin left a ->
      BEDC.Derived.MotzkinUp.Motzkin right b ->
      NatMul a b head ->
      BEDC.Derived.MotzkinUp.MotzkinConv (BHist.e1 left) right tail ->
      NatAdd head tail sum ->
        BEDC.Derived.MotzkinUp.MotzkinConv left (BHist.e1 right) sum ∧
          bwordLength (BHist.e1 right) = Nat.succ (bwordLength right) ∧
          bwordLength head = Nat.mul (bwordLength a) (bwordLength b) ∧
          bwordLength sum = Nat.add (bwordLength head) (bwordLength tail) :=
  BedcMathlibBridge.Constructive.Motzkin.convolution_step_readback

end BedcMathlibBridge.Export.Motzkin
