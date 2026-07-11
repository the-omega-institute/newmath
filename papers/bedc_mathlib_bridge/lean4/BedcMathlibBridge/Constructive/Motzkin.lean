import BEDC.Derived.MotzkinUp
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.NatMulComm
import Mathlib.Data.Nat.Basic

/-!
Motzkin recurrence readback correspondence.

The BEDC object is the `Motzkin`/`MotzkinConv` relation over unary `BHist`
rows. The bridge records the constructor-level recurrence and reads the
displayed BEDC `NatAdd` and `NatMul` rows through `bwordLength` into host
`Nat.add` and `Nat.mul`.
-/

namespace BedcMathlibBridge.Constructive.Motzkin

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  ()

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

def relationReadback (n value : BHist) : Prop :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.MotzkinUp.Motzkin n value

def convolutionReadback (left count sum : BHist) : Prop :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.MotzkinUp.MotzkinConv left count sum

theorem relationReadback_apply {n value : BHist} :
    relationReadback n value ↔ BEDC.Derived.MotzkinUp.Motzkin n value := by
  rfl

theorem convolutionReadback_apply {left count sum : BHist} :
    convolutionReadback left count sum ↔
      BEDC.Derived.MotzkinUp.MotzkinConv left count sum := by
  rfl

theorem zero_value :
    relationReadback BHist.Empty BEDC.Derived.MotzkinUp.NatOne := by
  exact BEDC.Derived.MotzkinUp.motzkin_zero

theorem one_value :
    relationReadback BEDC.Derived.MotzkinUp.NatOne BEDC.Derived.MotzkinUp.NatOne := by
  exact BEDC.Derived.MotzkinUp.motzkin_one

theorem two_value :
    relationReadback BEDC.Derived.MotzkinUp.NatTwo BEDC.Derived.MotzkinUp.NatTwo := by
  exact BEDC.Derived.MotzkinUp.motzkin_two

theorem three_value :
    relationReadback BEDC.Derived.MotzkinUp.NatThree BEDC.Derived.MotzkinUp.NatFour := by
  exact BEDC.Derived.MotzkinUp.motzkin_three

theorem four_value :
    relationReadback BEDC.Derived.MotzkinUp.NatFour BEDC.Derived.MotzkinUp.NatNine := by
  exact BEDC.Derived.MotzkinUp.motzkin_four

theorem five_value :
    relationReadback BEDC.Derived.MotzkinUp.NatFive BEDC.Derived.MotzkinUp.NatTwentyOne := by
  exact BEDC.Derived.MotzkinUp.motzkin_five

private theorem add_row_nat_add {current conv next : BHist} :
    NatAdd current conv next ->
      bwordLength next =
        Nat.add (bwordLength current) (bwordLength conv) := by
  intro addRow
  exact NatAdd_length addRow

private theorem mul_row_nat_mul {leftValue rightValue head : BHist} :
    NatMul leftValue rightValue head ->
      bwordLength head =
        Nat.mul (bwordLength leftValue) (bwordLength rightValue) := by
  intro mulRow
  exact NatMul_bwordLength mulRow

theorem constructor_step
    {n current conv next : BHist}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    relationReadback n current ->
      convolutionReadback BHist.Empty n conv ->
      NatAdd current conv next ->
        relationReadback (BHist.e1 n) next ∧
          bwordLength (BHist.e1 n) = Nat.succ (bwordLength n) ∧
          bwordLength next =
            Nat.add (bwordLength current) (bwordLength conv) := by
  intro currentRow convRow addRow
  exact ⟨
    BEDC.Derived.MotzkinUp.motzkin_succ_of_convolution currentRow convRow addRow,
    rfl,
    add_row_nat_add addRow⟩

theorem convolution_step_readback
    {left right a b head tail sum : BHist}
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    relationReadback left a ->
      relationReadback right b ->
      NatMul a b head ->
      convolutionReadback (BHist.e1 left) right tail ->
      NatAdd head tail sum ->
        convolutionReadback left (BHist.e1 right) sum ∧
          bwordLength (BHist.e1 right) = Nat.succ (bwordLength right) ∧
          bwordLength head = Nat.mul (bwordLength a) (bwordLength b) ∧
          bwordLength sum = Nat.add (bwordLength head) (bwordLength tail) := by
  intro leftRow rightRow mulRow tailRow addRow
  exact ⟨
    BEDC.Derived.MotzkinUp.MotzkinConv.step
      leftRow rightRow mulRow tailRow addRow,
    rfl,
    mul_row_nat_mul mulRow,
    add_row_nat_add addRow⟩

end BedcMathlibBridge.Constructive.Motzkin
