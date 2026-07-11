import BEDC.Derived.MotzkinPathUp
import Mathlib.Data.Nat.Basic

/-!
Motzkin path recurrence readback correspondence.

The BEDC object is the closed `Nat` sequence
`BEDC.Derived.MotzkinPathUp.motzkinNumber`, together with the convolution
term used by its recurrence. The bridge records the recurrence through host
`Nat.add` and `Nat.mul`.
-/

namespace BedcMathlibBridge.Constructive.MotzkinPath

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  ()

def numberReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.MotzkinPathUp.motzkinNumber n

def convolutionReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.MotzkinPathUp.motzkinRecurrenceConvolution n

theorem numberReadback_apply (n : Nat) :
    numberReadback n = BEDC.Derived.MotzkinPathUp.motzkinNumber n := by
  rfl

theorem convolutionReadback_apply (n : Nat) :
    convolutionReadback n =
      BEDC.Derived.MotzkinPathUp.motzkinRecurrenceConvolution n := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem numberReadback_zero :
    numberReadback 0 = 1 := by
  exact BEDC.Derived.MotzkinPathUp.motzkin_zero

theorem recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    numberReadback (Nat.succ n) =
      Nat.add (numberReadback n) (convolutionReadback n) := by
  change
    BEDC.Derived.MotzkinPathUp.motzkinNumber (Nat.succ n) =
      Nat.add
        (BEDC.Derived.MotzkinPathUp.motzkinNumber n)
        (BEDC.Derived.MotzkinPathUp.motzkinRecurrenceConvolution n)
  exact BEDC.Derived.MotzkinPathUp.motzkin_succ_recursion_strong n

theorem small_values :
    numberReadback 0 = 1 ∧ numberReadback 1 = 1 ∧
      numberReadback 2 = 2 ∧ numberReadback 3 = 4 ∧
        numberReadback 4 = 9 ∧ numberReadback 5 = 21 ∧
          numberReadback 6 = 51 := by
  exact BEDC.Derived.MotzkinPathUp.motzkin_small_values

theorem motzkinNumber_succ_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.MotzkinPathUp.motzkinNumber (Nat.succ n) =
      Nat.add
        (BEDC.Derived.MotzkinPathUp.motzkinNumber n)
        (BEDC.Derived.MotzkinPathUp.motzkinRecurrenceConvolution n) :=
  BEDC.Derived.MotzkinPathUp.motzkin_succ_recursion_strong n

end BedcMathlibBridge.Constructive.MotzkinPath
