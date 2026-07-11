import BedcMathlibBridge.Constructive.MotzkinPath

/-!
Export witness for the Motzkin path recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.MotzkinPath

open BedcMathlibBridge.Constructive.MotzkinPath

structure MotzkinPathExportWitness where
  number : Nat -> Nat
  convolution : Nat -> Nat
  number_apply :
    forall n : Nat, number n = numberReadback n
  convolution_apply :
    forall n : Nat, convolution n = convolutionReadback n
  bedc_number_apply :
    forall n : Nat,
      number n = BEDC.Derived.MotzkinPathUp.motzkinNumber n
  bedc_convolution_apply :
    forall n : Nat,
      convolution n =
        BEDC.Derived.MotzkinPathUp.motzkinRecurrenceConvolution n
  zero_apply : number 0 = 1
  recurrence_apply :
    forall n : Nat,
      number (Nat.succ n) = Nat.add (number n) (convolution n)
  small_values :
    number 0 = 1 ∧ number 1 = 1 ∧ number 2 = 2 ∧
      number 3 = 4 ∧ number 4 = 9 ∧ number 5 = 21 ∧
        number 6 = 51
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def motzkinPathExport : MotzkinPathExportWitness where
  number := numberReadback
  convolution := convolutionReadback
  number_apply := by
    intro n
    rfl
  convolution_apply := by
    intro n
    rfl
  bedc_number_apply := numberReadback_apply
  bedc_convolution_apply := convolutionReadback_apply
  zero_apply := numberReadback_zero
  recurrence_apply := recurrence_nat_add
  small_values := small_values
  mathlib_anchor := mathlibNatAnchor

theorem motzkinNumber_succ_recurrence_nat_add
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.MotzkinPathUp.motzkinNumber (Nat.succ n) =
      Nat.add
        (BEDC.Derived.MotzkinPathUp.motzkinNumber n)
        (BEDC.Derived.MotzkinPathUp.motzkinRecurrenceConvolution n) :=
  BedcMathlibBridge.Constructive.MotzkinPath.motzkinNumber_succ_recurrence_nat_add n

end BedcMathlibBridge.Export.MotzkinPath
