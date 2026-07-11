import BedcMathlibBridge.Constructive.SchroederNumber

/-!
Export witness for the Schroeder-number recurrence readback correspondence.
-/

namespace BedcMathlibBridge.Export.SchroederNumber

open BedcMathlibBridge.Constructive.SchroederNumber

structure SchroederNumberExportWitness where
  largeReadback : Nat -> Nat
  smallReadback : Nat -> Nat
  internalConvolutionReadback : Nat -> Nat
  large_apply :
    forall n : Nat,
      largeReadback n =
        BedcMathlibBridge.Constructive.SchroederNumber.largeReadback n
  small_apply :
    forall n : Nat,
      smallReadback n =
        BedcMathlibBridge.Constructive.SchroederNumber.smallReadback n
  internal_apply :
    forall n : Nat,
      internalConvolutionReadback n =
        BedcMathlibBridge.Constructive.SchroederNumber.internalConvolutionReadback n
  bedc_large_apply :
    forall n : Nat,
      largeReadback n = BEDC.Derived.SchroederNumberUp.largeSchroederNumber n
  bedc_small_apply :
    forall n : Nat,
      smallReadback n = BEDC.Derived.SchroederNumberUp.smallSchroederNumber n
  bedc_internal_apply :
    forall n : Nat,
      internalConvolutionReadback n =
        BEDC.Derived.SchroederNumberUp.smallSchroederInternalConvolution n
  large_zero : largeReadback 0 = 1
  small_zero : smallReadback 0 = 1
  small_one : smallReadback 1 = 1
  large_succ_from_small : forall n : Nat,
    largeReadback (Nat.succ n) = Nat.mul 2 (smallReadback (Nat.succ n))
  small_recurrence : forall n : Nat,
    smallReadback (Nat.succ (Nat.succ n)) =
      Nat.add
        (Nat.mul 3 (smallReadback (Nat.succ n)))
        (Nat.mul 2 (internalConvolutionReadback (Nat.succ n)))
  large_recurrence : forall n : Nat,
    largeReadback (Nat.succ (Nat.succ n)) =
      Nat.mul 2
        (Nat.add
          (Nat.mul 3 (smallReadback (Nat.succ n)))
          (Nat.mul 2 (internalConvolutionReadback (Nat.succ n))))
  large_small_values :
    largeReadback 0 = 1 ∧ largeReadback 1 = 2 ∧
      largeReadback 2 = 6 ∧ largeReadback 3 = 22 ∧
        largeReadback 4 = 90 ∧ largeReadback 5 = 394
  small_small_values :
    smallReadback 0 = 1 ∧ smallReadback 1 = 1 ∧
      smallReadback 2 = 3 ∧ smallReadback 3 = 11 ∧
        smallReadback 4 = 45 ∧ smallReadback 5 = 197
  mathlib_anchor : Nat.succ_injective = Nat.succ_injective

def schroederNumberExport : SchroederNumberExportWitness where
  largeReadback := largeReadback
  smallReadback := smallReadback
  internalConvolutionReadback := internalConvolutionReadback
  large_apply := by
    intro n
    rfl
  small_apply := by
    intro n
    rfl
  internal_apply := by
    intro n
    rfl
  bedc_large_apply := largeReadback_apply
  bedc_small_apply := smallReadback_apply
  bedc_internal_apply := internalConvolutionReadback_apply
  large_zero := largeReadback_zero
  small_zero := smallReadback_zero
  small_one := smallReadback_one
  large_succ_from_small := largeReadback_succ_from_small
  small_recurrence := smallReadback_recurrence_nat_add_mul
  large_recurrence := largeReadback_recurrence_nat_add_mul
  large_small_values := largeReadback_small_values
  small_small_values := smallReadback_small_values
  mathlib_anchor := mathlibNatAnchor

theorem largeSchroederNumber_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    BEDC.Derived.SchroederNumberUp.largeSchroederNumber
        (Nat.succ (Nat.succ n)) =
      Nat.mul 2
        (Nat.add
          (Nat.mul 3
            (BEDC.Derived.SchroederNumberUp.smallSchroederNumber (Nat.succ n)))
          (Nat.mul 2
            (BEDC.Derived.SchroederNumberUp.smallSchroederInternalConvolution
              (Nat.succ n)))) :=
  BedcMathlibBridge.Constructive.SchroederNumber.largeSchroederNumber_recurrence_nat_add_mul n

end BedcMathlibBridge.Export.SchroederNumber
