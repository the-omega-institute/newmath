import BEDC.Derived.SchroederNumberUp
import Mathlib.Data.Nat.Basic

/-!
Schroeder-number recurrence readback correspondence.

The BEDC objects are the closed `Nat` surfaces
`BEDC.Derived.SchroederNumberUp.largeSchroederNumber`,
`BEDC.Derived.SchroederNumberUp.smallSchroederNumber`, and the internal
convolution used by the recurrence. The bridge records their direct readback
through host `Nat.add` and `Nat.mul`.
-/

namespace BedcMathlibBridge.Constructive.SchroederNumber

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  ()

def largeReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.SchroederNumberUp.largeSchroederNumber n

def smallReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.SchroederNumberUp.smallSchroederNumber n

def internalConvolutionReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.SchroederNumberUp.smallSchroederInternalConvolution n

theorem largeReadback_apply (n : Nat) :
    largeReadback n = BEDC.Derived.SchroederNumberUp.largeSchroederNumber n := by
  rfl

theorem smallReadback_apply (n : Nat) :
    smallReadback n = BEDC.Derived.SchroederNumberUp.smallSchroederNumber n := by
  rfl

theorem internalConvolutionReadback_apply (n : Nat) :
    internalConvolutionReadback n =
      BEDC.Derived.SchroederNumberUp.smallSchroederInternalConvolution n := by
  rfl

theorem largeReadback_zero :
    largeReadback 0 = 1 := by
  rfl

theorem smallReadback_zero :
    smallReadback 0 = 1 := by
  rfl

theorem smallReadback_one :
    smallReadback 1 = 1 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem largeReadback_succ_from_small
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    largeReadback (Nat.succ n) =
      Nat.mul 2 (smallReadback (Nat.succ n)) := by
  exact BEDC.Derived.SchroederNumberUp.largeSchroeder_succ_from_small_strong n

theorem smallReadback_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    smallReadback (Nat.succ (Nat.succ n)) =
      Nat.add
        (Nat.mul 3 (smallReadback (Nat.succ n)))
        (Nat.mul 2 (internalConvolutionReadback (Nat.succ n))) := by
  change
    BEDC.Derived.SchroederNumberUp.smallSchroederNumber
        (Nat.succ (Nat.succ n)) =
      3 * BEDC.Derived.SchroederNumberUp.smallSchroederNumber (Nat.succ n) +
        2 *
          BEDC.Derived.SchroederNumberUp.smallSchroederInternalConvolution
            (Nat.succ n)
  exact BEDC.Derived.SchroederNumberUp.smallSchroeder_succ_succ_recursion_strong n

theorem largeReadback_recurrence_nat_add_mul
    (n : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    largeReadback (Nat.succ (Nat.succ n)) =
      Nat.mul 2
        (Nat.add
          (Nat.mul 3 (smallReadback (Nat.succ n)))
          (Nat.mul 2 (internalConvolutionReadback (Nat.succ n)))) := by
  change
    BEDC.Derived.SchroederNumberUp.largeSchroederNumber
        (Nat.succ (Nat.succ n)) =
      2 *
        (3 * BEDC.Derived.SchroederNumberUp.smallSchroederNumber (Nat.succ n) +
          2 *
            BEDC.Derived.SchroederNumberUp.smallSchroederInternalConvolution
              (Nat.succ n))
  exact BEDC.Derived.SchroederNumberUp.largeSchroeder_succ_succ_recursion_from_small n

theorem largeReadback_small_values :
    largeReadback 0 = 1 ∧ largeReadback 1 = 2 ∧
      largeReadback 2 = 6 ∧ largeReadback 3 = 22 ∧
        largeReadback 4 = 90 ∧ largeReadback 5 = 394 := by
  exact BEDC.Derived.SchroederNumberUp.largeSchroeder_small_values

theorem smallReadback_small_values :
    smallReadback 0 = 1 ∧ smallReadback 1 = 1 ∧
      smallReadback 2 = 3 ∧ smallReadback 3 = 11 ∧
        smallReadback 4 = 45 ∧ smallReadback 5 = 197 := by
  exact BEDC.Derived.SchroederNumberUp.smallSchroeder_small_values

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
  BEDC.Derived.SchroederNumberUp.largeSchroeder_succ_succ_recursion_from_small n

end BedcMathlibBridge.Constructive.SchroederNumber
