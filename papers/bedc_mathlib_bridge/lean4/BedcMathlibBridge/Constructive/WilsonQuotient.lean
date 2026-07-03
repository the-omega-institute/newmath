import BEDC.Derived.WilsonQuotientUp
import Mathlib.Data.Nat.Factorial.Basic

/-!
Wilson-quotient Nat readback through the factorial surface.

The slice is only the computable quotient expression `((p - 1)! + 1) / p`.
The exported correspondence below does not use Wilson congruence or `ZMod`
theorem surfaces.
-/

namespace BedcMathlibBridge.Constructive.WilsonQuotient

private def mathlibFactorialProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  ()

def toNat (p : Nat) : Nat :=
  let _ := mathlibFactorialProvenanceAnchor
  BEDC.Derived.WilsonQuotientUp.wilsonQuotientNat p

theorem toNat_apply (p : Nat) :
    toNat p = BEDC.Derived.WilsonQuotientUp.wilsonQuotientNat p := by
  rfl

theorem toNat_eq_bedc_factorial_formula (p : Nat) :
    toNat p =
      (BEDC.Derived.StirlingFirstUp.factorialNat (p - 1) + 1) / p := by
  rfl

private theorem stirlingFirstFactorialNat_eq_nat_factorial (n : Nat) :
    BEDC.Derived.StirlingFirstUp.factorialNat n = Nat.factorial n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        BEDC.Derived.StirlingFirstUp.factorialNat (Nat.succ n) =
            Nat.succ n * BEDC.Derived.StirlingFirstUp.factorialNat n := by
          rfl
        _ = Nat.succ n * Nat.factorial n := by
          rw [ih]
        _ = Nat.factorial (Nat.succ n) := by
          rfl

theorem toNat_eq_nat_factorial_formula (p : Nat) :
    toNat p = (Nat.factorial (p - 1) + 1) / p := by
  calc
    toNat p =
        (BEDC.Derived.StirlingFirstUp.factorialNat (p - 1) + 1) / p :=
      toNat_eq_bedc_factorial_formula p
    _ = (Nat.factorial (p - 1) + 1) / p := by
      rw [stirlingFirstFactorialNat_eq_nat_factorial (p - 1)]

end BedcMathlibBridge.Constructive.WilsonQuotient
