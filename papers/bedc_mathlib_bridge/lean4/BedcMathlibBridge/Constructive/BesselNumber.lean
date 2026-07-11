import BEDC.Derived.BesselNumberUp
import Mathlib.Data.Nat.Factorial.Basic

/-!
Bessel-number closed-form readback.

The BEDC side already carries the Bessel-number table and the closed division
formula. This bridge exposes only that formula against `Nat.factorial` and
`Nat.pow`.
-/

namespace BedcMathlibBridge.Constructive.BesselNumber

private def mathlibFactorialPowProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.factorial n = Nat.factorial n := fun _ => rfl
  let _ : forall a b : Nat, Nat.pow a b = Nat.pow a b := fun _ _ => rfl
  ()

def readback (n k : Nat) : Nat :=
  let _ := mathlibFactorialPowProvenanceAnchor
  BEDC.Derived.BesselNumberUp.besselClosedFormula n k

def mathlibClosedFormula (n k : Nat) : Nat :=
  Nat.factorial n /
    (Nat.pow 2 k * Nat.factorial k * Nat.factorial (n - (k + k)))

theorem readback_apply (n k : Nat) :
    readback n k = BEDC.Derived.BesselNumberUp.besselClosedFormula n k := by
  rfl

theorem stirlingFirstFactorialNat_eq_nat_factorial (n : Nat) :
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

private theorem besselClosedFormula_eq_stirling_factorial_formula (n k : Nat) :
    BEDC.Derived.BesselNumberUp.besselClosedFormula n k =
      BEDC.Derived.StirlingFirstUp.factorialNat n /
        (Nat.pow 2 k * BEDC.Derived.StirlingFirstUp.factorialNat k *
          BEDC.Derived.StirlingFirstUp.factorialNat (n - (k + k))) := by
  exact BEDC.Derived.BesselNumberUp.besselClosedFormula_definition n k

theorem besselClosedFormula_eq_nat_factorial_pow_formula (n k : Nat) :
    BEDC.Derived.BesselNumberUp.besselClosedFormula n k =
      Nat.factorial n /
        (Nat.pow 2 k * Nat.factorial k * Nat.factorial (n - (k + k))) := by
  calc
    BEDC.Derived.BesselNumberUp.besselClosedFormula n k =
        BEDC.Derived.StirlingFirstUp.factorialNat n /
          (Nat.pow 2 k * BEDC.Derived.StirlingFirstUp.factorialNat k *
            BEDC.Derived.StirlingFirstUp.factorialNat (n - (k + k))) :=
      besselClosedFormula_eq_stirling_factorial_formula n k
    _ =
        Nat.factorial n /
          (Nat.pow 2 k * Nat.factorial k * Nat.factorial (n - (k + k))) := by
      rw [stirlingFirstFactorialNat_eq_nat_factorial n,
        stirlingFirstFactorialNat_eq_nat_factorial k,
        stirlingFirstFactorialNat_eq_nat_factorial (n - (k + k))]

theorem readback_eq_mathlibClosedFormula (n k : Nat) :
    readback n k = mathlibClosedFormula n k := by
  rw [readback_apply]
  exact besselClosedFormula_eq_nat_factorial_pow_formula n k

end BedcMathlibBridge.Constructive.BesselNumber
