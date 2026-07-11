import BedcMathlibBridge.Constructive.BesselNumber

/-!
Export witness for the Bessel-number closed-form correspondence.
-/

namespace BedcMathlibBridge.Export.BesselNumber

open BedcMathlibBridge.Constructive.BesselNumber

structure BesselNumberExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply :
    forall n k : Nat,
      readback n k = BEDC.Derived.BesselNumberUp.besselClosedFormula n k
  mathlib_formula_apply :
    forall n k : Nat,
      readback n k =
        Nat.factorial n /
          (Nat.pow 2 k * Nat.factorial k * Nat.factorial (n - (k + k)))
  closed_formula_apply :
    forall n k : Nat,
      readback n k = mathlibClosedFormula n k

def besselNumberExport : BesselNumberExportWitness where
  readback := readback
  readback_apply := readback_apply
  mathlib_formula_apply := readback_eq_mathlibClosedFormula
  closed_formula_apply := readback_eq_mathlibClosedFormula

theorem besselClosedFormula_eq_nat_factorial_pow_formula (n k : Nat) :
    BEDC.Derived.BesselNumberUp.besselClosedFormula n k =
      Nat.factorial n /
        (Nat.pow 2 k * Nat.factorial k * Nat.factorial (n - (k + k))) :=
  BedcMathlibBridge.Constructive.BesselNumber.besselClosedFormula_eq_nat_factorial_pow_formula
    n k

end BedcMathlibBridge.Export.BesselNumber
