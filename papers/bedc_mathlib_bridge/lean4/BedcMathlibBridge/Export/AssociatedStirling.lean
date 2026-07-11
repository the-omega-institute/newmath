import BedcMathlibBridge.Constructive.AssociatedStirling

/-!
Export witness for the associated Stirling power-term slice.
-/

namespace BedcMathlibBridge.Export.AssociatedStirling

open BedcMathlibBridge.Constructive.AssociatedStirling

structure AssociatedStirlingExportWitness where
  factorialReadback : Nat -> Nat
  chooseReadback : Nat -> Nat -> Nat
  powerTermReadback : Nat -> Nat -> Nat -> Nat
  factorial_apply : forall k : Nat,
    factorialReadback k =
      BEDC.Derived.StirlingSecondCompleteUp.factorialCount k
  choose_apply : forall k j : Nat,
    chooseReadback k j = BEDC.Derived.StirlingSecondCompleteUp.C k j
  power_term_apply : forall n k j : Nat,
    powerTermReadback n k j =
      BEDC.Derived.StirlingSecondCompleteUp.explicitPowerTerm n k j
  nat_factorial_apply : forall k : Nat,
    factorialReadback k = Nat.factorial k
  nat_choose_apply : forall k j : Nat,
    chooseReadback k j = Nat.choose k j
  mathlib_power_term_apply : forall n k j : Nat,
    powerTermReadback n k j = mathlibPowerTerm n k j

def associatedStirlingExport : AssociatedStirlingExportWitness where
  factorialReadback := factorialReadback
  chooseReadback := chooseReadback
  powerTermReadback := powerTermReadback
  factorial_apply := factorialReadback_apply
  choose_apply := chooseReadback_apply
  power_term_apply := powerTermReadback_apply
  nat_factorial_apply := factorialReadback_eq_nat_factorial
  nat_choose_apply := chooseReadback_eq_nat_choose
  mathlib_power_term_apply := powerTermReadback_eq_mathlib

theorem associatedStirling_power_term_eq_nat_choose_pow (n k j : Nat) :
    BEDC.Derived.StirlingSecondCompleteUp.explicitPowerTerm n k j =
      Nat.choose k j * (k - j) ^ n :=
  BedcMathlibBridge.Constructive.AssociatedStirling.powerTermReadback_eq_mathlib n k j

end BedcMathlibBridge.Export.AssociatedStirling
