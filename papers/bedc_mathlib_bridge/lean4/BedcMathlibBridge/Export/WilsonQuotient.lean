import BedcMathlibBridge.Constructive.WilsonQuotient

/-!
Export witness for the Wilson-quotient factorial readback.
-/

namespace BedcMathlibBridge.Export.WilsonQuotient

open BedcMathlibBridge.Constructive.WilsonQuotient

structure WilsonQuotientExportWitness where
  readback : Nat -> Nat
  readback_apply : forall p : Nat, readback p = toNat p
  bedc_apply : forall p : Nat,
    readback p = BEDC.Derived.WilsonQuotientUp.wilsonQuotientNat p
  bedc_factorial_apply : forall p : Nat,
    readback p =
      (BEDC.Derived.StirlingFirstUp.factorialNat (p - 1) + 1) / p
  nat_factorial_apply : forall p : Nat,
    readback p = (Nat.factorial (p - 1) + 1) / p

def wilsonQuotientExport : WilsonQuotientExportWitness where
  readback := toNat
  readback_apply := by
    intro p
    rfl
  bedc_apply := toNat_apply
  bedc_factorial_apply := toNat_eq_bedc_factorial_formula
  nat_factorial_apply := toNat_eq_nat_factorial_formula

theorem wilsonQuotientNat_eq_nat_factorial_formula (p : Nat) :
    BEDC.Derived.WilsonQuotientUp.wilsonQuotientNat p =
      (Nat.factorial (p - 1) + 1) / p := by
  change toNat p = (Nat.factorial (p - 1) + 1) / p
  exact BedcMathlibBridge.Constructive.WilsonQuotient.toNat_eq_nat_factorial_formula p

end BedcMathlibBridge.Export.WilsonQuotient
