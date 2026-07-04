import BedcMathlibBridge.Constructive.SuperCatalan

/-!
Export witness for the super-Catalan choose-formula correspondence.
-/

namespace BedcMathlibBridge.Export.SuperCatalan

open BedcMathlibBridge.Constructive.SuperCatalan

structure SuperCatalanExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : forall m n : Nat, readback m n = superCatalan m n
  bedc_choose_formula_apply :
    forall m n : Nat,
      readback m n =
        (BEDC.Derived.BinomialIdentitiesUp.C (m + m) m *
            BEDC.Derived.BinomialIdentitiesUp.C (n + n) n) /
          BEDC.Derived.BinomialIdentitiesUp.C (m + n) m
  mathlib_choose_formula_apply :
    forall m n : Nat,
      readback m n =
        (Nat.choose (m + m) m * Nat.choose (n + n) n) /
          Nat.choose (m + n) m
  zero_zero_apply : readback 0 0 = 1

def superCatalanExport : SuperCatalanExportWitness where
  readback := superCatalan
  readback_apply := by
    intro m n
    rfl
  bedc_choose_formula_apply := superCatalan_eq_bedc_choose_formula
  mathlib_choose_formula_apply := superCatalan_eq_nat_choose_formula
  zero_zero_apply := superCatalan_zero_zero

theorem superCatalan_eq_nat_choose_formula (m n : Nat) :
    (BEDC.Derived.BinomialIdentitiesUp.C (m + m) m *
        BEDC.Derived.BinomialIdentitiesUp.C (n + n) n) /
      BEDC.Derived.BinomialIdentitiesUp.C (m + n) m =
    (Nat.choose (m + m) m * Nat.choose (n + n) n) /
      Nat.choose (m + n) m :=
  BedcMathlibBridge.Constructive.SuperCatalan.bedc_choose_formula_eq_nat_choose_formula m n

end BedcMathlibBridge.Export.SuperCatalan
