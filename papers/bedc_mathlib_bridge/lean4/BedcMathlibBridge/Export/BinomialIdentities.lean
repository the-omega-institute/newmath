import BedcMathlibBridge.Constructive.BinomialIdentities

/-!
Export witness for the `BinomialIdentitiesUp.C` correspondence.

The witness records the carrier-local BEDC binomial count, its pointwise
readback to mathlib `Nat.choose`, and the shared Pascal recurrence.
-/

namespace BedcMathlibBridge.Export.BinomialIdentities

open BedcMathlibBridge.Constructive.BinomialIdentities

structure BinomialIdentitiesExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ n k : Nat, readback n k = toNat n k
  bedc_apply : ∀ n k : Nat,
    readback n k = BEDC.Derived.BinomialIdentitiesUp.C n k
  nat_choose_apply : ∀ n k : Nat, readback n k = Nat.choose n k
  pascal_bedc_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      readback n k + readback n (Nat.succ k)
  pascal_mathlib_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) =
      Nat.choose n k + Nat.choose n (Nat.succ k)

def binomialIdentitiesExport : BinomialIdentitiesExportWitness where
  readback := toNat
  readback_apply := by
    intro n k
    rfl
  bedc_apply := toNat_apply
  nat_choose_apply := toNat_eq_nat_choose
  pascal_bedc_apply := toNat_pascal_bedc
  pascal_mathlib_apply := toNat_pascal_mathlib

theorem binomialIdentities_C_eq_nat_choose (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C n k = Nat.choose n k :=
  BedcMathlibBridge.Constructive.BinomialIdentities.toNat_eq_nat_choose n k

theorem binomialIdentities_pascal_matches_nat_choose (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C (Nat.succ n) (Nat.succ k) =
      Nat.choose n k + Nat.choose n (Nat.succ k) :=
  BedcMathlibBridge.Constructive.BinomialIdentities.toNat_pascal_mathlib n k

end BedcMathlibBridge.Export.BinomialIdentities
