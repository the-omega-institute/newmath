import BedcMathlibBridge.Constructive.QBinomial

/-!
Export witness for the q-binomial (Gaussian binomial) structural correspondence.

The witness records that the readback is the `q = 1` evaluation of the BEDC
Gaussian binomial polynomial `BEDC.Derived.QBinomialUp.qBinomial`, that this
evaluation is `polyEvalOne` (a structural `List Nat -> Nat` fold), and that it
satisfies both binomial boundaries, the additive Pascal recurrence, and the
pointwise equality with mathlib `Nat.choose`.
-/

namespace BedcMathlibBridge.Export.QBinomial

open BedcMathlibBridge.Constructive.QBinomial

structure QBinomialExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : ∀ n k : Nat, readback n k = toNat n k
  bedc_apply : ∀ n k : Nat,
    readback n k =
      BEDC.Derived.QBinomialUp.polyEvalOne
        (BEDC.Derived.QBinomialUp.qBinomial n k)
  zero_succ_apply : ∀ k : Nat, readback 0 (Nat.succ k) = 0
  zero_right_apply : ∀ n : Nat, readback n 0 = 1
  pascal_apply : ∀ n k : Nat,
    readback (Nat.succ n) (Nat.succ k) = readback n k + readback n (Nat.succ k)
  nat_choose_apply : ∀ n k : Nat, readback n k = Nat.choose n k

def qBinomialExport : QBinomialExportWitness where
  readback := toNat
  readback_apply := by
    intro n k
    rfl
  bedc_apply := by
    intro n k
    rfl
  zero_succ_apply := toNat_zero_succ
  zero_right_apply := toNat_zero_right
  pascal_apply := toNat_pascal
  nat_choose_apply := toNat_eq_nat_choose

theorem qBinomial_evalOne_eq_nat_choose (n k : Nat) :
    BEDC.Derived.QBinomialUp.polyEvalOne
        (BEDC.Derived.QBinomialUp.qBinomial n k) =
      Nat.choose n k :=
  BedcMathlibBridge.Constructive.QBinomial.toNat_eq_nat_choose n k

end BedcMathlibBridge.Export.QBinomial
