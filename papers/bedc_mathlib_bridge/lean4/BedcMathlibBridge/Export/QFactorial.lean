import BedcMathlibBridge.Constructive.QFactorial

/-!
Export witness for the q-factorial structural correspondence.

The witness records the `q = 1` readback of the BEDC q-factorial polynomial,
its zero and successor-multiplication laws, and the pointwise equality with
mathlib `Nat.factorial`.
-/

namespace BedcMathlibBridge.Export.QFactorial

open BedcMathlibBridge.Constructive.QFactorial

structure QFactorialExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n =
      BEDC.Derived.QFactorialUp.polyEvalOne
        (BEDC.Derived.QFactorialUp.qFactorial n)
  zero_apply : readback 0 = 1
  recurrence_apply : ∀ n : Nat, readback (Nat.succ n) = Nat.succ n * readback n
  nat_factorial_apply : ∀ n : Nat, readback n = Nat.factorial n

def qFactorialExport : QFactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  recurrence_apply := toNat_succ_mul
  nat_factorial_apply := toNat_eq_nat_factorial

theorem qFactorial_evalOne_eq_nat_factorial (n : Nat) :
    BEDC.Derived.QFactorialUp.polyEvalOne
        (BEDC.Derived.QFactorialUp.qFactorial n) =
      Nat.factorial n :=
  BedcMathlibBridge.Constructive.QFactorial.toNat_eq_nat_factorial n

end BedcMathlibBridge.Export.QFactorial
