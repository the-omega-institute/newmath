import BedcMathlibBridge.Constructive.OddDoubleFactorial

/-!
Export witness for the odd double factorial structural correspondence.

The witness records that the readback is the BEDC odd double factorial
`BEDC.Derived.EulerianSecondOrderUp.oddDoubleFactorialCount`, satisfies its
boundary and the `(2n+1)` scaling recurrence, and that the shifted readback is
pointwise equal to mathlib's odd double factorial `Nat.doubleFactorial (2n+1)`.
-/

namespace BedcMathlibBridge.Export.OddDoubleFactorial

open BedcMathlibBridge.Constructive.OddDoubleFactorial

structure OddDoubleFactorialExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat,
    readback n = BEDC.Derived.EulerianSecondOrderUp.oddDoubleFactorialCount n
  zero_apply : readback 0 = 1
  succ_apply : ∀ n : Nat,
    readback (Nat.succ n) = Nat.succ (n + n) * readback n
  double_factorial_apply : ∀ n : Nat,
    readback (Nat.succ n) = Nat.doubleFactorial (2 * n + 1)

def oddDoubleFactorialExport : OddDoubleFactorialExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := by
    intro n
    rfl
  zero_apply := toNat_zero
  succ_apply := toNat_succ
  double_factorial_apply := toNat_succ_eq_doubleFactorial

theorem oddDoubleFactorialCount_succ_eq_doubleFactorial (n : Nat) :
    BEDC.Derived.EulerianSecondOrderUp.oddDoubleFactorialCount (Nat.succ n) =
      Nat.doubleFactorial (2 * n + 1) :=
  BedcMathlibBridge.Constructive.OddDoubleFactorial.toNat_succ_eq_doubleFactorial n

end BedcMathlibBridge.Export.OddDoubleFactorial
