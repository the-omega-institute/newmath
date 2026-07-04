import BedcMathlibBridge.Constructive.FibonacciLucasIdentity

/-!
Export witness for the Fibonacci-Lucas doubling identity readback.
-/

namespace BedcMathlibBridge.Export.FibonacciLucasIdentity

open BedcMathlibBridge.Constructive.FibonacciLucasIdentity

structure FibonacciLucasIdentityExportWitness where
  fibReadback : Nat -> Nat
  lucasReadback : Nat -> Nat
  fib_apply :
    forall n : Nat,
      fibReadback n =
        BedcMathlibBridge.Constructive.FibonacciLucasIdentity.fibReadback n
  lucas_apply :
    forall n : Nat,
      lucasReadback n =
        BedcMathlibBridge.Constructive.FibonacciLucasIdentity.lucasReadback n
  bedc_fib_apply :
    forall n : Nat,
      fibReadback n = BEDC.Derived.FibonacciLucasIdentitiesUp.fib n
  bedc_lucas_apply :
    forall n : Nat,
      lucasReadback n = BEDC.Derived.FibonacciLucasIdentitiesUp.lucas n
  nat_fib_apply :
    forall n : Nat, fibReadback n = Nat.fib n
  lucas_nat_fib_shift_apply :
    forall n : Nat, lucasReadback (n + 1) = Nat.fib (n + 2) + Nat.fib n
  doubling_apply :
    forall n : Nat,
      fibReadback (2 * n) = Nat.mul (Nat.fib n) (lucasReadback n)

def fibonacciLucasIdentityExport : FibonacciLucasIdentityExportWitness where
  fibReadback := fibReadback
  lucasReadback := lucasReadback
  fib_apply := by
    intro n
    rfl
  lucas_apply := by
    intro n
    rfl
  bedc_fib_apply := fibReadback_apply
  bedc_lucas_apply := lucasReadback_apply
  nat_fib_apply := fibReadback_eq_nat_fib
  lucas_nat_fib_shift_apply := lucasReadback_succ_eq_nat_fib_add
  doubling_apply := fib_doubling_nat_fib_mul_lucas

theorem fib_doubling_nat_fib_mul_lucas (n : Nat) :
    BEDC.Derived.FibonacciLucasIdentitiesUp.fib (2 * n) =
      Nat.mul (Nat.fib n) (BEDC.Derived.FibonacciLucasIdentitiesUp.lucas n) := by
  change
    BedcMathlibBridge.Constructive.FibonacciLucasIdentity.fibReadback (2 * n) =
      Nat.mul
        (Nat.fib n)
        (BedcMathlibBridge.Constructive.FibonacciLucasIdentity.lucasReadback n)
  exact
    BedcMathlibBridge.Constructive.FibonacciLucasIdentity.fib_doubling_nat_fib_mul_lucas n

end BedcMathlibBridge.Export.FibonacciLucasIdentity
