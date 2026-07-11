import BedcMathlibBridge.Constructive.Fibonacci
import BedcMathlibBridge.Constructive.Lucas
import BEDC.Derived.FibonacciLucasIdentitiesUp

/-!
Fibonacci-Lucas doubling identity readback.

The BEDC side proves the doubling identity for its Window6 Fibonacci and
Lucas counts. The bridge records the same identity against the host `Nat.fib`
and `Nat.mul` surface.
-/

namespace BedcMathlibBridge.Constructive.FibonacciLucasIdentity

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : forall a b : Nat, a * b = Nat.mul a b := fun _ _ => rfl
  let _ : forall n : Nat, Nat.fib n = Nat.fib n := fun _ => rfl
  ()

def fibReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.FibonacciLucasIdentitiesUp.fib n

def lucasReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.FibonacciLucasIdentitiesUp.lucas n

theorem fibReadback_apply (n : Nat) :
    fibReadback n = BEDC.Derived.FibonacciLucasIdentitiesUp.fib n := by
  rfl

theorem lucasReadback_apply (n : Nat) :
    lucasReadback n = BEDC.Derived.FibonacciLucasIdentitiesUp.lucas n := by
  rfl

theorem fibReadback_eq_nat_fib (n : Nat) :
    fibReadback n = Nat.fib n := by
  change BEDC.Derived.FibonacciUp.fib n = Nat.fib n
  exact BedcMathlibBridge.Constructive.Fibonacci.toNat_eq_nat_fib n

theorem lucasReadback_succ_eq_nat_fib_add (n : Nat) :
    lucasReadback (n + 1) = Nat.fib (n + 2) + Nat.fib n := by
  change BEDC.Derived.FibonacciUp.lucas (n + 1) =
    Nat.fib (n + 2) + Nat.fib n
  exact BedcMathlibBridge.Constructive.Lucas.toNat_succ_eq_nat_fib_add n

theorem fib_doubling_nat_fib_mul_lucas (n : Nat) :
    fibReadback (2 * n) =
      Nat.mul (Nat.fib n) (lucasReadback n) := by
  calc
    fibReadback (2 * n) =
        BEDC.Derived.FibonacciLucasIdentitiesUp.fib (2 * n) := by
      rfl
    _ =
        Nat.mul
          (BEDC.Derived.FibonacciLucasIdentitiesUp.fib n)
          (BEDC.Derived.FibonacciLucasIdentitiesUp.lucas n) :=
      BEDC.Derived.FibonacciLucasIdentitiesUp.fib_two_mul_eq_fib_mul_lucas n
    _ = Nat.mul (Nat.fib n) (lucasReadback n) := by
      rw [show BEDC.Derived.FibonacciLucasIdentitiesUp.fib n = Nat.fib n by
        exact BedcMathlibBridge.Constructive.Fibonacci.toNat_eq_nat_fib n]
      rfl

end BedcMathlibBridge.Constructive.FibonacciLucasIdentity
