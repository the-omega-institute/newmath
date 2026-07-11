import BEDC.Derived.HyperfactorialUp
import BEDC.Derived.JacobsthalUp
import Mathlib.Data.Nat.Factorial.DoubleFactorial

namespace BedcMathlibBridge.Constructive.EvenDoubleFactorial

private def mathlibDoubleFactorialProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.doubleFactorial n = Nat.doubleFactorial n := fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibDoubleFactorialProvenanceAnchor
  BEDC.Derived.JacobsthalUp.powTwo n *
    BEDC.Derived.HyperfactorialUp.factorialNat n

theorem toNat_apply (n : Nat) :
    toNat n =
      BEDC.Derived.JacobsthalUp.powTwo n *
        BEDC.Derived.HyperfactorialUp.factorialNat n := by
  rfl

theorem toNat_zero :
    toNat 0 = 1 := by
  rfl

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) :=
          congrArg (fun x => a * x) (Nat.mul_succ b c).symm

theorem toNat_succ (n : Nat) :
    toNat (Nat.succ n) = 2 * Nat.succ n * toNat n := by
  unfold toNat
  rw [BEDC.Derived.JacobsthalUp.powTwo_succ]
  rw [BEDC.Derived.HyperfactorialUp.factorialNat_succ]
  calc
    (2 * BEDC.Derived.JacobsthalUp.powTwo n) *
        (Nat.succ n * BEDC.Derived.HyperfactorialUp.factorialNat n)
        = 2 *
            (BEDC.Derived.JacobsthalUp.powTwo n *
              (Nat.succ n * BEDC.Derived.HyperfactorialUp.factorialNat n)) :=
          nat_mul_assoc_pure 2
            (BEDC.Derived.JacobsthalUp.powTwo n)
            (Nat.succ n * BEDC.Derived.HyperfactorialUp.factorialNat n)
    _ = 2 *
          ((BEDC.Derived.JacobsthalUp.powTwo n * Nat.succ n) *
            BEDC.Derived.HyperfactorialUp.factorialNat n) := by
          rw [← nat_mul_assoc_pure
            (BEDC.Derived.JacobsthalUp.powTwo n)
            (Nat.succ n)
            (BEDC.Derived.HyperfactorialUp.factorialNat n)]
    _ = 2 *
          ((Nat.succ n * BEDC.Derived.JacobsthalUp.powTwo n) *
            BEDC.Derived.HyperfactorialUp.factorialNat n) := by
          rw [Nat.mul_comm (BEDC.Derived.JacobsthalUp.powTwo n) (Nat.succ n)]
    _ = 2 *
          (Nat.succ n *
            (BEDC.Derived.JacobsthalUp.powTwo n *
              BEDC.Derived.HyperfactorialUp.factorialNat n)) := by
          rw [nat_mul_assoc_pure
            (Nat.succ n)
            (BEDC.Derived.JacobsthalUp.powTwo n)
            (BEDC.Derived.HyperfactorialUp.factorialNat n)]
    _ = 2 * Nat.succ n *
          (BEDC.Derived.JacobsthalUp.powTwo n *
            BEDC.Derived.HyperfactorialUp.factorialNat n) := by
          rw [← nat_mul_assoc_pure 2 (Nat.succ n)
            (BEDC.Derived.JacobsthalUp.powTwo n *
              BEDC.Derived.HyperfactorialUp.factorialNat n)]

private theorem doubleFactorial_even_succ (n : Nat) :
    Nat.doubleFactorial (2 * Nat.succ n) =
      2 * Nat.succ n * Nat.doubleFactorial (2 * n) := by
  have hidx : 2 * Nat.succ n = 2 * n + 2 := by
    rw [Nat.mul_succ]
  rw [hidx, Nat.doubleFactorial_add_two, ← hidx]

theorem toNat_eq_doubleFactorial_even (n : Nat) :
    toNat n = Nat.doubleFactorial (2 * n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [toNat_succ, ih, doubleFactorial_even_succ]

end BedcMathlibBridge.Constructive.EvenDoubleFactorial
