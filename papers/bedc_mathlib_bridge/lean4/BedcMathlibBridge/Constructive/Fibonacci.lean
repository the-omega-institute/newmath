import BEDC.Derived.FibonacciUp
import Mathlib.Data.Nat.Fib.Basic

namespace BedcMathlibBridge.Constructive.Fibonacci

private def mathlibFibProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.fib n = Nat.fib n := fun _ => rfl
  ()

private theorem iterate_succ_apply_last {α : Type} (f : α -> α) :
    ∀ (n : Nat) (x : α), f^[n + 1] x = f (f^[n] x)
  | 0, _ => rfl
  | n + 1, x => by
      calc
        f^[n + 1 + 1] x = f^[n + 1] (f x) := by rfl
        _ = f (f^[n] (f x)) := iterate_succ_apply_last f n (f x)
        _ = f (f^[n + 1] x) := by rfl

private def natFibStep (p : Nat × Nat) : Nat × Nat :=
  (p.2, p.1 + p.2)

private theorem nat_fib_add_two (n : Nat) :
    Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := by
  unfold Nat.fib
  change (natFibStep^[n + 2] (0, 1)).1 =
    (natFibStep^[n] (0, 1)).1 + (natFibStep^[n + 1] (0, 1)).1
  cases hBase : natFibStep^[n] (0, 1) with
  | mk a b =>
      have hNext : natFibStep^[n + 1] (0, 1) = (b, a + b) := by
        calc
          natFibStep^[n + 1] (0, 1) = natFibStep (natFibStep^[n] (0, 1)) :=
            iterate_succ_apply_last natFibStep n (0, 1)
          _ = (b, a + b) := by
            rw [hBase]
            rfl
      have hNextNext : natFibStep^[n + 2] (0, 1) = (a + b, b + (a + b)) := by
        calc
          natFibStep^[n + 2] (0, 1) = natFibStep (natFibStep^[n + 1] (0, 1)) := by
            change natFibStep^[n + 1 + 1] (0, 1) =
              natFibStep (natFibStep^[n + 1] (0, 1))
            exact iterate_succ_apply_last natFibStep (n + 1) (0, 1)
          _ = (a + b, b + (a + b)) := by
            rw [hNext]
            rfl
      rw [hNextNext, hNext]

def toNat (n : Nat) : Nat :=
  let _ := mathlibFibProvenanceAnchor
  BEDC.Derived.FibonacciUp.fib n

theorem toNat_zero : toNat 0 = 0 := by
  rfl

theorem toNat_one : toNat 1 = 1 := by
  rfl

theorem toNat_recurrence (n : Nat) :
    toNat (n + 2) = toNat (n + 1) + toNat n := by
  rfl

theorem toNat_recurrence_mathlib_order (n : Nat) :
    toNat (n + 2) = toNat n + toNat (n + 1) := by
  rw [toNat_recurrence, Nat.add_comm]

private theorem toNat_pair_eq_nat_fib (n : Nat) :
    toNat n = Nat.fib n ∧ toNat (n + 1) = Nat.fib (n + 1) := by
  induction n with
  | zero =>
      constructor
      · rfl
      · rfl
  | succ n ih =>
      constructor
      · exact ih.right
      · change toNat (n + 2) = Nat.fib (n + 2)
        calc
          toNat (n + 2) = toNat n + toNat (n + 1) :=
            toNat_recurrence_mathlib_order n
          _ = Nat.fib n + Nat.fib (n + 1) := by
            rw [ih.left, ih.right]
          _ = Nat.fib (n + 2) := (nat_fib_add_two n).symm

theorem toNat_eq_nat_fib (n : Nat) :
    toNat n = Nat.fib n :=
  (toNat_pair_eq_nat_fib n).left

end BedcMathlibBridge.Constructive.Fibonacci
