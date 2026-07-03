import BedcMathlibBridge.Constructive.Fibonacci
import BEDC.Derived.LeonardoNumberUp

/-!
Leonardo-number readback through the Fibonacci surface.

The BEDC object is the closed recurrence `1, 1, L (n+2) = L (n+1) + L n + 1`.
Its shifted companion is a Fibonacci recurrence with initial value `2`, giving
the pointwise host expression `2 * Nat.fib (n + 1) - 1`.
-/

namespace BedcMathlibBridge.Constructive.Leonardo

private def mathlibFibProvenanceAnchor : Unit :=
  let _ : forall n : Nat, Nat.fib n = Nat.fib n := fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibFibProvenanceAnchor
  BEDC.Derived.LeonardoNumberUp.leonardoNumber n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.LeonardoNumberUp.leonardoNumber n := by
  rfl

theorem toNat_zero :
    toNat 0 = 1 := by
  rfl

theorem toNat_one :
    toNat 1 = 1 := by
  rfl

theorem toNat_recurrence (n : Nat) :
    toNat (n + 2) = toNat (n + 1) + toNat n + 1 := by
  rfl

theorem bedc_fib_eq_nat_fib (n : Nat) :
    BEDC.Derived.FibonacciUp.fib n = Nat.fib n := by
  change BedcMathlibBridge.Constructive.Fibonacci.toNat n = Nat.fib n
  exact BedcMathlibBridge.Constructive.Fibonacci.toNat_eq_nat_fib n

private theorem shiftedLeonardo_pair_eq_two_mul_bedc_fib_succ (n : Nat) :
    BEDC.Derived.LeonardoNumberUp.shiftedLeonardo n =
        2 * BEDC.Derived.FibonacciUp.fib (n + 1) ∧
      BEDC.Derived.LeonardoNumberUp.shiftedLeonardo (n + 1) =
        2 * BEDC.Derived.FibonacciUp.fib (n + 2) := by
  induction n with
  | zero =>
      constructor
      · rfl
      · rfl
  | succ n ih =>
      constructor
      · exact ih.right
      · change
          BEDC.Derived.LeonardoNumberUp.shiftedLeonardo (n + 2) =
            2 * BEDC.Derived.FibonacciUp.fib (n + 3)
        calc
          BEDC.Derived.LeonardoNumberUp.shiftedLeonardo (n + 2) =
              BEDC.Derived.LeonardoNumberUp.shiftedLeonardo (n + 1) +
                BEDC.Derived.LeonardoNumberUp.shiftedLeonardo n :=
            BEDC.Derived.LeonardoNumberUp.shiftedLeonardo_recurrence n
          _ =
              2 * BEDC.Derived.FibonacciUp.fib (n + 2) +
                2 * BEDC.Derived.FibonacciUp.fib (n + 1) := by
            rw [ih.right, ih.left]
          _ =
              2 *
                (BEDC.Derived.FibonacciUp.fib (n + 2) +
                  BEDC.Derived.FibonacciUp.fib (n + 1)) := by
            rw [Nat.mul_add]
          _ = 2 * BEDC.Derived.FibonacciUp.fib (n + 3) := by
            rw [← BEDC.Derived.FibonacciUp.fib_recurrence (n + 1)]

private theorem shiftedLeonardo_eq_two_mul_bedc_fib_succ (n : Nat) :
    BEDC.Derived.LeonardoNumberUp.shiftedLeonardo n =
      2 * BEDC.Derived.FibonacciUp.fib (n + 1) :=
  (shiftedLeonardo_pair_eq_two_mul_bedc_fib_succ n).left

private theorem add_one_sub_one (n : Nat) :
    (n + 1) - 1 = n := by
  rfl

theorem toNat_eq_nat_fib_formula (n : Nat) :
    toNat n = 2 * Nat.fib (n + 1) - 1 := by
  change
    BEDC.Derived.LeonardoNumberUp.leonardoNumber n =
      2 * Nat.fib (n + 1) - 1
  calc
    BEDC.Derived.LeonardoNumberUp.leonardoNumber n =
        BEDC.Derived.LeonardoNumberUp.shiftedLeonardo n - 1 := by
      unfold BEDC.Derived.LeonardoNumberUp.shiftedLeonardo
      exact (add_one_sub_one (BEDC.Derived.LeonardoNumberUp.leonardoNumber n)).symm
    _ = 2 * BEDC.Derived.FibonacciUp.fib (n + 1) - 1 := by
      rw [shiftedLeonardo_eq_two_mul_bedc_fib_succ n]
    _ = 2 * Nat.fib (n + 1) - 1 := by
      rw [bedc_fib_eq_nat_fib (n + 1)]

end BedcMathlibBridge.Constructive.Leonardo
