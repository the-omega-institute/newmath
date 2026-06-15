import BEDC.Derived.Window6FibonacciCount

namespace BEDC.Derived.Window6Lucas

abbrev fib : Nat -> Nat :=
  BEDC.Derived.Window6Fibonacci.fib

/--
`lucas m` is the Window6 length-`m` cyclic no-adjacent-one word count,
equivalently the trace of the two-state transfer matrix power `M^m`.
This file formalizes the Lucas recurrence and its Fibonacci bridge inside
the mathlib-free constructive Lean fragment with no placeholder proofs.
-/
def lucas : Nat -> Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

theorem lucas_recurrence (m : Nat) :
    lucas (m + 2) = lucas (m + 1) + lucas m := by
  rfl

theorem lucas_one : lucas 1 = 1 := by
  rfl

theorem lucas_two : lucas 2 = 3 := by
  rfl

theorem lucas_six : lucas 6 = 18 := by
  rfl

private theorem add_right_rotation (a b c d : Nat) :
    a + b + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [Nat.add_assoc a c (b + d)]

private theorem lucas_fib_bridge_pair (m : Nat) :
    lucas (m + 1) = fib (m + 2) + fib m ∧
      lucas (m + 2) = fib (m + 3) + fib (m + 1) := by
  induction m with
  | zero =>
      constructor
      · rfl
      · rfl
  | succ m ih =>
      constructor
      · exact ih.right
      · rw [lucas_recurrence, ih.right, ih.left]
        rw [add_right_rotation]
        rfl

theorem lucas_eq_fib_add (m : Nat) :
    lucas (m + 1) = fib (m + 2) + fib m := by
  exact (lucas_fib_bridge_pair m).left

end BEDC.Derived.Window6Lucas
