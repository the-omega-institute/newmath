import BEDC.Derived.Window6TransferMatrix
import BEDC.Derived.Window6LucasCount
import BEDC.Derived.Window6FibonacciCount

namespace BEDC.Derived.Window6Doubling

abbrev fib : Nat -> Nat :=
  BEDC.Derived.Window6Fibonacci.fib

abbrev lucas : Nat -> Nat :=
  BEDC.Derived.Window6Lucas.lucas

/--
The identity `F_{2n}=F_n L_n` is the Fibonacci doubling law.  It is the
Nat-level form of the transfer-matrix observation `M^{2n}=(M^n)^2`, with
`M_pow_fib` identifying the Fibonacci entries and `lucas_eq_fib_add`
identifying the Lucas row sum.
-/
theorem transfer_b_entry_succ (n : Nat) :
    (BEDC.Derived.Window6Transfer.npow
      BEDC.Derived.Window6Transfer.M (n + 1)).b =
      ((fib (n + 1) : Nat) : Int) := by
  rw [BEDC.Derived.Window6Transfer.M_pow_fib n]

private theorem add_right_rotation (a b c d : Nat) :
    a + b + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [Nat.add_assoc a c (b + d)]

private theorem add_mul_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * Nat.succ c =
            (a + b) * c + (a + b) := Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) :=
          congrArg (fun x => x + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun x => a * c + (x + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun x => x + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

private theorem fib_pair_step (a0 a1 b0 b1 : Nat) :
    ((a1 + a0) * b1 + a1 * b0) + (a1 * b1 + a0 * b0) =
      ((a1 + a0) + a1) * b1 + (a1 + a0) * b0 := by
  calc
    ((a1 + a0) * b1 + a1 * b0) + (a1 * b1 + a0 * b0) =
        (((a1 + a0) * b1 + a1 * b1) + (a1 * b0 + a0 * b0)) := by
      rw [add_right_rotation]
    _ = (((a1 + a0) + a1) * b1 + (a1 * b0 + a0 * b0)) := by
      rw [(add_mul_pure (a1 + a0) a1 b1).symm]
    _ = (((a1 + a0) + a1) * b1 + (a1 + a0) * b0) := by
      rw [(add_mul_pure a1 a0 b0).symm]

private theorem fib_add_pair (m n : Nat) :
    fib (m + n + 1) =
        fib (m + 1) * fib (n + 1) + fib m * fib n ∧
      fib (m + n + 2) =
        fib (m + 2) * fib (n + 1) + fib (m + 1) * fib n := by
  induction m with
  | zero =>
      constructor
      · rw [Nat.zero_add]
        change fib (n + 1) = 1 * fib (n + 1) + 0 * fib n
        rw [Nat.one_mul]
        rw [Nat.zero_mul]
        exact (Nat.add_zero (fib (n + 1))).symm
      · rw [Nat.zero_add]
        change fib (n + 2) = 1 * fib (n + 1) + 1 * fib n
        rw [Nat.one_mul]
        rw [Nat.one_mul]
        rfl
  | succ m ih =>
      constructor
      · rw [show m + 1 + n + 1 = m + n + 2 by
          rw [Nat.add_assoc m 1 n]
          rw [Nat.add_comm 1 n]
          rw [← Nat.add_assoc m n 1]]
        change fib (m + n + 2) =
          fib (m + 2) * fib (n + 1) + fib (m + 1) * fib n
        exact ih.right
      · calc
          fib (m + 1 + n + 2) =
              fib (m + n + 3) := by
            rw [show m + 1 + n + 2 = m + n + 3 by
              rw [Nat.add_assoc m 1 n]
              rw [Nat.add_comm 1 n]
              rw [← Nat.add_assoc m n 1]]
          _ = fib (m + n + 2) + fib (m + n + 1) := by
            rfl
          _ =
              (fib (m + 2) * fib (n + 1) + fib (m + 1) * fib n) +
                (fib (m + 1) * fib (n + 1) + fib m * fib n) := by
            rw [ih.left, ih.right]
          _ =
              fib (m + 1 + 2) * fib (n + 1) +
                fib (m + 1 + 1) * fib n := by
            change ((fib (m + 1) + fib m) * fib (n + 1) +
                fib (m + 1) * fib n) +
                (fib (m + 1) * fib (n + 1) + fib m * fib n) =
              ((fib (m + 1) + fib m) + fib (m + 1)) * fib (n + 1) +
                (fib (m + 1) + fib m) * fib n
            exact fib_pair_step (fib m) (fib (m + 1)) (fib n) (fib (n + 1))

private theorem fib_add_one (m n : Nat) :
    fib (m + n + 1) =
      fib (m + 1) * fib (n + 1) + fib m * fib n := by
  exact (fib_add_pair m n).left

private theorem two_mul_eq_add_self (n : Nat) :
    2 * n = n + n := by
  exact Nat.two_mul n

private theorem fib_shift_doubling (n : Nat) :
    fib (2 * n + 2) = fib (n + 1) * lucas (n + 1) := by
  have h :=
    fib_add_one (n + 1) n
  rw [show n + 1 + n + 1 = 2 * n + 2 by
    rw [two_mul_eq_add_self n]
    rw [Nat.add_assoc n 1 n]
    rw [Nat.add_comm 1 n]
    rw [← Nat.add_assoc n n 1]] at h
  calc
    fib (2 * n + 2) =
        fib (n + 1 + 1) * fib (n + 1) + fib (n + 1) * fib n := h
    _ =
        fib (n + 1) * fib (n + 2) + fib (n + 1) * fib n := by
      rw [Nat.mul_comm (fib (n + 1 + 1)) (fib (n + 1))]
    _ =
        fib (n + 1) * (fib (n + 2) + fib n) := by
      rw [Nat.mul_add]
    _ =
        fib (n + 1) * lucas (n + 1) := by
      exact congrArg (fun x => fib (n + 1) * x)
        (BEDC.Derived.Window6Lucas.lucas_eq_fib_add n).symm

theorem fib_two_mul_eq_fib_mul_lucas (n : Nat) :
    fib (2 * n) = fib n * lucas n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      exact fib_shift_doubling n

example : fib 12 = fib 6 * lucas 6 := by
  rfl

example : fib 10 = fib 5 * lucas 5 := by
  rfl

end BEDC.Derived.Window6Doubling
