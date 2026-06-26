import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.FibonacciUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.Window6LucasFibNormRelation

namespace BEDC.Derived.LucasSequenceUp

abbrev integerRing :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev integerLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

abbrev altSign : Nat -> Int :=
  BEDC.Derived.Window6Transfer.altSign

def lucasU (P Q : Int) : Nat -> Int
  | 0 => 0
  | 1 => 1
  | n + 2 => P * lucasU P Q (n + 1) - Q * lucasU P Q n

def lucasV (P Q : Int) : Nat -> Int
  | 0 => 2
  | 1 => P
  | n + 2 => P * lucasV P Q (n + 1) - Q * lucasV P Q n

def discriminant (P Q : Int) : Int :=
  P * P - 4 * Q

abbrev fibonacciSpecialU (n : Nat) : Int :=
  lucasU 1 (-1) n

abbrev fibonacciSpecialV (n : Nat) : Int :=
  lucasV 1 (-1) n

abbrev fibonacciInt (n : Nat) : Int :=
  (BEDC.Derived.Window6Fibonacci.fib n : Int)

abbrev lucasInt (n : Nat) : Int :=
  (BEDC.Derived.Window6Lucas.lucas n : Int)

private theorem int_neg_neg (x : Int) :
    -(-x) = x := by
  cases x with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n => rfl
  | negSucc n => rfl

private theorem sub_neg_one_mul (x y : Int) :
    x - (-1 : Int) * y = x + y := by
  rw [← Int.neg_eq_neg_one_mul y]
  rw [Int.sub_eq_add_neg]
  rw [int_neg_neg]

private theorem fibonacci_special_step (x y : Int) :
    (1 : Int) * x - (-1 : Int) * y = x + y := by
  rw [Int.one_mul]
  exact sub_neg_one_mul x y

private def twoStep (motive : Nat -> Prop)
    (zeroCase : motive 0)
    (oneCase : motive 1)
    (stepCase : ∀ n, motive n -> motive (n + 1) -> motive (n + 2)) :
    ∀ n, motive n
  | 0 => zeroCase
  | 1 => oneCase
  | n + 2 =>
      stepCase n
        (twoStep motive zeroCase oneCase stepCase n)
        (twoStep motive zeroCase oneCase stepCase (n + 1))

theorem lucasU_zero (P Q : Int) :
    lucasU P Q 0 = 0 := by
  rfl

theorem lucasU_one (P Q : Int) :
    lucasU P Q 1 = 1 := by
  rfl

theorem lucasU_recurrence (P Q : Int) (n : Nat) :
    lucasU P Q (n + 2) =
      P * lucasU P Q (n + 1) - Q * lucasU P Q n := by
  rfl

theorem lucasV_zero (P Q : Int) :
    lucasV P Q 0 = 2 := by
  rfl

theorem lucasV_one (P Q : Int) :
    lucasV P Q 1 = P := by
  rfl

theorem lucasV_recurrence (P Q : Int) (n : Nat) :
    lucasV P Q (n + 2) =
      P * lucasV P Q (n + 1) - Q * lucasV P Q n := by
  rfl

theorem lucasU_add_one_identity (P Q : Int) (m : Nat) :
    lucasU P Q (m + 2) =
      lucasV P Q 1 * lucasU P Q (m + 1) - Q * lucasU P Q m := by
  rfl

theorem discriminant_eq (P Q : Int) :
    discriminant P Q = P * P - 4 * Q := by
  rfl

theorem fibonacciSpecialU_zero :
    fibonacciSpecialU 0 = 0 := by
  rfl

theorem fibonacciSpecialU_one :
    fibonacciSpecialU 1 = 1 := by
  rfl

theorem fibonacciSpecialU_recurrence (n : Nat) :
    fibonacciSpecialU (n + 2) =
      1 * fibonacciSpecialU (n + 1) - (-1) * fibonacciSpecialU n := by
  rfl

theorem fibonacciSpecialU_add_recurrence (n : Nat) :
    fibonacciSpecialU (n + 2) =
      fibonacciSpecialU (n + 1) + fibonacciSpecialU n := by
  exact fibonacci_special_step (fibonacciSpecialU (n + 1)) (fibonacciSpecialU n)

theorem fibonacciSpecialV_zero :
    fibonacciSpecialV 0 = 2 := by
  rfl

theorem fibonacciSpecialV_one :
    fibonacciSpecialV 1 = 1 := by
  rfl

theorem fibonacciSpecialV_recurrence (n : Nat) :
    fibonacciSpecialV (n + 2) =
      1 * fibonacciSpecialV (n + 1) - (-1) * fibonacciSpecialV n := by
  rfl

theorem fibonacciSpecialV_add_recurrence (n : Nat) :
    fibonacciSpecialV (n + 2) =
      fibonacciSpecialV (n + 1) + fibonacciSpecialV n := by
  exact fibonacci_special_step (fibonacciSpecialV (n + 1)) (fibonacciSpecialV n)

theorem lucasU_fibonacci_special_eq_fibonacciInt (n : Nat) :
    lucasU 1 (-1) n = fibonacciInt n := by
  exact twoStep
    (fun k => lucasU 1 (-1) k = fibonacciInt k)
    (by rfl)
    (by rfl)
    (by
      intro k h0 h1
      unfold lucasU
      rw [h1, h0]
      rw [fibonacci_special_step]
      change fibonacciInt (k + 1) + fibonacciInt k = fibonacciInt (k + 2)
      change
        ((BEDC.Derived.Window6Fibonacci.fib (k + 1) : Nat) : Int) +
          ((BEDC.Derived.Window6Fibonacci.fib k : Nat) : Int) =
            ((BEDC.Derived.Window6Fibonacci.fib (k + 1) +
              BEDC.Derived.Window6Fibonacci.fib k : Nat) : Int)
      exact Int.ofNat_add_ofNat
        (BEDC.Derived.Window6Fibonacci.fib (k + 1))
        (BEDC.Derived.Window6Fibonacci.fib k))
    n

theorem lucasV_fibonacci_special_eq_lucasInt (n : Nat) :
    lucasV 1 (-1) n = lucasInt n := by
  exact twoStep
    (fun k => lucasV 1 (-1) k = lucasInt k)
    (by rfl)
    (by rfl)
    (by
      intro k h0 h1
      unfold lucasV
      rw [h1, h0]
      rw [fibonacci_special_step]
      change lucasInt (k + 1) + lucasInt k = lucasInt (k + 2)
      change
        ((BEDC.Derived.Window6Lucas.lucas (k + 1) : Nat) : Int) +
          ((BEDC.Derived.Window6Lucas.lucas k : Nat) : Int) =
            ((BEDC.Derived.Window6Lucas.lucas (k + 1) +
              BEDC.Derived.Window6Lucas.lucas k : Nat) : Int)
      exact Int.ofNat_add_ofNat
        (BEDC.Derived.Window6Lucas.lucas (k + 1))
        (BEDC.Derived.Window6Lucas.lucas k))
    n

theorem fibonacciSpecialU_eq_fibonacciInt (n : Nat) :
    fibonacciSpecialU n = fibonacciInt n :=
  lucasU_fibonacci_special_eq_fibonacciInt n

theorem fibonacciSpecialV_eq_lucasInt (n : Nat) :
    fibonacciSpecialV n = lucasInt n :=
  lucasV_fibonacci_special_eq_lucasInt n

theorem fibonacciSpecialU_eq_fibonacciInt_zero :
    fibonacciSpecialU 0 = fibonacciInt 0 := by
  rfl

theorem fibonacciSpecialU_eq_fibonacciInt_one :
    fibonacciSpecialU 1 = fibonacciInt 1 := by
  rfl

theorem fibonacciSpecialU_eq_fibonacciInt_two :
    fibonacciSpecialU 2 = fibonacciInt 2 := by
  rfl

theorem fibonacciSpecialU_eq_fibonacciInt_three :
    fibonacciSpecialU 3 = fibonacciInt 3 := by
  rfl

theorem fibonacciSpecialU_eq_fibonacciInt_four :
    fibonacciSpecialU 4 = fibonacciInt 4 := by
  rfl

theorem fibonacciSpecialU_eq_fibonacciInt_five :
    fibonacciSpecialU 5 = fibonacciInt 5 := by
  rfl

theorem fibonacciSpecialV_eq_lucasInt_zero :
    fibonacciSpecialV 0 = lucasInt 0 := by
  rfl

theorem fibonacciSpecialV_eq_lucasInt_one :
    fibonacciSpecialV 1 = lucasInt 1 := by
  rfl

theorem fibonacciSpecialV_eq_lucasInt_two :
    fibonacciSpecialV 2 = lucasInt 2 := by
  rfl

theorem fibonacciSpecialV_eq_lucasInt_three :
    fibonacciSpecialV 3 = lucasInt 3 := by
  rfl

theorem fibonacciSpecialV_eq_lucasInt_four :
    fibonacciSpecialV 4 = lucasInt 4 := by
  rfl

theorem fibonacciSpecialV_eq_lucasInt_five :
    fibonacciSpecialV 5 = lucasInt 5 := by
  rfl

private theorem discriminant_special :
    discriminant 1 (-1) = 5 := by
  rfl

theorem fibonacciSpecial_norm_identity (n : Nat) :
    fibonacciSpecialV n ^ 2 -
      discriminant 1 (-1) * fibonacciSpecialU n ^ 2 =
        4 * altSign n := by
  change
    (lucasV 1 (-1) n) ^ 2 -
      discriminant 1 (-1) * (lucasU 1 (-1) n) ^ 2 =
        4 * BEDC.Derived.Window6Transfer.altSign n
  rw [lucasU_fibonacci_special_eq_fibonacciInt n,
    lucasV_fibonacci_special_eq_lucasInt n]
  rw [discriminant_special]
  exact BEDC.Derived.Window6LucasFibNormRelation.lucas_fib_norm_universal n

end BEDC.Derived.LucasSequenceUp
