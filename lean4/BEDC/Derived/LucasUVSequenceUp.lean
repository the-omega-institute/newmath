import BEDC.Derived.LucasSequenceGeneralUp
import BEDC.Derived.FibonacciLucasIdentitiesUp

namespace BEDC.Derived.LucasUVSequenceUp

abbrev lucasU : Int -> Int -> Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasU

abbrev lucasV : Int -> Int -> Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasV

abbrev discriminant : Int -> Int -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.discriminant

abbrev qpow : Int -> Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.qpow

abbrev lucasNorm : Int -> Int -> Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasNorm

abbrev fibonacciU : Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciU

abbrev fibonacciV : Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciV

abbrev pellU : Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.pellU

abbrev pellV : Nat -> Int :=
  BEDC.Derived.LucasSequenceGeneralUp.pellV

abbrev mersenneU : Nat -> Int :=
  lucasU 3 2

abbrev mersenneV : Nat -> Int :=
  lucasV 3 2

private theorem int_mul_one_right_clean (x : Int) :
    x * (1 : Int) = x := by
  cases x with
  | ofNat n =>
      change Int.ofNat (n * 1) = Int.ofNat n
      rw [Nat.mul_one]
  | negSucc n =>
      change Int.negOfNat ((n + 1) * 1) = Int.negSucc n
      rw [Nat.mul_one]
      rfl

theorem lucasU_zero (P Q : Int) :
    lucasU P Q 0 = 0 :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasU_zero P Q

theorem lucasU_one (P Q : Int) :
    lucasU P Q 1 = 1 :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasU_one P Q

theorem lucasU_recurrence (P Q : Int) (n : Nat) :
    lucasU P Q (n + 2) =
      P * lucasU P Q (n + 1) - Q * lucasU P Q n :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasU_recurrence P Q n

theorem lucasV_zero (P Q : Int) :
    lucasV P Q 0 = 2 :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasV_zero P Q

theorem lucasV_one (P Q : Int) :
    lucasV P Q 1 = P :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasV_one P Q

theorem lucasV_recurrence (P Q : Int) (n : Nat) :
    lucasV P Q (n + 2) =
      P * lucasV P Q (n + 1) - Q * lucasV P Q n :=
  BEDC.Derived.LucasSequenceGeneralUp.lucasV_recurrence P Q n

theorem lucasV_one_eq_lucasU_two (P Q : Int) :
    lucasV P Q 1 = lucasU P Q 2 := by
  unfold lucasV lucasU
  change P = P * 1 - Q * 0
  rw [Int.mul_zero]
  rw [int_mul_one_right_clean]
  rw [Int.sub_eq_add_neg]
  rw [show (-(0 : Int)) = 0 by rfl]
  rw [Int.add_zero]

theorem discriminant_eq (P Q : Int) :
    discriminant P Q = P * P - 4 * Q :=
  BEDC.Derived.LucasSequenceGeneralUp.discriminant_eq P Q

theorem lucasU_add_one_identity (P Q : Int) (m : Nat) :
    lucasU P Q (m + 2) =
      lucasV P Q 1 * lucasU P Q (m + 1) - Q * lucasU P Q m :=
  BEDC.Derived.LucasSequenceUp.lucasU_add_one_identity P Q m

theorem fibonacciU_zero :
    fibonacciU 0 = 0 :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciU_zero

theorem fibonacciU_one :
    fibonacciU 1 = 1 :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciU_one

theorem fibonacciU_recurrence (n : Nat) :
    fibonacciU (n + 2) = fibonacciU (n + 1) + fibonacciU n :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciU_recurrence n

theorem fibonacciV_zero :
    fibonacciV 0 = 2 :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciV_zero

theorem fibonacciV_one :
    fibonacciV 1 = 1 :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciV_one

theorem fibonacciV_recurrence (n : Nat) :
    fibonacciV (n + 2) = fibonacciV (n + 1) + fibonacciV n :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciV_recurrence n

theorem fibonacciU_eq_FibonacciUp (n : Nat) :
    fibonacciU n = (BEDC.Derived.FibonacciUp.fib n : Int) :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciU_eq_FibonacciUp n

theorem fibonacciV_eq_FibonacciUp_lucas (n : Nat) :
    fibonacciV n = (BEDC.Derived.FibonacciUp.lucas n : Int) :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacciV_eq_FibonacciUp_lucas n

theorem fibonacciV_succ_eq_fibonacciU_succ_succ_add_fibonacciU (n : Nat) :
    fibonacciV (n + 1) = fibonacciU (n + 2) + fibonacciU n := by
  rw [fibonacciV_eq_FibonacciUp_lucas]
  rw [fibonacciU_eq_FibonacciUp]
  rw [fibonacciU_eq_FibonacciUp]
  rw [BEDC.Derived.FibonacciUp.lucas_eq_fib_add n]
  exact (Int.ofNat_add_ofNat
    (BEDC.Derived.FibonacciUp.fib (n + 2))
    (BEDC.Derived.FibonacciUp.fib n)).symm

theorem fibonacci_norm_identity (n : Nat) :
    lucasNorm 1 (-1) n = 4 * qpow (-1) n :=
  BEDC.Derived.LucasSequenceGeneralUp.fibonacci_norm_identity n

theorem fibonacci_nat_addition_succ (m n : Nat) :
    BEDC.Derived.FibonacciLucasIdentitiesUp.fib (m + n + 1) =
      BEDC.Derived.FibonacciLucasIdentitiesUp.fib (m + 1) *
          BEDC.Derived.FibonacciLucasIdentitiesUp.fib (n + 1) +
        BEDC.Derived.FibonacciLucasIdentitiesUp.fib m *
          BEDC.Derived.FibonacciLucasIdentitiesUp.fib n :=
  BEDC.Derived.FibonacciLucasIdentitiesUp.fib_addition_succ m n

theorem fibonacciU_addition_succ (m n : Nat) :
    fibonacciU (m + n + 1) =
      fibonacciU (m + 1) * fibonacciU (n + 1) +
        fibonacciU m * fibonacciU n := by
  rw [fibonacciU_eq_FibonacciUp (m + n + 1)]
  rw [fibonacciU_eq_FibonacciUp (m + 1)]
  rw [fibonacciU_eq_FibonacciUp (n + 1)]
  rw [fibonacciU_eq_FibonacciUp m]
  rw [fibonacciU_eq_FibonacciUp n]
  change
    ((BEDC.Derived.FibonacciLucasIdentitiesUp.fib (m + n + 1) : Nat) : Int) =
      ((BEDC.Derived.FibonacciLucasIdentitiesUp.fib (m + 1) : Nat) : Int) *
          ((BEDC.Derived.FibonacciLucasIdentitiesUp.fib (n + 1) : Nat) : Int) +
        ((BEDC.Derived.FibonacciLucasIdentitiesUp.fib m : Nat) : Int) *
          ((BEDC.Derived.FibonacciLucasIdentitiesUp.fib n : Nat) : Int)
  rw [BEDC.Derived.FibonacciLucasIdentitiesUp.fib_addition_succ m n]
  rw [Int.ofNat_mul_ofNat]
  rw [Int.ofNat_mul_ofNat]
  exact (Int.ofNat_add_ofNat
    (BEDC.Derived.FibonacciLucasIdentitiesUp.fib (m + 1) *
      BEDC.Derived.FibonacciLucasIdentitiesUp.fib (n + 1))
    (BEDC.Derived.FibonacciLucasIdentitiesUp.fib m *
      BEDC.Derived.FibonacciLucasIdentitiesUp.fib n)).symm

theorem pellU_zero :
    pellU 0 = 0 :=
  BEDC.Derived.LucasSequenceGeneralUp.pellU_zero

theorem pellU_one :
    pellU 1 = 1 :=
  BEDC.Derived.LucasSequenceGeneralUp.pellU_one

theorem pellU_recurrence (n : Nat) :
    pellU (n + 2) = 2 * pellU (n + 1) - (-1) * pellU n :=
  BEDC.Derived.LucasSequenceGeneralUp.pellU_recurrence n

theorem pellV_zero :
    pellV 0 = 2 :=
  BEDC.Derived.LucasSequenceGeneralUp.pellV_zero

theorem pellV_one :
    pellV 1 = 2 :=
  BEDC.Derived.LucasSequenceGeneralUp.pellV_one

theorem pellV_recurrence (n : Nat) :
    pellV (n + 2) = 2 * pellV (n + 1) - (-1) * pellV n :=
  BEDC.Derived.LucasSequenceGeneralUp.pellV_recurrence n

theorem pell_parameters :
    lucasU 2 (-1) 0 = 0 ∧ lucasU 2 (-1) 1 = 1 ∧
      (∀ n : Nat,
        lucasU 2 (-1) (n + 2) =
          2 * lucasU 2 (-1) (n + 1) - (-1) * lucasU 2 (-1) n) :=
  BEDC.Derived.LucasSequenceGeneralUp.pell_parameters

theorem pell_companion_parameters :
    lucasV 2 (-1) 0 = 2 ∧ lucasV 2 (-1) 1 = 2 ∧
      (∀ n : Nat,
        lucasV 2 (-1) (n + 2) =
          2 * lucasV 2 (-1) (n + 1) - (-1) * lucasV 2 (-1) n) :=
  BEDC.Derived.LucasSequenceGeneralUp.pell_companion_parameters

theorem mersenneU_zero :
    mersenneU 0 = 0 := by
  rfl

theorem mersenneU_one :
    mersenneU 1 = 1 := by
  rfl

theorem mersenneU_recurrence (n : Nat) :
    mersenneU (n + 2) = 3 * mersenneU (n + 1) - 2 * mersenneU n := by
  rfl

theorem mersenneV_zero :
    mersenneV 0 = 2 := by
  rfl

theorem mersenneV_one :
    mersenneV 1 = 3 := by
  rfl

theorem mersenneV_recurrence (n : Nat) :
    mersenneV (n + 2) = 3 * mersenneV (n + 1) - 2 * mersenneV n := by
  rfl

theorem mersenne_discriminant :
    discriminant 3 2 = 1 := by
  rfl

end BEDC.Derived.LucasUVSequenceUp
