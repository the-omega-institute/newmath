import BEDC.Derived.LucasSequenceUp
import BEDC.Derived.PellLucasUp
import BEDC.Derived.JacobsthalUp

namespace BEDC.Derived.LucasSequenceGeneralUp

abbrev lucasU : Int -> Int -> Nat -> Int :=
  BEDC.Derived.LucasSequenceUp.lucasU

abbrev lucasV : Int -> Int -> Nat -> Int :=
  BEDC.Derived.LucasSequenceUp.lucasV

abbrev discriminant : Int -> Int -> Int :=
  BEDC.Derived.LucasSequenceUp.discriminant

def qpow (Q : Int) : Nat -> Int
  | 0 => 1
  | n + 1 => qpow Q n * Q

def lucasNorm (P Q : Int) (n : Nat) : Int :=
  lucasV P Q n ^ (2 : Nat) -
    discriminant P Q * lucasU P Q n ^ (2 : Nat)

abbrev fibonacciU (n : Nat) : Int :=
  lucasU 1 (-1) n

abbrev fibonacciV (n : Nat) : Int :=
  lucasV 1 (-1) n

abbrev pellU (n : Nat) : Int :=
  lucasU 2 (-1) n

abbrev pellV (n : Nat) : Int :=
  lucasV 2 (-1) n

abbrev jacobsthalU (n : Nat) : Int :=
  lucasU 1 (-2) n

abbrev jacobsthalV (n : Nat) : Int :=
  lucasV 1 (-2) n

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

private theorem int_mul_neg_one_right_clean (x : Int) :
    x * (-1 : Int) = -x := by
  cases x with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n =>
          change Int.negOfNat ((n + 1) * 1) = Int.negOfNat (n + 1)
          rw [Nat.mul_one]
  | negSucc n =>
      change Int.ofNat ((n + 1) * 1) = Int.ofNat (n + 1)
      rw [Nat.mul_one]

theorem lucasU_zero (P Q : Int) :
    lucasU P Q 0 = 0 :=
  BEDC.Derived.LucasSequenceUp.lucasU_zero P Q

theorem lucasU_one (P Q : Int) :
    lucasU P Q 1 = 1 :=
  BEDC.Derived.LucasSequenceUp.lucasU_one P Q

theorem lucasU_recurrence (P Q : Int) (n : Nat) :
    lucasU P Q (n + 2) =
      P * lucasU P Q (n + 1) - Q * lucasU P Q n :=
  BEDC.Derived.LucasSequenceUp.lucasU_recurrence P Q n

theorem lucasV_zero (P Q : Int) :
    lucasV P Q 0 = 2 :=
  BEDC.Derived.LucasSequenceUp.lucasV_zero P Q

theorem lucasV_one (P Q : Int) :
    lucasV P Q 1 = P :=
  BEDC.Derived.LucasSequenceUp.lucasV_one P Q

theorem lucasV_recurrence (P Q : Int) (n : Nat) :
    lucasV P Q (n + 2) =
      P * lucasV P Q (n + 1) - Q * lucasV P Q n :=
  BEDC.Derived.LucasSequenceUp.lucasV_recurrence P Q n

theorem discriminant_eq (P Q : Int) :
    discriminant P Q = P * P - 4 * Q :=
  BEDC.Derived.LucasSequenceUp.discriminant_eq P Q

theorem qpow_zero (Q : Int) :
    qpow Q 0 = 1 := by
  rfl

theorem qpow_succ (Q : Int) (n : Nat) :
    qpow Q (n + 1) = qpow Q n * Q := by
  rfl

theorem norm_zero_general (P Q : Int) :
    lucasNorm P Q 0 = 4 * qpow Q 0 := by
  unfold lucasNorm discriminant lucasV lucasU qpow
  change (4 : Int) - (P * P - 4 * Q) * 0 = 4 * 1
  rw [Int.mul_zero]
  rw [Int.sub_eq_add_neg]
  rw [show (-(0 : Int)) = 0 by rfl]
  rw [Int.add_zero]
  rw [int_mul_one_right_clean]

theorem qpow_neg_one_eq_altSign (n : Nat) :
    qpow (-1) n = BEDC.Derived.Window6Transfer.altSign n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold qpow
      rw [ih]
      rw [int_mul_neg_one_right_clean]
      rfl

theorem fibonacci_norm_zero :
    lucasNorm 1 (-1) 0 = 4 * qpow (-1) 0 := by
  exact norm_zero_general 1 (-1)

theorem fibonacci_norm_one :
    lucasNorm 1 (-1) 1 = 4 * qpow (-1) 1 := by
  rfl

theorem fibonacci_norm_identity (n : Nat) :
    lucasNorm 1 (-1) n = 4 * qpow (-1) n := by
  rw [qpow_neg_one_eq_altSign]
  exact BEDC.Derived.LucasSequenceUp.fibonacciSpecial_norm_identity n

theorem fibonacciU_zero :
    fibonacciU 0 = 0 := by
  rfl

theorem fibonacciU_one :
    fibonacciU 1 = 1 := by
  rfl

theorem fibonacciU_recurrence (n : Nat) :
    fibonacciU (n + 2) = fibonacciU (n + 1) + fibonacciU n := by
  exact BEDC.Derived.LucasSequenceUp.fibonacciSpecialU_add_recurrence n

theorem fibonacciV_zero :
    fibonacciV 0 = 2 := by
  rfl

theorem fibonacciV_one :
    fibonacciV 1 = 1 := by
  rfl

theorem fibonacciV_recurrence (n : Nat) :
    fibonacciV (n + 2) = fibonacciV (n + 1) + fibonacciV n := by
  exact BEDC.Derived.LucasSequenceUp.fibonacciSpecialV_add_recurrence n

theorem fibonacciU_eq_FibonacciUp (n : Nat) :
    fibonacciU n = (BEDC.Derived.FibonacciUp.fib n : Int) :=
  BEDC.Derived.LucasSequenceUp.fibonacciSpecialU_eq_fibonacciInt n

theorem fibonacciV_eq_FibonacciUp_lucas (n : Nat) :
    fibonacciV n = (BEDC.Derived.FibonacciUp.lucas n : Int) :=
  BEDC.Derived.LucasSequenceUp.fibonacciSpecialV_eq_lucasInt n

theorem pellU_zero :
    pellU 0 = 0 := by
  rfl

theorem pellU_one :
    pellU 1 = 1 := by
  rfl

theorem pellU_recurrence (n : Nat) :
    pellU (n + 2) = 2 * pellU (n + 1) - (-1) * pellU n := by
  exact BEDC.Derived.PellLucasUp.lucasU_pell_parameters.right.right n

theorem pellV_zero :
    pellV 0 = 2 := by
  rfl

theorem pellV_one :
    pellV 1 = 2 := by
  rfl

theorem pellV_recurrence (n : Nat) :
    pellV (n + 2) = 2 * pellV (n + 1) - (-1) * pellV n := by
  exact BEDC.Derived.PellLucasUp.lucasV_companion_pell_parameters.right.right n

theorem pell_parameters :
    lucasU 2 (-1) 0 = 0 ∧ lucasU 2 (-1) 1 = 1 ∧
      (∀ n : Nat,
        lucasU 2 (-1) (n + 2) =
          2 * lucasU 2 (-1) (n + 1) - (-1) * lucasU 2 (-1) n) :=
  BEDC.Derived.PellLucasUp.lucasU_pell_parameters

theorem pell_companion_parameters :
    lucasV 2 (-1) 0 = 2 ∧ lucasV 2 (-1) 1 = 2 ∧
      (∀ n : Nat,
        lucasV 2 (-1) (n + 2) =
          2 * lucasV 2 (-1) (n + 1) - (-1) * lucasV 2 (-1) n) :=
  BEDC.Derived.PellLucasUp.lucasV_companion_pell_parameters

theorem jacobsthalU_zero :
    jacobsthalU 0 = 0 := by
  rfl

theorem jacobsthalU_one :
    jacobsthalU 1 = 1 := by
  rfl

theorem jacobsthalU_recurrence (n : Nat) :
    jacobsthalU (n + 2) = jacobsthalU (n + 1) + 2 * jacobsthalU n := by
  exact BEDC.Derived.JacobsthalUp.lucasUJacobsthal_recurrence n

theorem jacobsthalV_zero :
    jacobsthalV 0 = 2 := by
  rfl

theorem jacobsthalV_one :
    jacobsthalV 1 = 1 := by
  rfl

theorem jacobsthalV_recurrence (n : Nat) :
    jacobsthalV (n + 2) = jacobsthalV (n + 1) + 2 * jacobsthalV n := by
  exact BEDC.Derived.JacobsthalUp.lucasVJacobsthal_recurrence n

theorem jacobsthalU_matches_existing_recurrence (n : Nat) :
    jacobsthalU (n + 2) =
      jacobsthalU (n + 1) + 2 * jacobsthalU n :=
  BEDC.Derived.JacobsthalUp.lucasUJacobsthal_recurrence n

theorem jacobsthalV_matches_existing_recurrence (n : Nat) :
    jacobsthalV (n + 2) =
      jacobsthalV (n + 1) + 2 * jacobsthalV n :=
  BEDC.Derived.JacobsthalUp.lucasVJacobsthal_recurrence n

theorem add_formula_second_zero_seed (P Q : Int) :
    lucasU P Q (0 + 0) =
      lucasU P Q 0 * lucasU P Q (0 + 1) -
        Q * lucasU P Q (0 - 1) * lucasU P Q 0 := by
  unfold lucasU
  change (0 : Int) = 0 * 1 - Q * 0 * 0
  rw [Int.mul_zero]
  rw [int_mul_one_right_clean]
  rw [Int.sub_eq_add_neg]
  rw [show (-(0 : Int)) = 0 by rfl]
  rw [Int.add_zero]

theorem add_formula_zero_zero :
    lucasU 1 (-1) (0 + 0) =
      lucasU 1 (-1) 0 * lucasU 1 (-1) (0 + 1) -
        (-1) * lucasU 1 (-1) (0 - 1) * lucasU 1 (-1) 0 :=
  add_formula_second_zero_seed 1 (-1)

theorem add_formula_one_index_seed :
    lucasU 1 (-1) (1 + 1) =
      lucasU 1 (-1) 1 * lucasU 1 (-1) (1 + 1) -
        (-1) * lucasU 1 (-1) (1 - 1) * lucasU 1 (-1) 1 := by
  rfl

end BEDC.Derived.LucasSequenceGeneralUp
