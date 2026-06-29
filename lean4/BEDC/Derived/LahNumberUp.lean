import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.LahUp
import BEDC.Derived.PochhammerUp
import BEDC.Derived.RationalUp.Core
import BEDC.Derived.StirlingCycleUp
import BEDC.Derived.StirlingFirstUp
import BEDC.Derived.StirlingUp

namespace BEDC.Derived.LahNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev factorialNat : Nat -> Nat :=
  BEDC.Derived.StirlingFirstUp.factorialNat

abbrev fallingNat (x k : Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natDescPochhammerCount x k

abbrev risingNat (x n : Nat) : Nat :=
  BEDC.Derived.StirlingCycleUp.risingFactorialValue x n

abbrev Z : Type :=
  BEDC.Algebra.Rel.IntegerUp

abbrev Zeq : Z -> Z -> Prop :=
  BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev zOne : Z :=
  integerRing.one

def zOfNat (n : Nat) : Z :=
  BEDC.Derived.RationalUp.intOfNat
    (BEDC.Derived.IntUp.natToUnary n)
    (BEDC.Derived.IntUp.natToUnary_unary n)

-- Lah 数的核心递归由 `LahUp` 承载, 本文件导出闭式表面与整数读回。
abbrev lahNumber : Nat -> Nat -> Nat :=
  BEDC.Derived.LahUp.lahNumber

def lahNumberFn (n k : BHist) : BHist :=
  BEDC.Derived.IntUp.natToUnary
    (lahNumber (bwordLength n) (bwordLength k))

def lahInteger (n k : Nat) : Z :=
  zOfNat (lahNumber n k)

def lahIntegerPair (n k : Nat) : BHist × BHist :=
  BEDC.Derived.RationalUp.intToPair (lahInteger n k)

def lahClosedNumerator : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 0
  | Nat.succ n, Nat.succ k =>
      C n k * factorialNat (Nat.succ n)

def lahClosedDenominator : Nat -> Nat
  | 0 => 1
  | Nat.succ k => factorialNat (Nat.succ k)

def lahClosedFormula (n k : Nat) : Nat :=
  lahClosedNumerator n k / lahClosedDenominator k

def lahExactClosedDivision (n k q : Nat) : Prop :=
  q * lahClosedDenominator k = lahClosedNumerator n k

def lahDescendingExpansionPrefix (x n : Nat) : Nat -> Nat
  | 0 => lahNumber n 0 * fallingNat x 0
  | Nat.succ k =>
      lahDescendingExpansionPrefix x n k +
        lahNumber n (Nat.succ k) * fallingNat x (Nat.succ k)

def lahDescendingExpansion (x n : Nat) : Nat :=
  lahDescendingExpansionPrefix x n n

abbrev lahStirlingDiagonalSum : Nat -> Nat -> Nat :=
  BEDC.Derived.LahUp.lahStirlingDiagonalSum

theorem lahNumber_zero_zero :
    lahNumber 0 0 = 1 := by
  exact BEDC.Derived.LahUp.lahNumber_zero_zero

theorem lahNumber_zero_succ (k : Nat) :
    lahNumber 0 (Nat.succ k) = 0 := by
  exact BEDC.Derived.LahUp.lahNumber_zero_succ k

theorem lahNumber_succ_zero (n : Nat) :
    lahNumber (Nat.succ n) 0 = 0 := by
  exact BEDC.Derived.LahUp.lahNumber_succ_zero n

theorem lahNumber_recurrence (n k : Nat) :
    lahNumber (Nat.succ n) (Nat.succ k) =
      (n + Nat.succ k) * lahNumber n (Nat.succ k) + lahNumber n k := by
  exact BEDC.Derived.LahUp.lahNumber_recurrence n k

theorem lahNumberFn_unary_result (n k : BHist) :
    UnaryHistory (lahNumberFn n k) := by
  unfold lahNumberFn
  exact BEDC.Derived.IntUp.natToUnary_unary _

theorem lahNumberFn_natToUnary (n k : Nat) :
    lahNumberFn
        (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary k) =
      BEDC.Derived.IntUp.natToUnary (lahNumber n k) := by
  unfold lahNumberFn
  repeat rw [BEDC.Derived.IntUp.natToUnary_length]

theorem lahInteger_is_bedc_integer (n k : Nat) :
    BEDC.Derived.IntUp.IntPairCarrier
      (lahIntegerPair n k).1
      (lahIntegerPair n k).2 := by
  unfold lahIntegerPair
  exact BEDC.Derived.RationalUp.intToPair_carrier (lahInteger n k)

theorem lahInteger_reflects_nat (n k : Nat) :
    Zeq (lahInteger n k) (zOfNat (lahNumber n k)) := by
  exact integerRing.refl _

theorem lahInteger_zero_zero :
    Zeq (lahInteger 0 0) zOne := by
  exact integerRing.refl zOne

theorem lahNumber_self_and_above :
    ∀ n : Nat, lahNumber n n = 1 ∧
      ∀ extra : Nat, lahNumber n (Nat.succ (n + extra)) = 0 := by
  exact BEDC.Derived.LahUp.lahNumber_self_and_above

theorem lahNumber_self (n : Nat) :
    lahNumber n n = 1 :=
  (lahNumber_self_and_above n).left

theorem lahNumber_above (n extra : Nat) :
    lahNumber n (Nat.succ (n + extra)) = 0 :=
  (lahNumber_self_and_above n).right extra

theorem lahNumber_succ_one :
    ∀ n : Nat, lahNumber (Nat.succ n) 1 = factorialNat (Nat.succ n) := by
  exact BEDC.Derived.LahUp.lahNumber_succ_one_eq_factorial

theorem lahNumber_succ_one_eq_stirlingCycleRowSum (n : Nat) :
    lahNumber (Nat.succ n) 1 =
      BEDC.Derived.StirlingCycleUp.stirlingCycleRowSum (Nat.succ n) := by
  rw [lahNumber_succ_one]
  rw [BEDC.Derived.StirlingCycleUp.stirlingCycleRowSum_eq_factorial]

theorem zero_sub_clean :
    ∀ k : Nat, 0 - k = 0 := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change Nat.pred (0 - k) = 0
      rw [ih]
      rfl

theorem one_sub_succ (k : Nat) :
    1 - Nat.succ k = 0 := by
  cases k with
  | zero =>
      rfl
  | succ k =>
      change Nat.succ 0 - Nat.succ (Nat.succ k) = 0
      rw [Nat.succ_sub_succ_eq_sub]
      exact zero_sub_clean (Nat.succ k)

theorem falling_one_succ_succ_zero (k : Nat) :
    fallingNat 1 (Nat.succ (Nat.succ k)) = 0 := by
  unfold fallingNat
  rw [BEDC.Derived.PochhammerUp.natDescPochhammerCount_succ 1 (Nat.succ k)]
  rw [one_sub_succ k]
  exact Nat.mul_zero _

theorem lahDescendingExpansionPrefix_one_succ (n fuel : Nat) :
    lahDescendingExpansionPrefix 1 (Nat.succ n) (Nat.succ fuel) =
      lahNumber (Nat.succ n) 1 := by
  induction fuel with
  | zero =>
      change
        lahNumber (Nat.succ n) 0 * 1 +
            lahNumber (Nat.succ n) 1 * 1 =
          lahNumber (Nat.succ n) 1
      rw [lahNumber_succ_zero]
      rw [Nat.zero_mul, Nat.mul_one, Nat.zero_add]
  | succ fuel ih =>
      change
        lahDescendingExpansionPrefix 1 (Nat.succ n) (Nat.succ fuel) +
            lahNumber (Nat.succ n) (Nat.succ (Nat.succ fuel)) *
              fallingNat 1 (Nat.succ (Nat.succ fuel)) =
          lahNumber (Nat.succ n) 1
      rw [ih]
      rw [falling_one_succ_succ_zero]
      rw [Nat.mul_zero, Nat.add_zero]

theorem risingFactorialValue_one_eq_factorial :
    ∀ n : Nat, risingNat 1 n = factorialNat n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change risingNat 1 n * (1 + n) =
        Nat.succ n * factorialNat n
      rw [ih]
      rw [Nat.add_comm 1 n]
      rw [← Nat.succ_eq_add_one n]
      rw [Nat.mul_comm]

theorem risingFactorialValue_one_eq_lah_first_column (n : Nat) :
    risingNat 1 (Nat.succ n) = lahNumber (Nat.succ n) 1 := by
  rw [risingFactorialValue_one_eq_factorial]
  rw [lahNumber_succ_one]

theorem risingFactorialValue_one_lah_falling_expansion (n : Nat) :
    risingNat 1 (Nat.succ n) =
      lahDescendingExpansion 1 (Nat.succ n) := by
  unfold lahDescendingExpansion
  rw [lahDescendingExpansionPrefix_one_succ]
  exact risingFactorialValue_one_eq_lah_first_column n

theorem lahExactClosedDivision_first_column (n : Nat) :
    lahExactClosedDivision (Nat.succ n) 1 (lahNumber (Nat.succ n) 1) := by
  unfold lahExactClosedDivision lahClosedDenominator lahClosedNumerator
  change lahNumber (Nat.succ n) 1 * 1 =
    C n 0 * factorialNat (Nat.succ n)
  rw [Nat.mul_one]
  unfold C
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right]
  rw [Nat.one_mul]
  exact lahNumber_succ_one n

theorem lahStirlingDiagonalSum_self_eq_lahNumber_self (n : Nat) :
    lahStirlingDiagonalSum n n = lahNumber n n := by
  exact BEDC.Derived.LahUp.lahStirlingDiagonalSum_self_eq_lahNumber_self n

theorem LahNumberUp_constructive_export :
    (∀ n k : Nat,
      lahNumber (Nat.succ n) (Nat.succ k) =
        (n + Nat.succ k) * lahNumber n (Nat.succ k) +
          lahNumber n k) ∧
      (∀ n : Nat,
        lahNumber (Nat.succ n) 1 =
          BEDC.Derived.StirlingCycleUp.stirlingCycleRowSum (Nat.succ n)) ∧
      (∀ n : Nat,
        risingNat 1 (Nat.succ n) =
          lahDescendingExpansion 1 (Nat.succ n)) ∧
      (∀ n : Nat,
        lahExactClosedDivision (Nat.succ n) 1 (lahNumber (Nat.succ n) 1)) ∧
      (∀ n : Nat,
        lahStirlingDiagonalSum n n = lahNumber n n) := by
  constructor
  · intro n k
    exact lahNumber_recurrence n k
  · constructor
    · intro n
      exact lahNumber_succ_one_eq_stirlingCycleRowSum n
    · constructor
      · intro n
        exact risingFactorialValue_one_lah_falling_expansion n
      · constructor
        · intro n
          exact lahExactClosedDivision_first_column n
        · intro n
          exact lahStirlingDiagonalSum_self_eq_lahNumber_self n

end BEDC.Derived.LahNumberUp
