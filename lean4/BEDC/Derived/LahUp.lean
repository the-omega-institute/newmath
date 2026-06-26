import BEDC.Derived.FactorialUp
import BEDC.Derived.StirlingFirstUp
import BEDC.Derived.StirlingUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.LahUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.FactorialUp
open BEDC.Derived.StirlingFirstUp (factorialNat stirlingFirst stirlingFirst_self)
open BEDC.Derived.StirlingUp
  (stirlingSecond stirlingSecond_self stirlingSecond_above stirlingSecond_zero_succ)

abbrev UnaryOne : BHist := BHist.e1 BHist.Empty

-- 无符号 Lah 数的闭递归展示。
def lahNumber : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 0
  | Nat.succ n, Nat.succ k =>
      (n + Nat.succ k) * lahNumber n (Nat.succ k) + lahNumber n k

def lahNumberFn (n k : BHist) : BHist :=
  natToUnary (lahNumber (bwordLength n) (bwordLength k))

def lahStirlingDiagonalSum (n : Nat) : Nat -> Nat
  | 0 => stirlingFirst n 0 * stirlingSecond 0 n
  | Nat.succ m =>
      lahStirlingDiagonalSum n m +
        stirlingFirst n (Nat.succ m) * stirlingSecond (Nat.succ m) n

theorem lahNumber_zero_zero :
    lahNumber 0 0 = 1 := by
  rfl

theorem lahNumber_zero_succ (k : Nat) :
    lahNumber 0 (Nat.succ k) = 0 := by
  rfl

theorem lahNumber_succ_zero (n : Nat) :
    lahNumber (Nat.succ n) 0 = 0 := by
  rfl

theorem lahNumber_recurrence (n k : Nat) :
    lahNumber (Nat.succ n) (Nat.succ k) =
      (n + Nat.succ k) * lahNumber n (Nat.succ k) + lahNumber n k := by
  rfl

theorem lahNumber_self_and_above :
    ∀ n : Nat, lahNumber n n = 1 ∧
      ∀ extra : Nat, lahNumber n (Nat.succ (n + extra)) = 0 := by
  intro n
  induction n with
  | zero =>
      constructor
      · rfl
      · intro extra
        rfl
  | succ n ih =>
      constructor
      · change (n + Nat.succ n) * lahNumber n (Nat.succ n) +
          lahNumber n n = 1
        rw [ih.right 0, ih.left]
        rfl
      · intro extra
        change
          (n + Nat.succ (Nat.succ n + extra)) *
              lahNumber n (Nat.succ (Nat.succ n + extra)) +
            lahNumber n (Nat.succ n + extra) = 0
        rw [Nat.succ_add]
        rw [ih.right extra]
        rw [show Nat.succ (Nat.succ (n + extra)) =
            Nat.succ (n + Nat.succ extra) by
          rw [Nat.add_succ]]
        rw [ih.right (Nat.succ extra)]
        rfl

theorem lahNumber_self (n : Nat) :
    lahNumber n n = 1 :=
  (lahNumber_self_and_above n).left

theorem lahNumber_above (n extra : Nat) :
    lahNumber n (Nat.succ (n + extra)) = 0 :=
  (lahNumber_self_and_above n).right extra

theorem lahNumber_succ_one_eq_factorial :
    ∀ n : Nat, lahNumber (Nat.succ n) 1 = factorialNat (Nat.succ n) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [lahNumber_recurrence (Nat.succ n) 0]
      rw [ih]
      rw [Nat.add_comm (Nat.succ n) 1]
      rw [lahNumber_succ_zero]
      rw [Nat.add_zero]
      rw [Nat.one_add]
      rw [Nat.add_comm n 1]
      rw [Nat.one_add]
      rfl

theorem lahStirlingDiagonalSum_zero :
    lahStirlingDiagonalSum 0 0 = 1 := by
  rfl

theorem lahStirlingDiagonalSum_below_zero :
    ∀ n extra : Nat, lahStirlingDiagonalSum (Nat.succ (n + extra)) n = 0 := by
  intro n
  induction n with
  | zero =>
      intro extra
      rw [Nat.zero_add]
      change stirlingFirst (Nat.succ extra) 0 *
        stirlingSecond 0 (Nat.succ extra) = 0
      rw [stirlingSecond_zero_succ]
      exact Nat.mul_zero _
  | succ n ih =>
      intro extra
      rw [Nat.succ_add]
      change lahStirlingDiagonalSum (Nat.succ (Nat.succ (n + extra))) n +
          stirlingFirst (Nat.succ (Nat.succ (n + extra))) (Nat.succ n) *
            stirlingSecond (Nat.succ n) (Nat.succ (Nat.succ (n + extra))) = 0
      have prefixZero := ih (Nat.succ extra)
      rw [Nat.add_succ] at prefixZero
      rw [prefixZero]
      have secondZero :
          stirlingSecond (Nat.succ n)
            (Nat.succ (Nat.succ (n + extra))) = 0 := by
        rw [show Nat.succ (Nat.succ (n + extra)) =
            Nat.succ (Nat.succ n + extra) by
          rw [Nat.succ_add]]
        exact stirlingSecond_above (Nat.succ n) extra
      rw [secondZero]
      rw [Nat.mul_zero]

theorem lahStirlingDiagonalSum_self_one :
    ∀ n : Nat, lahStirlingDiagonalSum n n = 1 := by
  intro n
  cases n with
  | zero =>
      rfl
  | succ n =>
      change lahStirlingDiagonalSum (Nat.succ n) n +
          stirlingFirst (Nat.succ n) (Nat.succ n) *
            stirlingSecond (Nat.succ n) (Nat.succ n) = 1
      rw [stirlingFirst_self, stirlingSecond_self]
      have prefixZero := lahStirlingDiagonalSum_below_zero n 0
      rw [Nat.add_zero] at prefixZero
      rw [prefixZero]

theorem lahStirlingDiagonalSum_self_eq_lahNumber_self (n : Nat) :
    lahStirlingDiagonalSum n n = lahNumber n n := by
  rw [lahStirlingDiagonalSum_self_one n, lahNumber_self n]

theorem lahNumberFn_unary_result (n k : BHist) :
    UnaryHistory (lahNumberFn n k) := by
  unfold lahNumberFn
  exact natToUnary_unary _

theorem lahNumberFn_zero_zero :
    lahNumberFn BHist.Empty BHist.Empty = UnaryOne := by
  rfl

theorem lahNumberFn_recurrence_natToUnary (n k : Nat) :
    lahNumberFn (natToUnary (Nat.succ n)) (natToUnary (Nat.succ k)) =
      natToUnary
        ((n + Nat.succ k) * lahNumber n (Nat.succ k) + lahNumber n k) := by
  unfold lahNumberFn
  rw [natToUnary_length, natToUnary_length]
  rfl

theorem lahNumberFn_self (n : Nat) :
    lahNumberFn (natToUnary n) (natToUnary n) = UnaryOne := by
  unfold lahNumberFn
  rw [natToUnary_length]
  rw [lahNumber_self]
  rfl

theorem LahUp_constructive_export :
    (lahNumber 0 0 = 1) ∧
      (∀ n k : Nat,
        lahNumber (Nat.succ n) (Nat.succ k) =
          (n + Nat.succ k) * lahNumber n (Nat.succ k) + lahNumber n k) ∧
      (∀ n : Nat, lahNumber n n = 1) ∧
      (∀ n : Nat, lahStirlingDiagonalSum n n = lahNumber n n) ∧
      (∀ n k : BHist, UnaryHistory (lahNumberFn n k)) := by
  constructor
  · exact lahNumber_zero_zero
  · constructor
    · intro n k
      exact lahNumber_recurrence n k
    · constructor
      · intro n
        exact lahNumber_self n
      · constructor
        · intro n
          exact lahStirlingDiagonalSum_self_eq_lahNumber_self n
        · intro n k
          exact lahNumberFn_unary_result n k

end BEDC.Derived.LahUp
