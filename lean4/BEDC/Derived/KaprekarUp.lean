import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.NatUp
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.KaprekarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

/-!
Kaprekar 算术使用有限 `List Nat` 数字表表示。数字按低位在前存放,
与仓库中已有的局部基数展开约定一致。
-/

def digitsInBaseBool (base : Nat) : List Nat -> Bool
  | [] => true
  | d :: ds => (decide (d < base)) && digitsInBaseBool base ds

def DigitsInBase (base : Nat) (digits : List Nat) : Prop :=
  digitsInBaseBool base digits = true

instance digitsInBaseDecidable (base : Nat) (digits : List Nat) :
    Decidable (DigitsInBase base digits) :=
  inferInstanceAs (Decidable (digitsInBaseBool base digits = true))

def digitValue (base : Nat) : List Nat -> Nat
  | [] => 0
  | d :: ds => d + base * digitValue base ds

def digitSum : List Nat -> Nat
  | [] => 0
  | d :: ds => d + digitSum ds

def KaprekarSplit
    (base n : Nat) (squareDigits lowDigits highDigits : List Nat) : Prop :=
  DigitsInBase base squareDigits ∧
    DigitsInBase base lowDigits ∧
      DigitsInBase base highDigits ∧
        squareDigits = lowDigits ++ highDigits ∧
          digitValue base squareDigits = n * n ∧
            digitValue base lowDigits + digitValue base highDigits = n

def KaprekarNumber (base n : Nat) : Prop :=
  ∃ squareDigits : List Nat, ∃ lowDigits : List Nat, ∃ highDigits : List Nat,
    KaprekarSplit base n squareDigits lowDigits highDigits

instance kaprekarSplitDecidable
    (base n : Nat) (squareDigits lowDigits highDigits : List Nat) :
    Decidable (KaprekarSplit base n squareDigits lowDigits highDigits) :=
  inferInstanceAs
    (Decidable
      (DigitsInBase base squareDigits ∧
        DigitsInBase base lowDigits ∧
          DigitsInBase base highDigits ∧
            squareDigits = lowDigits ++ highDigits ∧
              digitValue base squareDigits = n * n ∧
                digitValue base lowDigits + digitValue base highDigits = n))

def insertAscending (x : Nat) : List Nat -> List Nat
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertAscending x ys

def sortAscending : List Nat -> List Nat
  | [] => []
  | x :: xs => insertAscending x (sortAscending xs)

def insertDescending (x : Nat) : List Nat -> List Nat
  | [] => [x]
  | y :: ys =>
      if y <= x then
        x :: y :: ys
      else
        y :: insertDescending x ys

def sortDescending : List Nat -> List Nat
  | [] => []
  | x :: xs => insertDescending x (sortDescending xs)

-- 低位在前时, 升序数字表读回为通常 Kaprekar 步骤中的降序数。
def kaprekarStepDigits (base : Nat) (digits : List Nat) : Nat :=
  digitValue base (sortAscending digits) - digitValue base (sortDescending digits)

def kaprekarStepUnary (base : Nat) (digits : List Nat) : BHist :=
  natToUnary (kaprekarStepDigits base digits)

def digitsOf6174 : List Nat :=
  [4, 7, 1, 6]

def FourDigitKaprekarFixed (n : Nat) (digits : List Nat) : Prop :=
  DigitsInBase 10 digits ∧
    digits.length = 4 ∧
      digitValue 10 digits = n ∧ kaprekarStepDigits 10 digits = n

instance fourDigitKaprekarFixedDecidable (n : Nat) (digits : List Nat) :
    Decidable (FourDigitKaprekarFixed n digits) :=
  inferInstanceAs
    (Decidable
      (DigitsInBase 10 digits ∧
        digits.length = 4 ∧
          digitValue 10 digits = n ∧ kaprekarStepDigits 10 digits = n))

theorem digitValue_digitsOf6174 :
    digitValue 10 digitsOf6174 = 6174 := by
  rfl

theorem digitSum_digitsOf6174 :
    digitSum digitsOf6174 = 18 := by
  rfl

theorem sortAscending_digitsOf6174 :
    sortAscending digitsOf6174 = [1, 4, 6, 7] := by
  decide

theorem sortDescending_digitsOf6174 :
    sortDescending digitsOf6174 = [7, 6, 4, 1] := by
  decide

theorem kaprekar_6174_step :
    kaprekarStepDigits 10 digitsOf6174 = 6174 := by
  decide

theorem kaprekar_6174_four_digit_fixed :
    FourDigitKaprekarFixed 6174 digitsOf6174 := by
  decide

theorem kaprekarStepUnary_unary (base : Nat) (digits : List Nat) :
    UnaryHistory (kaprekarStepUnary base digits) := by
  unfold kaprekarStepUnary
  exact natToUnary_unary (kaprekarStepDigits base digits)

theorem kaprekar_6174_unary_fixed :
    kaprekarStepUnary 10 digitsOf6174 = natToUnary 6174 := by
  unfold kaprekarStepUnary
  rw [kaprekar_6174_step]

theorem kaprekar_45_decimal :
    KaprekarNumber 10 45 := by
  exact ⟨[5, 2, 0, 2], [5, 2], [0, 2], by decide⟩

private theorem unary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        unary_hsame_of_length resultData.left (natToUnary_unary _)
          ((NatMul_bwordLength resultData.right).trans (by
            rw [natToUnary_length, natToUnary_length, natToUnary_length]))
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

private theorem natToUnary_append (m n : Nat) :
    append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

theorem natToUnary_add_rel (a b : Nat) :
    NatAdd (natToUnary a) (natToUnary b) (natToUnary (a + b)) := by
  exact ⟨natToUnary_unary a, natToUnary_unary b,
    cont_intro (natToUnary_append a b).symm⟩

theorem kaprekar_45_square_unary :
    NatMul (natToUnary 45) (natToUnary 45) (natToUnary 2025) := by
  exact natToUnary_mul_rel 45 45

theorem kaprekar_45_split_add_unary :
    NatAdd (natToUnary 25) (natToUnary 20) (natToUnary 45) := by
  exact natToUnary_add_rel 25 20

theorem kaprekar_small_decimal_values :
    KaprekarNumber 10 1 ∧
      KaprekarNumber 10 9 ∧
        KaprekarNumber 10 45 ∧
          KaprekarNumber 10 55 ∧ KaprekarNumber 10 99 := by
  constructor
  · exact ⟨[1], [1], [], by decide⟩
  · constructor
    · exact ⟨[1, 8], [1], [8], by decide⟩
    · constructor
      · exact kaprekar_45_decimal
      · constructor
        · exact ⟨[5, 2, 0, 3], [5, 2], [0, 3], by decide⟩
        · exact ⟨[1, 0, 8, 9], [1, 0], [8, 9], by decide⟩

end BEDC.Derived.KaprekarUp
