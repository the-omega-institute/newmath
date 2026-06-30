import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.PrimeUp.NatMulTransport

namespace BEDC.Derived.HarshadNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

-- 十进制数字按低位到高位排列, 例如 10 记为 [0, 1]。
def digitSum (base : Nat) : List Nat -> Nat
  | [] => 0
  | digit :: rest => digit + digitSum base rest

def digitEval (base : Nat) : List Nat -> Nat
  | [] => 0
  | digit :: rest => digit + base * digitEval base rest

inductive DigitsInBase (base : Nat) : List Nat -> Prop where
  | nil : DigitsInBase base []
  | cons {digit : Nat} {rest : List Nat} :
      digit < base -> DigitsInBase base rest -> DigitsInBase base (digit :: rest)

def dividesNat (divisor value : Nat) : Prop :=
  ∃ factor : Nat, value = divisor * factor

def decimalBase : Nat := 10

def HarshadDigits (digits : List Nat) (value : Nat) : Prop :=
  DigitsInBase decimalBase digits ∧
    digitEval decimalBase digits = value ∧
      0 < digitSum decimalBase digits ∧
        dividesNat (digitSum decimalBase digits) value

def HarshadNumber (value : Nat) : Prop :=
  ∃ digits : List Nat, HarshadDigits digits value

abbrev Harshad := HarshadNumber

inductive AllHarshad : List Nat -> Prop where
  | nil : AllHarshad []
  | cons {value : Nat} {rest : List Nat} :
      HarshadNumber value -> AllHarshad rest -> AllHarshad (value :: rest)

inductive ConsecutiveNatList : List Nat -> Prop where
  | nil : ConsecutiveNatList []
  | singleton (value : Nat) : ConsecutiveNatList [value]
  | step {first second : Nat} {rest : List Nat} :
      second = first + 1 ->
        ConsecutiveNatList (second :: rest) ->
          ConsecutiveNatList (first :: second :: rest)

def oneToTenDigits : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem digitSum_nil (base : Nat) :
    digitSum base [] = 0 := by
  rfl

theorem digitEval_nil (base : Nat) :
    digitEval base [] = 0 := by
  rfl

theorem digitSum_cons (base digit : Nat) (rest : List Nat) :
    digitSum base (digit :: rest) = digit + digitSum base rest := by
  rfl

theorem digitEval_cons (base digit : Nat) (rest : List Nat) :
    digitEval base (digit :: rest) = digit + base * digitEval base rest := by
  rfl

theorem digitSum_singleton (base digit : Nat) :
    digitSum base [digit] = digit := by
  rfl

theorem digitEval_singleton (base digit : Nat) :
    digitEval base [digit] = digit := by
  rfl

theorem digitSum_decimal_ten_digits :
    digitSum decimalBase [0, 1] = 1 := by
  rfl

theorem digitEval_decimal_ten_digits :
    digitEval decimalBase [0, 1] = 10 := by
  rfl

private theorem natToUnary_hsame_of_length {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro hUnary kUnary lengthEq
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

theorem natToUnary_mul_rel (a b : Nat) :
    NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) := by
  have total := NatMul_total (natToUnary_unary a) (natToUnary_unary b)
  cases total with
  | intro result resultData =>
      have sameResult : hsame result (natToUnary (a * b)) :=
        natToUnary_hsame_of_length resultData.left (natToUnary_unary _)
          (calc
            bwordLength result =
                bwordLength (natToUnary a) * bwordLength (natToUnary b) :=
              NatMul_bwordLength resultData.right
            _ = a * b := by
              exact
                (congrArg (fun x => x * bwordLength (natToUnary b))
                    (natToUnary_length a)).trans
                  (congrArg (fun x => a * x) (natToUnary_length b))
            _ = bwordLength (natToUnary (a * b)) :=
              (natToUnary_length (a * b)).symm)
      exact (NatMul_result_hsame_transport resultData.right sameResult).right

theorem dividesNat_to_natDivides {divisor value : Nat} :
    dividesNat divisor value ->
      NatDivides (natToUnary divisor) (natToUnary value) := by
  intro divides
  cases divides with
  | intro factor factorData =>
      exact ⟨natToUnary factor, natToUnary_unary factor, by
        cases factorData
        exact natToUnary_mul_rel divisor factor⟩

theorem harshad_unary_divides_digit_sum {value : Nat} :
    HarshadNumber value ->
      ∃ digits : List Nat,
        DigitsInBase decimalBase digits ∧
          digitEval decimalBase digits = value ∧
            0 < digitSum decimalBase digits ∧
              NatDivides (natToUnary (digitSum decimalBase digits))
                (natToUnary value) := by
  intro h
  cases h with
  | intro digits data =>
      exact ⟨digits, data.left, data.right.left, data.right.right.left,
        dividesNat_to_natDivides data.right.right.right⟩

theorem harshad_one : HarshadNumber 1 := by
  exact ⟨[1],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 0,
    ⟨1, rfl⟩⟩

theorem harshad_two : HarshadNumber 2 := by
  exact ⟨[2],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 1,
    ⟨1, rfl⟩⟩

theorem harshad_three : HarshadNumber 3 := by
  exact ⟨[3],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 2,
    ⟨1, rfl⟩⟩

theorem harshad_four : HarshadNumber 4 := by
  exact ⟨[4],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 3,
    ⟨1, rfl⟩⟩

theorem harshad_five : HarshadNumber 5 := by
  exact ⟨[5],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 4,
    ⟨1, rfl⟩⟩

theorem harshad_six : HarshadNumber 6 := by
  exact ⟨[6],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 5,
    ⟨1, rfl⟩⟩

theorem harshad_seven : HarshadNumber 7 := by
  exact ⟨[7],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 6,
    ⟨1, rfl⟩⟩

theorem harshad_eight : HarshadNumber 8 := by
  exact ⟨[8],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 7,
    ⟨1, rfl⟩⟩

theorem harshad_nine : HarshadNumber 9 := by
  exact ⟨[9],
    DigitsInBase.cons (by decide) DigitsInBase.nil,
    rfl,
    Nat.zero_lt_succ 8,
    ⟨1, rfl⟩⟩

theorem harshad_ten : HarshadNumber 10 := by
  exact ⟨[0, 1],
    DigitsInBase.cons (by decide)
      (DigitsInBase.cons (by decide) DigitsInBase.nil),
    rfl,
    Nat.zero_lt_succ 0,
    ⟨10, rfl⟩⟩

theorem harshad_twelve : HarshadNumber 12 := by
  exact ⟨[2, 1],
    DigitsInBase.cons (by decide)
      (DigitsInBase.cons (by decide) DigitsInBase.nil),
    rfl,
    Nat.zero_lt_succ 2,
    ⟨4, rfl⟩⟩

theorem harshad_eighteen : HarshadNumber 18 := by
  exact ⟨[8, 1],
    DigitsInBase.cons (by decide)
      (DigitsInBase.cons (by decide) DigitsInBase.nil),
    rfl,
    Nat.zero_lt_succ 8,
    ⟨2, rfl⟩⟩

theorem one_to_ten_all_harshad :
    AllHarshad oneToTenDigits := by
  unfold oneToTenDigits
  exact AllHarshad.cons harshad_one
    (AllHarshad.cons harshad_two
      (AllHarshad.cons harshad_three
        (AllHarshad.cons harshad_four
          (AllHarshad.cons harshad_five
            (AllHarshad.cons harshad_six
              (AllHarshad.cons harshad_seven
                (AllHarshad.cons harshad_eight
                  (AllHarshad.cons harshad_nine
                    (AllHarshad.cons harshad_ten AllHarshad.nil)))))))))

theorem one_to_ten_consecutive :
    ConsecutiveNatList oneToTenDigits := by
  unfold oneToTenDigits
  exact ConsecutiveNatList.step rfl
    (ConsecutiveNatList.step rfl
      (ConsecutiveNatList.step rfl
        (ConsecutiveNatList.step rfl
          (ConsecutiveNatList.step rfl
            (ConsecutiveNatList.step rfl
              (ConsecutiveNatList.step rfl
                (ConsecutiveNatList.step rfl
                  (ConsecutiveNatList.step rfl
                    (ConsecutiveNatList.singleton 10)))))))))

theorem one_to_ten_consecutive_harshad :
    ConsecutiveNatList oneToTenDigits ∧ AllHarshad oneToTenDigits := by
  exact ⟨one_to_ten_consecutive, one_to_ten_all_harshad⟩

end BEDC.Derived.HarshadNumberUp
