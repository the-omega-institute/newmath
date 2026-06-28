import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.NarcissisticNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

def natPow : Nat -> Nat -> Nat
  | _base, 0 => 1
  | base, Nat.succ exponent => base * natPow base exponent

def digitsBelow (base : Nat) : List Nat -> Bool
  | [] => true
  | d :: rest => if d < base then digitsBelow base rest else false

def nonzeroHead : List Nat -> Prop
  | [] => False
  | d :: _rest => 0 < d

def evalDigits (base : Nat) : List Nat -> Nat
  | [] => 0
  | d :: rest => d * natPow base rest.length + evalDigits base rest

def digitPowSum (digits : List Nat) (exponent : Nat) : Nat :=
  match digits with
  | [] => 0
  | d :: rest => natPow d exponent + digitPowSum rest exponent

def narcissisticDigits (digits : List Nat) : Prop :=
  digitsBelow 10 digits = true ∧ nonzeroHead digits ∧
    evalDigits 10 digits = digitPowSum digits digits.length

def narcissistic (n : Nat) : Prop :=
  ∃ digits : List Nat, narcissisticDigits digits ∧ evalDigits 10 digits = n

def digitPowSumUnary (digits : List Nat) (exponent : Nat) : BHist :=
  natToUnary (digitPowSum digits exponent)

def narcissisticUnary (n : BHist) : Prop :=
  ∃ k : Nat, n = natToUnary k ∧ narcissistic k

theorem natPow_zero (base : Nat) :
    natPow base 0 = 1 := by
  rfl

theorem natPow_succ (base exponent : Nat) :
    natPow base (Nat.succ exponent) = base * natPow base exponent := by
  rfl

theorem natPow_mono_left {a b exponent : Nat} :
    a <= b -> natPow a exponent <= natPow b exponent := by
  intro leAB
  induction exponent with
  | zero =>
      exact Nat.le_refl 1
  | succ exponent ih =>
      change a * natPow a exponent <= b * natPow b exponent
      exact Nat.mul_le_mul leAB ih

theorem digitPowSum_nil (exponent : Nat) :
    digitPowSum [] exponent = 0 := by
  rfl

theorem digitPowSum_cons (d exponent : Nat) (rest : List Nat) :
    digitPowSum (d :: rest) exponent =
      natPow d exponent + digitPowSum rest exponent := by
  rfl

theorem digitPowSum_unary (digits : List Nat) (exponent : Nat) :
    UnaryHistory (digitPowSumUnary digits exponent) := by
  unfold digitPowSumUnary
  exact natToUnary_unary (digitPowSum digits exponent)

theorem digitPowSum_bound_by_repeated_max
    (digits : List Nat) (exponent maxDigit : Nat) :
    digitsBelow (Nat.succ maxDigit) digits = true ->
      digitPowSum digits exponent <= digits.length * natPow maxDigit exponent := by
  intro below
  induction digits with
  | nil =>
      exact Nat.zero_le (0 * natPow maxDigit exponent)
  | cons d rest ih =>
      unfold digitsBelow at below
      by_cases dBelow : d < Nat.succ maxDigit
      · rw [if_pos dBelow] at below
        have dLe : d <= maxDigit := Nat.le_of_lt_succ dBelow
        have powLe : natPow d exponent <= natPow maxDigit exponent :=
          natPow_mono_left dLe
        have tailLe :
            digitPowSum rest exponent <= rest.length * natPow maxDigit exponent :=
          ih below
        calc
          digitPowSum (d :: rest) exponent
              <= natPow maxDigit exponent + rest.length * natPow maxDigit exponent :=
            Nat.add_le_add powLe tailLe
          _ = (d :: rest).length * natPow maxDigit exponent := by
            change natPow maxDigit exponent + rest.length * natPow maxDigit exponent =
              Nat.succ rest.length * natPow maxDigit exponent
            rw [Nat.succ_mul, Nat.add_comm]
      · rw [if_neg dBelow] at below
        cases below

theorem decimal_digitPowSum_bound (digits : List Nat) (exponent : Nat) :
    digitsBelow 10 digits = true ->
      digitPowSum digits exponent <= digits.length * natPow 9 exponent := by
  intro below
  exact digitPowSum_bound_by_repeated_max digits exponent 9 below

theorem evalDigits_head_lower_bound (d : Nat) (rest : List Nat) :
    0 < d -> natPow 10 rest.length <= evalDigits 10 (d :: rest) := by
  intro pos
  have oneLe : 1 <= d := pos
  calc
    natPow 10 rest.length = 1 * natPow 10 rest.length := by
      rw [Nat.one_mul]
    _ <= d * natPow 10 rest.length := Nat.mul_le_mul_right (natPow 10 rest.length) oneLe
    _ <= d * natPow 10 rest.length + evalDigits 10 rest := Nat.le.intro rfl

theorem narcissisticDigits_decimal_length_bound (d : Nat) (rest : List Nat) :
    narcissisticDigits (d :: rest) ->
      natPow 10 rest.length <=
        (d :: rest).length * natPow 9 (d :: rest).length := by
  intro nar
  have lower : natPow 10 rest.length <= evalDigits 10 (d :: rest) :=
    evalDigits_head_lower_bound d rest nar.right.left
  have upper :
      digitPowSum (d :: rest) (d :: rest).length <=
        (d :: rest).length * natPow 9 (d :: rest).length :=
    decimal_digitPowSum_bound (d :: rest) (d :: rest).length nar.left
  calc
    natPow 10 rest.length <= evalDigits 10 (d :: rest) := lower
    _ = digitPowSum (d :: rest) (d :: rest).length := nar.right.right
    _ <= (d :: rest).length * natPow 9 (d :: rest).length := upper

theorem narcissisticDigits_length_obstruction (d : Nat) (rest : List Nat) :
    narcissisticDigits (d :: rest) ->
      (natPow 10 rest.length <=
          (d :: rest).length * natPow 9 (d :: rest).length -> False) ->
        False := by
  intro nar impossible
  exact impossible (narcissisticDigits_decimal_length_bound d rest nar)

private theorem decimal_length_sixty_one_bound_absurd :
    natPow 10 60 <= 61 * natPow 9 61 -> False := by
  intro bound
  have impossible : (natPow 10 60 <= 61 * natPow 9 61) -> False := by
    decide
  exact impossible bound

theorem no_decimal_narcissisticDigits_length_sixty_one (digits : List Nat) :
    digits.length = 61 -> narcissisticDigits digits -> False := by
  intro lengthEq nar
  cases digits with
  | nil =>
      cases lengthEq
  | cons d rest =>
      have restLength : rest.length = 60 := Nat.succ.inj lengthEq
      have obstruction := narcissisticDigits_decimal_length_bound d rest nar
      rw [restLength, lengthEq] at obstruction
      change natPow 10 60 <= 61 * natPow 9 61 at obstruction
      exact decimal_length_sixty_one_bound_absurd obstruction

theorem narcissisticUnary_unary {n : BHist} :
    narcissisticUnary n -> UnaryHistory n := by
  intro nar
  cases nar with
  | intro k data =>
      cases data.left
      exact natToUnary_unary k

theorem narcissisticUnary_length {n : BHist} :
    narcissisticUnary n ->
      ∃ k : Nat, bwordLength n = k ∧ narcissistic k := by
  intro nar
  cases nar with
  | intro k data =>
      cases data.left
      exact ⟨k, natToUnary_length k, data.right⟩

private theorem narcissistic_of_digits (digits : List Nat) (n : Nat) :
    narcissisticDigits digits -> evalDigits 10 digits = n -> narcissistic n := by
  intro digitsOk value
  exact ⟨digits, digitsOk, value⟩

private theorem one_digit_narcissisticDigits (d : Nat) :
    0 < d -> d < 10 -> narcissisticDigits [d] := by
  intro dPos dLtTen
  unfold narcissisticDigits digitsBelow nonzeroHead evalDigits digitPowSum natPow
  rw [if_pos dLtTen]
  exact ⟨rfl, dPos, rfl⟩

theorem narcissistic_one : narcissistic 1 := by
  exact narcissistic_of_digits [1] 1 (one_digit_narcissisticDigits 1 (by decide) (by decide)) rfl

theorem narcissistic_two : narcissistic 2 := by
  exact narcissistic_of_digits [2] 2 (one_digit_narcissisticDigits 2 (by decide) (by decide)) rfl

theorem narcissistic_three : narcissistic 3 := by
  exact narcissistic_of_digits [3] 3 (one_digit_narcissisticDigits 3 (by decide) (by decide)) rfl

theorem narcissistic_four : narcissistic 4 := by
  exact narcissistic_of_digits [4] 4 (one_digit_narcissisticDigits 4 (by decide) (by decide)) rfl

theorem narcissistic_five : narcissistic 5 := by
  exact narcissistic_of_digits [5] 5 (one_digit_narcissisticDigits 5 (by decide) (by decide)) rfl

theorem narcissistic_six : narcissistic 6 := by
  exact narcissistic_of_digits [6] 6 (one_digit_narcissisticDigits 6 (by decide) (by decide)) rfl

theorem narcissistic_seven : narcissistic 7 := by
  exact narcissistic_of_digits [7] 7 (one_digit_narcissisticDigits 7 (by decide) (by decide)) rfl

theorem narcissistic_eight : narcissistic 8 := by
  exact narcissistic_of_digits [8] 8 (one_digit_narcissisticDigits 8 (by decide) (by decide)) rfl

theorem narcissistic_nine : narcissistic 9 := by
  exact narcissistic_of_digits [9] 9 (one_digit_narcissisticDigits 9 (by decide) (by decide)) rfl

theorem one_to_nine_narcissistic :
    narcissistic 1 ∧ narcissistic 2 ∧ narcissistic 3 ∧
      narcissistic 4 ∧ narcissistic 5 ∧ narcissistic 6 ∧
        narcissistic 7 ∧ narcissistic 8 ∧ narcissistic 9 := by
  exact ⟨narcissistic_one, narcissistic_two, narcissistic_three,
    narcissistic_four, narcissistic_five, narcissistic_six,
    narcissistic_seven, narcissistic_eight, narcissistic_nine⟩

theorem digitPowSum_153 :
    digitPowSum [1, 5, 3] 3 = 153 := by
  rfl

theorem narcissisticDigits_153 :
    narcissisticDigits [1, 5, 3] := by
  unfold narcissisticDigits digitsBelow nonzeroHead evalDigits digitPowSum natPow
  exact ⟨rfl, by decide, rfl⟩

theorem narcissistic_153 : narcissistic 153 := by
  exact narcissistic_of_digits [1, 5, 3] 153 narcissisticDigits_153 rfl

theorem digitPowSum_370 :
    digitPowSum [3, 7, 0] 3 = 370 := by
  rfl

theorem narcissisticDigits_370 :
    narcissisticDigits [3, 7, 0] := by
  unfold narcissisticDigits digitsBelow nonzeroHead evalDigits digitPowSum natPow
  exact ⟨rfl, by decide, rfl⟩

theorem narcissistic_370 : narcissistic 370 := by
  exact narcissistic_of_digits [3, 7, 0] 370 narcissisticDigits_370 rfl

theorem digitPowSum_371 :
    digitPowSum [3, 7, 1] 3 = 371 := by
  rfl

theorem narcissisticDigits_371 :
    narcissisticDigits [3, 7, 1] := by
  unfold narcissisticDigits digitsBelow nonzeroHead evalDigits digitPowSum natPow
  exact ⟨rfl, by decide, rfl⟩

theorem narcissistic_371 : narcissistic 371 := by
  exact narcissistic_of_digits [3, 7, 1] 371 narcissisticDigits_371 rfl

theorem digitPowSum_407 :
    digitPowSum [4, 0, 7] 3 = 407 := by
  rfl

theorem narcissisticDigits_407 :
    narcissisticDigits [4, 0, 7] := by
  unfold narcissisticDigits digitsBelow nonzeroHead evalDigits digitPowSum natPow
  exact ⟨rfl, by decide, rfl⟩

theorem narcissistic_407 : narcissistic 407 := by
  exact narcissistic_of_digits [4, 0, 7] 407 narcissisticDigits_407 rfl

def verifiedNarcissisticDecimalList : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 153, 370, 371, 407]

theorem verifiedNarcissisticDecimalList_counts :
    List.Nodup verifiedNarcissisticDecimalList ∧
      List.count 1 verifiedNarcissisticDecimalList = 1 ∧
      List.count 2 verifiedNarcissisticDecimalList = 1 ∧
      List.count 3 verifiedNarcissisticDecimalList = 1 ∧
      List.count 4 verifiedNarcissisticDecimalList = 1 ∧
      List.count 5 verifiedNarcissisticDecimalList = 1 ∧
      List.count 6 verifiedNarcissisticDecimalList = 1 ∧
      List.count 7 verifiedNarcissisticDecimalList = 1 ∧
      List.count 8 verifiedNarcissisticDecimalList = 1 ∧
      List.count 9 verifiedNarcissisticDecimalList = 1 ∧
      List.count 153 verifiedNarcissisticDecimalList = 1 ∧
      List.count 370 verifiedNarcissisticDecimalList = 1 ∧
      List.count 371 verifiedNarcissisticDecimalList = 1 ∧
      List.count 407 verifiedNarcissisticDecimalList = 1 := by
  unfold verifiedNarcissisticDecimalList
  decide

theorem verifiedNarcissisticDecimalList_witnesses :
    narcissistic 1 ∧ narcissistic 2 ∧ narcissistic 3 ∧
      narcissistic 4 ∧ narcissistic 5 ∧ narcissistic 6 ∧
        narcissistic 7 ∧ narcissistic 8 ∧ narcissistic 9 ∧
          narcissistic 153 ∧ narcissistic 370 ∧ narcissistic 371 ∧
            narcissistic 407 := by
  exact ⟨narcissistic_one, narcissistic_two, narcissistic_three,
    narcissistic_four, narcissistic_five, narcissistic_six,
    narcissistic_seven, narcissistic_eight, narcissistic_nine,
    narcissistic_153, narcissistic_370, narcissistic_371, narcissistic_407⟩

theorem narcissisticUnary_153 :
    narcissisticUnary (natToUnary 153) := by
  exact ⟨153, rfl, narcissistic_153⟩

theorem narcissisticUnary_370 :
    narcissisticUnary (natToUnary 370) := by
  exact ⟨370, rfl, narcissistic_370⟩

theorem narcissisticUnary_371 :
    narcissisticUnary (natToUnary 371) := by
  exact ⟨371, rfl, narcissistic_371⟩

theorem narcissisticUnary_407 :
    narcissisticUnary (natToUnary 407) := by
  exact ⟨407, rfl, narcissistic_407⟩

end BEDC.Derived.NarcissisticNumberUp
