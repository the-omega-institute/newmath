import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.HappyNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

def digitSquare (d : Nat) : Nat :=
  d * d

def digitSqSum : List Nat -> Nat
  | [] => 0
  | d :: ds => digitSquare d + digitSqSum ds

def countNat (target : Nat) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      if x = target then countNat target xs + 1 else countNat target xs

def containsNat (target : Nat) (xs : List Nat) : Prop :=
  0 < countNat target xs

def natDigitsFuelLsb : Nat -> Nat -> Nat -> List Nat
  | 0, _base, n => [n]
  | fuel + 1, base, n =>
      if base < 2 then
        [n]
      else if n < base then
        [n]
      else
        n % base :: natDigitsFuelLsb fuel base (n / base)

def natDigitsLsb (base n : Nat) : List Nat :=
  natDigitsFuelLsb (n + 1) base n

def digitSqSumNat (base n : Nat) : Nat :=
  digitSqSum (natDigitsLsb base n)

def happyIterate (base : Nat) : Nat -> Nat -> Nat
  | 0, n => n
  | fuel + 1, n => happyIterate base fuel (digitSqSumNat base n)

def HappyWithin (base fuel n : Nat) : Prop :=
  happyIterate base fuel n = 1

def happyWithinBool (base fuel n : Nat) : Bool :=
  Nat.beq (happyIterate base fuel n) 1

def unhappyCycle : List Nat :=
  [4, 16, 37, 58, 89, 145, 42, 20]

def UnhappyCycleMember (n : Nat) : Prop :=
  containsNat n unhappyCycle

def UnhappyCycleStep (n next : Nat) : Prop :=
  (n = 4 ∧ next = 16) ∨
    (n = 16 ∧ next = 37) ∨
      (n = 37 ∧ next = 58) ∨
        (n = 58 ∧ next = 89) ∨
          (n = 89 ∧ next = 145) ∨
            (n = 145 ∧ next = 42) ∨
              (n = 42 ∧ next = 20) ∨
                (n = 20 ∧ next = 4)

def EntersUnhappyCycleWithin (base fuel n : Nat) : Prop :=
  UnhappyCycleMember (happyIterate base fuel n)

def digitSqSumUp (digits : List Nat) : BHist :=
  natToUnary (digitSqSum digits)

def happyStepUp (base : Nat) (n : BHist) : BHist :=
  natToUnary (digitSqSumNat base (bwordLength n))

def happyIterateUp (base fuel : Nat) (n : BHist) : BHist :=
  natToUnary (happyIterate base fuel (bwordLength n))

theorem digitSqSum_nil :
    digitSqSum [] = 0 := by
  rfl

theorem digitSqSum_cons (d : Nat) (ds : List Nat) :
    digitSqSum (d :: ds) = d * d + digitSqSum ds := by
  rfl

theorem digitSqSum_decimal_23 :
    digitSqSum [3, 2] = 13 := by
  rfl

theorem digitSqSum_decimal_145 :
    digitSqSum [5, 4, 1] = 42 := by
  rfl

theorem digitSqSumUp_unary (digits : List Nat) :
    UnaryHistory (digitSqSumUp digits) := by
  exact natToUnary_unary (digitSqSum digits)

theorem digitSqSumUp_length (digits : List Nat) :
    bwordLength (digitSqSumUp digits) = digitSqSum digits := by
  exact natToUnary_length (digitSqSum digits)

theorem happyStepUp_unary (base : Nat) (n : BHist) :
    UnaryHistory (happyStepUp base n) := by
  exact natToUnary_unary (digitSqSumNat base (bwordLength n))

theorem happyIterateUp_unary (base fuel : Nat) (n : BHist) :
    UnaryHistory (happyIterateUp base fuel n) := by
  exact natToUnary_unary (happyIterate base fuel (bwordLength n))

theorem digitSqSumNat_decimal_four :
    digitSqSumNat 10 4 = 16 := by
  rfl

theorem digitSqSumNat_decimal_sixteen :
    digitSqSumNat 10 16 = 37 := by
  rfl

theorem digitSqSumNat_decimal_thirtySeven :
    digitSqSumNat 10 37 = 58 := by
  rfl

theorem digitSqSumNat_decimal_fiftyEight :
    digitSqSumNat 10 58 = 89 := by
  rfl

theorem digitSqSumNat_decimal_eightyNine :
    digitSqSumNat 10 89 = 145 := by
  rfl

theorem digitSqSumNat_decimal_oneHundredFortyFive :
    digitSqSumNat 10 145 = 42 := by
  rfl

theorem digitSqSumNat_decimal_fortyTwo :
    digitSqSumNat 10 42 = 20 := by
  rfl

theorem digitSqSumNat_decimal_twenty :
    digitSqSumNat 10 20 = 4 := by
  rfl

theorem unhappyCycle_decimal_edges :
    UnhappyCycleStep 4 16 ∧
      UnhappyCycleStep 16 37 ∧
        UnhappyCycleStep 37 58 ∧
          UnhappyCycleStep 58 89 ∧
            UnhappyCycleStep 89 145 ∧
              UnhappyCycleStep 145 42 ∧
                UnhappyCycleStep 42 20 ∧
                  UnhappyCycleStep 20 4 := by
  exact ⟨Or.inl ⟨rfl, rfl⟩,
    ⟨Or.inr (Or.inl ⟨rfl, rfl⟩),
      ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))),
            ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))),
              ⟨Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl ⟨rfl, rfl⟩)))))),
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr ⟨rfl, rfl⟩))))))⟩⟩⟩⟩⟩⟩⟩

theorem unhappyCycle_decimal_step_values :
    digitSqSumNat 10 4 = 16 ∧
      digitSqSumNat 10 16 = 37 ∧
        digitSqSumNat 10 37 = 58 ∧
          digitSqSumNat 10 58 = 89 ∧
            digitSqSumNat 10 89 = 145 ∧
              digitSqSumNat 10 145 = 42 ∧
                digitSqSumNat 10 42 = 20 ∧
                  digitSqSumNat 10 20 = 4 := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩

theorem unhappyCycle_count_four :
    countNat 4 unhappyCycle = 1 := by
  rfl

theorem unhappyCycle_nodup :
    unhappyCycle.Nodup := by
  decide

theorem unhappyCycle_count_members :
    countNat 4 unhappyCycle = 1 ∧
      countNat 16 unhappyCycle = 1 ∧
        countNat 37 unhappyCycle = 1 ∧
          countNat 58 unhappyCycle = 1 ∧
            countNat 89 unhappyCycle = 1 ∧
              countNat 145 unhappyCycle = 1 ∧
                countNat 42 unhappyCycle = 1 ∧
                  countNat 20 unhappyCycle = 1 := by
  exact ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩

theorem unhappyCycle_count_sixteen :
    countNat 16 unhappyCycle = 1 := by
  rfl

theorem unhappyCycle_count_one :
    countNat 1 unhappyCycle = 0 := by
  rfl

theorem unhappy_from_four_returns_four :
    happyIterate 10 8 4 = 4 := by
  rfl

theorem four_enters_unhappy_cycle :
    EntersUnhappyCycleWithin 10 0 4 := by
  exact Nat.zero_lt_succ 0

theorem happy_one :
    HappyWithin 10 0 1 := by
  rfl

theorem happy_seven :
    HappyWithin 10 5 7 := by
  rfl

theorem happy_ten :
    HappyWithin 10 1 10 := by
  rfl

theorem happy_thirteen :
    HappyWithin 10 2 13 := by
  rfl

theorem happy_nineteen :
    HappyWithin 10 4 19 := by
  rfl

theorem happy_twentyThree :
    HappyWithin 10 3 23 := by
  rfl

theorem happyWithinBool_true_iff (base fuel n : Nat) :
    happyWithinBool base fuel n = true ↔ HappyWithin base fuel n := by
  constructor
  · intro h
    unfold happyWithinBool at h
    unfold HappyWithin
    exact Nat.eq_of_beq_eq_true h
  · intro h
    unfold happyWithinBool
    unfold HappyWithin at h
    rw [h]
    rfl

theorem happyWithinBool_one :
    happyWithinBool 10 0 1 = true := by
  rfl

theorem happyWithinBool_seven :
    happyWithinBool 10 5 7 = true := by
  rfl

theorem happyWithinBool_ten :
    happyWithinBool 10 1 10 = true := by
  rfl

theorem happyWithinBool_thirteen :
    happyWithinBool 10 2 13 = true := by
  rfl

theorem happyWithinBool_nineteen :
    happyWithinBool 10 4 19 = true := by
  rfl

theorem happyWithinBool_twentyThree :
    happyWithinBool 10 3 23 = true := by
  rfl

theorem happyStepUp_decimal_ten :
    happyStepUp 10 (natToUnary 10) = natToUnary 1 := by
  rfl

theorem happyIterateUp_decimal_twentyThree :
    happyIterateUp 10 3 (natToUnary 23) = natToUnary 1 := by
  rfl

end BEDC.Derived.HappyNumberUp
