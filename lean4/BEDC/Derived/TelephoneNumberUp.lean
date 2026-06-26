import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.DerangementUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.PadicUp
import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.PochhammerUp

set_option maxRecDepth 10000

namespace BEDC.Derived.TelephoneNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp

abbrev factorialCount (n : Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natFactorialCount n

abbrev binomialCount (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev derangementNumber (n : Nat) : Nat :=
  BEDC.Derived.DerangementUp.derangementNumber n

def telephoneNumber : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => telephoneNumber (n + 1) + (n + 1) * telephoneNumber n

def twoPow : Nat -> Nat
  | 0 => 1
  | Nat.succ k => 2 * twoPow k

def pairRemainder : Nat -> Nat -> Option Nat
  | n, 0 => some n
  | 0, Nat.succ _ => none
  | 1, Nat.succ _ => none
  | Nat.succ (Nat.succ n), Nat.succ k => pairRemainder n k

def rangeFuel : Nat -> List Nat
  | 0 => [0]
  | Nat.succ fuel => rangeFuel fuel ++ [Nat.succ fuel]

def natListSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + natListSum xs

def telephoneFormulaTermNumerator (n _k : Nat) : Nat :=
  factorialCount n

def telephoneFormulaTermDenominator (n k : Nat) : Nat :=
  match pairRemainder n k with
  | none => 1
  | some remainder => twoPow k * factorialCount k * factorialCount remainder

def telephoneFormulaTerm (n k : Nat) : Nat :=
  match pairRemainder n k with
  | none => 0
  | some remainder =>
      factorialCount n / (twoPow k * factorialCount k * factorialCount remainder)

def telephoneFormulaWithFuel (n fuel : Nat) : Nat :=
  natListSum (List.map (telephoneFormulaTerm n) (rangeFuel fuel))

def telephoneFormulaNumber (n : Nat) : Nat :=
  telephoneFormulaWithFuel n n

def telephoneFormulaTermNumeratorUp (n k : Nat) : BHist :=
  natToUnary (telephoneFormulaTermNumerator n k)

def telephoneFormulaTermDenominatorUp (n k : Nat) : BHist :=
  natToUnary (telephoneFormulaTermDenominator n k)

def telephoneFormulaTermQuotientUp (n k : Nat) : BHist :=
  natToUnary (telephoneFormulaTerm n k)

def telephoneNumberFn (n : BHist) : BHist :=
  natToUnary (telephoneNumber (bwordLength n))

def telephoneFormulaNumberFn (n : BHist) : BHist :=
  natToUnary (telephoneFormulaNumber (bwordLength n))

theorem telephoneNumber_zero :
    telephoneNumber 0 = 1 := by
  rfl

theorem telephoneNumber_one :
    telephoneNumber 1 = 1 := by
  rfl

theorem telephoneNumber_two :
    telephoneNumber 2 = 2 := by
  rfl

theorem telephoneNumber_three :
    telephoneNumber 3 = 4 := by
  rfl

theorem telephoneNumber_four :
    telephoneNumber 4 = 10 := by
  rfl

theorem telephoneNumber_five :
    telephoneNumber 5 = 26 := by
  rfl

theorem telephoneNumber_six :
    telephoneNumber 6 = 76 := by
  rfl

theorem telephoneNumber_recurrence (n : Nat) :
    telephoneNumber (n + 2) =
      telephoneNumber (n + 1) + (n + 1) * telephoneNumber n := by
  rfl

theorem telephoneNumber_succ_succ_recurrence (n : Nat) :
    telephoneNumber (Nat.succ (Nat.succ n)) =
      telephoneNumber (Nat.succ n) + Nat.succ n * telephoneNumber n := by
  rfl

theorem twoPow_zero :
    twoPow 0 = 1 := by
  rfl

theorem twoPow_succ (k : Nat) :
    twoPow (Nat.succ k) = 2 * twoPow k := by
  rfl

theorem pairRemainder_zero_right (n : Nat) :
    pairRemainder n 0 = some n := by
  cases n <;> rfl

theorem pairRemainder_zero_left_succ (k : Nat) :
    pairRemainder 0 (Nat.succ k) = none := by
  rfl

theorem pairRemainder_one_left_succ (k : Nat) :
    pairRemainder 1 (Nat.succ k) = none := by
  rfl

theorem pairRemainder_succ_succ_succ (n k : Nat) :
    pairRemainder (Nat.succ (Nat.succ n)) (Nat.succ k) =
      pairRemainder n k := by
  rfl

theorem rangeFuel_zero :
    rangeFuel 0 = [0] := by
  rfl

theorem rangeFuel_succ (fuel : Nat) :
    rangeFuel (Nat.succ fuel) = rangeFuel fuel ++ [Nat.succ fuel] := by
  rfl

theorem natListSum_nil :
    natListSum [] = 0 := by
  rfl

theorem natListSum_cons (x : Nat) (xs : List Nat) :
    natListSum (x :: xs) = x + natListSum xs := by
  rfl

theorem telephoneFormulaTerm_zero (n : Nat) :
    telephoneFormulaTerm n 0 = factorialCount n / factorialCount n := by
  unfold telephoneFormulaTerm factorialCount
  rw [pairRemainder_zero_right]
  change BEDC.Derived.PochhammerUp.natFactorialCount n /
      (twoPow 0 * BEDC.Derived.PochhammerUp.natFactorialCount 0 *
        BEDC.Derived.PochhammerUp.natFactorialCount n) =
    BEDC.Derived.PochhammerUp.natFactorialCount n /
      BEDC.Derived.PochhammerUp.natFactorialCount n
  rw [twoPow_zero]
  rw [BEDC.Derived.PochhammerUp.natFactorialCount_zero]
  rw [Nat.one_mul]

theorem telephoneFormulaTerm_over_budget_zero (k : Nat) :
    telephoneFormulaTerm 0 (Nat.succ k) = 0 := by
  rfl

theorem telephoneFormulaTerm_succ_over_budget_zero (k : Nat) :
    telephoneFormulaTerm 1 (Nat.succ k) = 0 := by
  rfl

theorem telephoneFormulaTerm_pairRemainder (n k remainder : Nat) :
    pairRemainder n k = some remainder ->
      telephoneFormulaTerm n k =
        factorialCount n / (twoPow k * factorialCount k * factorialCount remainder) := by
  intro h
  unfold telephoneFormulaTerm
  rw [h]

theorem telephoneFormulaWithFuel_zero (n : Nat) :
    telephoneFormulaWithFuel n 0 = telephoneFormulaTerm n 0 := by
  rfl

theorem telephoneFormulaWithFuel_succ (n fuel : Nat) :
    telephoneFormulaWithFuel n (Nat.succ fuel) =
      natListSum
        (List.map (telephoneFormulaTerm n) (rangeFuel fuel ++ [Nat.succ fuel])) := by
  rfl

theorem telephoneFormulaNumber_sum_definition (n : Nat) :
    telephoneFormulaNumber n =
      natListSum (List.map (telephoneFormulaTerm n) (rangeFuel n)) := by
  rfl

theorem telephoneFormulaNumber_zero :
    telephoneFormulaNumber 0 = 1 := by
  rfl

theorem telephoneFormulaNumber_one :
    telephoneFormulaNumber 1 = 1 := by
  rfl

theorem telephoneFormulaNumber_two :
    telephoneFormulaNumber 2 = 2 := by
  rfl

theorem telephoneFormulaNumber_three :
    telephoneFormulaNumber 3 = 4 := by
  rfl

theorem telephoneFormulaNumber_four :
    telephoneFormulaNumber 4 = 10 := by
  rfl

theorem telephoneFormulaNumber_five :
    telephoneFormulaNumber 5 = 26 := by
  rfl

theorem telephoneFormulaNumber_six :
    telephoneFormulaNumber 6 = 76 := by
  rfl

theorem telephoneFormula_matches_recurrence_small :
    telephoneFormulaNumber 0 = telephoneNumber 0 ∧
      telephoneFormulaNumber 1 = telephoneNumber 1 ∧
        telephoneFormulaNumber 2 = telephoneNumber 2 ∧
          telephoneFormulaNumber 3 = telephoneNumber 3 ∧
            telephoneFormulaNumber 4 = telephoneNumber 4 ∧
              telephoneFormulaNumber 5 = telephoneNumber 5 ∧
                telephoneFormulaNumber 6 = telephoneNumber 6 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · rfl

theorem telephoneFormulaTerm_division_site_four_two :
    NatDivRem (telephoneFormulaTermDenominatorUp 4 2)
      (telephoneFormulaTermNumeratorUp 4 2)
      (natQuotFn (telephoneFormulaTermDenominatorUp 4 2)
        (telephoneFormulaTermNumeratorUp 4 2))
      (natModFn (telephoneFormulaTermDenominatorUp 4 2)
        (telephoneFormulaTermNumeratorUp 4 2)) := by
  exact natModFn_spec (natToUnary_unary _) (natToUnary_unary _)
    (fun h => not_hsame_e1_empty h)

theorem telephoneFormulaTerm_division_site_five_two :
    NatDivRem (telephoneFormulaTermDenominatorUp 5 2)
      (telephoneFormulaTermNumeratorUp 5 2)
      (natQuotFn (telephoneFormulaTermDenominatorUp 5 2)
        (telephoneFormulaTermNumeratorUp 5 2))
      (natModFn (telephoneFormulaTermDenominatorUp 5 2)
        (telephoneFormulaTermNumeratorUp 5 2)) := by
  exact natModFn_spec (natToUnary_unary _) (natToUnary_unary _)
    (fun h => not_hsame_e1_empty h)

theorem telephoneFormulaTerm_division_site_six_three :
    NatDivRem (telephoneFormulaTermDenominatorUp 6 3)
      (telephoneFormulaTermNumeratorUp 6 3)
      (natQuotFn (telephoneFormulaTermDenominatorUp 6 3)
        (telephoneFormulaTermNumeratorUp 6 3))
      (natModFn (telephoneFormulaTermDenominatorUp 6 3)
        (telephoneFormulaTermNumeratorUp 6 3)) := by
  exact natModFn_spec (natToUnary_unary _) (natToUnary_unary _)
    (fun h => not_hsame_e1_empty h)

theorem telephoneNumberFn_unary_result (n : BHist) :
    UnaryHistory (telephoneNumberFn n) := by
  unfold telephoneNumberFn
  exact natToUnary_unary _

theorem telephoneFormulaNumberFn_unary_result (n : BHist) :
    UnaryHistory (telephoneFormulaNumberFn n) := by
  unfold telephoneFormulaNumberFn
  exact natToUnary_unary _

theorem telephoneNumberFn_recurrence_natToUnary (n : Nat) :
    telephoneNumberFn (natToUnary (n + 2)) =
      natToUnary
        (telephoneNumber (n + 1) + (n + 1) * telephoneNumber n) := by
  unfold telephoneNumberFn
  rw [natToUnary_length]
  rfl

theorem telephoneFormulaNumberFn_length (n : Nat) :
    bwordLength (telephoneFormulaNumberFn (natToUnary n)) =
      telephoneFormulaNumber n := by
  unfold telephoneFormulaNumberFn
  have inputLength : bwordLength (natToUnary n) = n := natToUnary_length n
  rw [inputLength]
  exact natToUnary_length _

theorem TelephoneNumberUp_constructive_export :
    (∀ n : Nat,
      telephoneNumber (n + 2) =
        telephoneNumber (n + 1) + (n + 1) * telephoneNumber n) ∧
      telephoneNumber 0 = 1 ∧ telephoneNumber 1 = 1 ∧
        telephoneNumber 2 = 2 ∧ telephoneNumber 3 = 4 ∧
          telephoneNumber 4 = 10 ∧ telephoneNumber 5 = 26 ∧
            telephoneNumber 6 = 76 ∧
              telephoneFormulaNumber 0 = 1 ∧ telephoneFormulaNumber 1 = 1 ∧
                telephoneFormulaNumber 2 = 2 ∧ telephoneFormulaNumber 3 = 4 ∧
                  telephoneFormulaNumber 4 = 10 ∧ telephoneFormulaNumber 5 = 26 ∧
                    telephoneFormulaNumber 6 = 76 ∧
                      NatDivRem (telephoneFormulaTermDenominatorUp 6 3)
                        (telephoneFormulaTermNumeratorUp 6 3)
                        (natQuotFn (telephoneFormulaTermDenominatorUp 6 3)
                          (telephoneFormulaTermNumeratorUp 6 3))
                        (natModFn (telephoneFormulaTermDenominatorUp 6 3)
                          (telephoneFormulaTermNumeratorUp 6 3)) := by
  constructor
  · intro n
    exact telephoneNumber_recurrence n
  · constructor
    · exact telephoneNumber_zero
    · constructor
      · exact telephoneNumber_one
      · constructor
        · exact telephoneNumber_two
        · constructor
          · exact telephoneNumber_three
          · constructor
            · exact telephoneNumber_four
            · constructor
              · exact telephoneNumber_five
              · constructor
                · exact telephoneNumber_six
                · constructor
                  · exact telephoneFormulaNumber_zero
                  · constructor
                    · exact telephoneFormulaNumber_one
                    · constructor
                      · exact telephoneFormulaNumber_two
                      · constructor
                        · exact telephoneFormulaNumber_three
                        · constructor
                          · exact telephoneFormulaNumber_four
                          · constructor
                            · exact telephoneFormulaNumber_five
                            · constructor
                              · exact telephoneFormulaNumber_six
                              · exact telephoneFormulaTerm_division_site_six_three

end BEDC.Derived.TelephoneNumberUp
