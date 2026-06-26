import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.DerangementUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.PadicUp

namespace BEDC.Derived.MenageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev factorialCount (n : Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natFactorialCount n

abbrev derangementNumber (n : Nat) : Nat :=
  BEDC.Derived.DerangementUp.derangementNumber n

def rangeFuel : Nat -> List Nat
  | 0 => [0]
  | Nat.succ fuel => rangeFuel fuel ++ [Nat.succ fuel]

def intListSum : List Int -> Int
  | [] => 0
  | x :: xs => x + intListSum xs

def alternatingSignedTerm : Nat -> Nat -> Int
  | 0, value => value
  | Nat.succ k, value => -alternatingSignedTerm k value

def menageFormulaTermNat (n k : Nat) : Nat :=
  match 2 * n - k with
  | 0 => 0
  | Nat.succ d =>
      ((2 * n) * C (2 * n - k) k * factorialCount (n - k)) / Nat.succ d

def menageFormulaTermNumerator (n k : Nat) : Nat :=
  (2 * n) * C (2 * n - k) k * factorialCount (n - k)

def menageFormulaTermDivisor (n k : Nat) : Nat :=
  2 * n - k

def menageFormulaTermDivisorUp (n k : Nat) : BHist :=
  natToUnary (menageFormulaTermDivisor n k)

def menageFormulaTermNumeratorUp (n k : Nat) : BHist :=
  natToUnary (menageFormulaTermNumerator n k)

def menageFormulaTermQuotientUp (n k : Nat) : BHist :=
  natToUnary (menageFormulaTermNat n k)

def menageFormulaTerm (n k : Nat) : Int :=
  alternatingSignedTerm k (menageFormulaTermNat n k)

def menageFormulaWithFuel (n fuel : Nat) : Int :=
  intListSum (List.map (menageFormulaTerm n) (rangeFuel fuel))

def menageFormulaNumber (n : Nat) : Int :=
  menageFormulaWithFuel n n

def menageNumber (n : Nat) : Nat :=
  Int.toNat (menageFormulaNumber n)

def menageLinearRemainder (n : Nat) : Int :=
  menageFormulaNumber (Nat.succ n) - ((n : Int) * menageFormulaNumber n)

def menageDerangementGap (n : Nat) : Int :=
  menageFormulaNumber n - (derangementNumber n : Int)

theorem rangeFuel_zero :
    rangeFuel 0 = [0] := by
  rfl

theorem rangeFuel_succ (fuel : Nat) :
    rangeFuel (Nat.succ fuel) = rangeFuel fuel ++ [Nat.succ fuel] := by
  rfl

theorem intListSum_nil :
    intListSum [] = 0 := by
  rfl

theorem intListSum_cons (x : Int) (xs : List Int) :
    intListSum (x :: xs) = x + intListSum xs := by
  rfl

theorem alternatingSignedTerm_zero (value : Nat) :
    alternatingSignedTerm 0 value = (value : Int) := by
  rfl

theorem alternatingSignedTerm_succ (k value : Nat) :
    alternatingSignedTerm (Nat.succ k) value = -alternatingSignedTerm k value := by
  rfl

theorem menageFormulaTermNat_denominator_zero (n k : Nat) :
    2 * n - k = 0 -> menageFormulaTermNat n k = 0 := by
  intro h
  unfold menageFormulaTermNat
  rw [h]

theorem menageFormulaTermNat_denominator_succ (n k d : Nat) :
    2 * n - k = Nat.succ d ->
      menageFormulaTermNat n k =
        ((2 * n) * C (2 * n - k) k * factorialCount (n - k)) / Nat.succ d := by
  intro h
  unfold menageFormulaTermNat
  rw [h]

theorem menageFormulaTerm_division_site_three_zero :
    NatDivRem (menageFormulaTermDivisorUp 3 0)
      (menageFormulaTermNumeratorUp 3 0)
      (natQuotFn (menageFormulaTermDivisorUp 3 0)
        (menageFormulaTermNumeratorUp 3 0))
      (natModFn (menageFormulaTermDivisorUp 3 0)
        (menageFormulaTermNumeratorUp 3 0)) := by
  exact natModFn_spec (natToUnary_unary _) (natToUnary_unary _)
    (fun h => not_hsame_e1_empty h)

theorem menageFormulaTerm_division_site_four_two :
    NatDivRem (menageFormulaTermDivisorUp 4 2)
      (menageFormulaTermNumeratorUp 4 2)
      (natQuotFn (menageFormulaTermDivisorUp 4 2)
        (menageFormulaTermNumeratorUp 4 2))
      (natModFn (menageFormulaTermDivisorUp 4 2)
        (menageFormulaTermNumeratorUp 4 2)) := by
  exact natModFn_spec (natToUnary_unary _) (natToUnary_unary _)
    (fun h => not_hsame_e1_empty h)

theorem menageFormulaTerm_division_site_five_four :
    NatDivRem (menageFormulaTermDivisorUp 5 4)
      (menageFormulaTermNumeratorUp 5 4)
      (natQuotFn (menageFormulaTermDivisorUp 5 4)
        (menageFormulaTermNumeratorUp 5 4))
      (natModFn (menageFormulaTermDivisorUp 5 4)
        (menageFormulaTermNumeratorUp 5 4)) := by
  exact natModFn_spec (natToUnary_unary _) (natToUnary_unary _)
    (fun h => not_hsame_e1_empty h)

theorem menageFormulaTerm_division_sites_unary :
    UnaryHistory (menageFormulaTermDivisorUp 3 0) ∧
      UnaryHistory (menageFormulaTermNumeratorUp 4 2) ∧
        UnaryHistory (menageFormulaTermQuotientUp 5 4) := by
  constructor
  · exact natToUnary_unary _
  · constructor
    · exact natToUnary_unary _
    · exact natToUnary_unary _

theorem menageFormulaWithFuel_zero (n : Nat) :
    menageFormulaWithFuel n 0 = menageFormulaTerm n 0 := by
  rfl

theorem menageFormulaWithFuel_succ (n fuel : Nat) :
    menageFormulaWithFuel n (Nat.succ fuel) =
      intListSum
        (List.map (menageFormulaTerm n) (rangeFuel fuel ++ [Nat.succ fuel])) := by
  rfl

theorem menageNumber_def (n : Nat) :
    menageNumber n = Int.toNat (menageFormulaNumber n) := by
  rfl

theorem menageNumber_three :
    menageNumber 3 = 1 := by
  rfl

theorem menageNumber_four :
    menageNumber 4 = 2 := by
  rfl

theorem menageNumber_five :
    menageNumber 5 = 13 := by
  rfl

theorem menageFormulaNumber_three :
    menageFormulaNumber 3 = 1 := by
  rfl

theorem menageFormulaNumber_four :
    menageFormulaNumber 4 = 2 := by
  rfl

theorem menageFormulaNumber_five :
    menageFormulaNumber 5 = 13 := by
  rfl

theorem menageFormulaNumber_one :
    menageFormulaNumber 1 = -1 := by
  rfl

theorem menageFormulaNumber_two :
    menageFormulaNumber 2 = 0 := by
  rfl

theorem menageFormula_three_term_expansion :
    menageFormulaNumber 3 =
      menageFormulaTerm 3 0 + menageFormulaTerm 3 1 +
        menageFormulaTerm 3 2 + menageFormulaTerm 3 3 := by
  rfl

theorem menageFormula_four_term_expansion :
    menageFormulaNumber 4 =
      menageFormulaTerm 4 0 + menageFormulaTerm 4 1 +
        menageFormulaTerm 4 2 + menageFormulaTerm 4 3 +
          menageFormulaTerm 4 4 := by
  rfl

theorem menageFormula_five_term_expansion :
    menageFormulaNumber 5 =
      menageFormulaTerm 5 0 + menageFormulaTerm 5 1 +
        menageFormulaTerm 5 2 + menageFormulaTerm 5 3 +
          menageFormulaTerm 5 4 + menageFormulaTerm 5 5 := by
  rfl

theorem menage_formula_linear_recurrence_at_five :
    menageFormulaNumber 5 =
      (5 : Int) * menageFormulaNumber 4 + 3 := by
  rfl

theorem menage_formula_four_term_recurrence_at_five :
    menageFormulaNumber 5 =
      (5 : Int) * menageFormulaNumber 4 +
        2 * menageFormulaNumber 3 -
          ((5 : Int) - 4) * menageFormulaNumber 2 -
            menageFormulaNumber 1 := by
  rfl

theorem menage_derangement_low_relation :
    menageNumber 3 = derangementNumber 2 ∧
      menageNumber 4 = derangementNumber 3 ∧
        menageNumber 5 =
          derangementNumber 4 + derangementNumber 3 +
            derangementNumber 2 + derangementNumber 0 := by
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

theorem MenageUp_constructive_export :
    menageFormulaNumber 3 = 1 ∧
      menageFormulaNumber 4 = 2 ∧
        menageFormulaNumber 5 = 13 ∧
          menageNumber 3 = 1 ∧
            menageNumber 4 = 2 ∧
              menageNumber 5 = 13 ∧
                NatDivRem (menageFormulaTermDivisorUp 3 0)
                  (menageFormulaTermNumeratorUp 3 0)
                  (natQuotFn (menageFormulaTermDivisorUp 3 0)
                    (menageFormulaTermNumeratorUp 3 0))
                  (natModFn (menageFormulaTermDivisorUp 3 0)
                    (menageFormulaTermNumeratorUp 3 0)) ∧
                menageFormulaNumber 5 =
                  (5 : Int) * menageFormulaNumber 4 +
                    2 * menageFormulaNumber 3 -
                      ((5 : Int) - 4) * menageFormulaNumber 2 -
                        menageFormulaNumber 1 ∧
                  menageNumber 3 = derangementNumber 2 ∧
                    menageNumber 4 = derangementNumber 3 := by
  constructor
  · exact menageFormulaNumber_three
  · constructor
    · exact menageFormulaNumber_four
    · constructor
      · exact menageFormulaNumber_five
      · constructor
        · exact menageNumber_three
        · constructor
          · exact menageNumber_four
          · constructor
            · exact menageNumber_five
            · constructor
              · exact menageFormulaTerm_division_site_three_zero
              · constructor
                · exact menage_formula_four_term_recurrence_at_five
                · constructor
                  · exact menage_derangement_low_relation.left
                  · exact menage_derangement_low_relation.right.left

end BEDC.Derived.MenageUp
