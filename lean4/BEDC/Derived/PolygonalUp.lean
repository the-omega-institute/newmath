import BEDC.Derived.FactorialUp
import BEDC.Derived.StirlingUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Algebra.Rel.IntegerUp

namespace BEDC.Derived.PolygonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp (NatChoose)
open BEDC.Derived.StirlingUp (UnaryTwo chooseTwo NatChoose_two_natToUnary)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

set_option linter.unusedSimpArgs false

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

private abbrev integerRing :
    BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def triangularNumber (n : Nat) : Nat :=
  chooseTwo (Nat.succ n)

def squareNumber (n : Nat) : Nat :=
  n * n

def pentagonalNumber : Nat -> Nat
  | 0 => 0
  | Nat.succ n => pentagonalNumber n + (3 * n + 1)

def polygonalNumber (s : Nat) : Nat -> Nat
  | 0 => 0
  | Nat.succ n => polygonalNumber s n + ((s - 2) * n + 1)

def triangularFn (n : BHist) : BHist :=
  natToUnary (triangularNumber (bwordLength n))

def squareFn (n : BHist) : BHist :=
  natToUnary (squareNumber (bwordLength n))

def pentagonalFn (n : BHist) : BHist :=
  natToUnary (pentagonalNumber (bwordLength n))

def polygonalFn (s n : BHist) : BHist :=
  natToUnary (polygonalNumber (bwordLength s) (bwordLength n))

theorem triangularFn_unary (n : BHist) :
    UnaryHistory (triangularFn n) := by
  unfold triangularFn
  exact natToUnary_unary _

theorem squareFn_unary (n : BHist) :
    UnaryHistory (squareFn n) := by
  unfold squareFn
  exact natToUnary_unary _

theorem pentagonalFn_unary (n : BHist) :
    UnaryHistory (pentagonalFn n) := by
  unfold pentagonalFn
  exact natToUnary_unary _

theorem polygonalFn_unary (s n : BHist) :
    UnaryHistory (polygonalFn s n) := by
  unfold polygonalFn
  exact natToUnary_unary _

theorem triangular_zero :
    triangularNumber 0 = 0 := by
  rfl

theorem triangular_one :
    triangularNumber 1 = 1 := by
  rfl

theorem pentagonal_zero :
    pentagonalNumber 0 = 0 := by
  rfl

theorem pentagonal_one :
    pentagonalNumber 1 = 1 := by
  rfl

theorem square_succ (n : Nat) :
    squareNumber (Nat.succ n) = squareNumber n + n + Nat.succ n := by
  unfold squareNumber
  rw [Nat.mul_succ]
  rw [Nat.succ_mul]

theorem pentagonal_succ (n : Nat) :
    pentagonalNumber (Nat.succ n) = pentagonalNumber n + (3 * n + 1) := by
  rfl

theorem polygonal_succ (s n : Nat) :
    polygonalNumber s (Nat.succ n) =
      polygonalNumber s n + ((s - 2) * n + 1) := by
  rfl

theorem polygonal_three_step (n : Nat) :
    (3 - 2) * n + 1 = Nat.succ n := by
  change 1 * n + 1 = Nat.succ n
  rw [Nat.one_mul]

theorem polygonal_four_step (n : Nat) :
    (4 - 2) * n + 1 = n + Nat.succ n := by
  change 2 * n + 1 = n + Nat.succ n
  rw [Nat.two_mul]
  change Nat.succ (n + n) = n + Nat.succ n
  exact (Nat.add_succ n n).symm

theorem triangular_succ (n : Nat) :
    triangularNumber (Nat.succ n) = triangularNumber n + Nat.succ n := by
  unfold triangularNumber chooseTwo
  change Nat.succ n + chooseTwo (Nat.succ n) =
    chooseTwo (Nat.succ n) + Nat.succ n
  exact Nat.add_comm _ _

theorem polygonal_three_eq_triangular (n : Nat) :
    polygonalNumber 3 n = triangularNumber n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [polygonal_succ, triangular_succ, ih, polygonal_three_step]

theorem polygonal_four_eq_square (n : Nat) :
    polygonalNumber 4 n = squareNumber n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [polygonal_succ, square_succ, ih, polygonal_four_step]
      rw [Nat.add_assoc]

theorem polygonal_five_eq_pentagonal (n : Nat) :
    polygonalNumber 5 n = pentagonalNumber n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [polygonal_succ, pentagonal_succ, ih]

theorem triangular_eq_previous_add_self (n : Nat) :
    triangularNumber n = triangularNumber (n - 1) + n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      exact triangular_succ n

theorem triangular_double_eq_mul_succ (n : Nat) :
    2 * triangularNumber n = n * Nat.succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [triangular_succ]
      rw [Nat.mul_add]
      rw [ih]
      rw [Nat.mul_succ n n]
      rw [Nat.succ_mul]
      rw [Nat.one_mul]
      rw [Nat.mul_succ (Nat.succ n) (Nat.succ n)]
      rw [Nat.mul_succ (Nat.succ n) n]
      rw [Nat.succ_mul n n]
      rw [Nat.add_assoc (n * n + n) (Nat.succ n) (Nat.succ n)]

private theorem tri_square_add_rearrange (p n : Nat) :
    p + n + Nat.succ n + (p + n) = p + n + p + n + Nat.succ n := by
  change ((p + n) + Nat.succ n) + (p + n) =
    (((p + n) + p) + n) + Nat.succ n
  rw [Nat.add_assoc (p + n) (Nat.succ n) (p + n)]
  rw [Nat.add_comm (Nat.succ n) (p + n)]
  rw [← Nat.add_assoc (p + n) (p + n) (Nat.succ n)]
  change (p + n + (p + n)) + Nat.succ n =
    (((p + n) + p) + n) + Nat.succ n
  rw [Nat.add_assoc (p + n) p n]

theorem triangular_add_previous_eq_square (n : Nat) :
    triangularNumber n + triangularNumber (n - 1) = squareNumber n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [square_succ]
      rw [← ih]
      rw [triangular_succ]
      rw [show n + 1 - 1 = n by exact Nat.succ_sub_one n]
      rw [triangular_eq_previous_add_self n]
      exact tri_square_add_rearrange (triangularNumber (n - 1)) n

theorem triangular_eq_chooseTwo_nat (n : Nat) :
    triangularNumber n = chooseTwo (Nat.succ n) := by
  rfl

theorem triangular_succ_natChoose_two (n : Nat) :
    NatChoose (natToUnary (Nat.succ (Nat.succ n))) UnaryTwo
      (natToUnary (triangularNumber (Nat.succ n))) := by
  rw [triangular_eq_chooseTwo_nat]
  exact NatChoose_two_natToUnary n

theorem triangular_eq_choose_two_length (n : BHist) :
    triangularNumber (bwordLength n) =
      chooseTwo (Nat.succ (bwordLength n)) := by
  rfl

theorem triangularFn_natToUnary (n : Nat) :
    triangularFn (natToUnary n) = natToUnary (triangularNumber n) := by
  unfold triangularFn
  rw [natToUnary_length]

theorem squareFn_natToUnary (n : Nat) :
    squareFn (natToUnary n) = natToUnary (squareNumber n) := by
  unfold squareFn
  rw [natToUnary_length]

theorem pentagonalFn_natToUnary (n : Nat) :
    pentagonalFn (natToUnary n) = natToUnary (pentagonalNumber n) := by
  unfold pentagonalFn
  rw [natToUnary_length]

theorem integerRing_refl_for_polygonal_carrier (x : IntegerUp) :
    IntEq x x :=
  integerRing.refl x

theorem PolygonalUp_constructive_export :
    triangularNumber 0 = 0 ∧
      triangularNumber 1 = 1 ∧
      pentagonalNumber 0 = 0 ∧
      pentagonalNumber 1 = 1 ∧
      (∀ n : Nat, polygonalNumber 3 n = triangularNumber n) ∧
      (∀ n : Nat, polygonalNumber 4 n = squareNumber n) ∧
      (∀ n : Nat, polygonalNumber 5 n = pentagonalNumber n) ∧
      (∀ n : Nat,
        triangularNumber n + triangularNumber (n - 1) = squareNumber n) ∧
      (∀ n : Nat,
        2 * triangularNumber n = n * Nat.succ n) ∧
      (∀ n : Nat,
        triangularNumber n = chooseTwo (Nat.succ n)) := by
  constructor
  · exact triangular_zero
  · constructor
    · exact triangular_one
    · constructor
      · exact pentagonal_zero
      · constructor
        · exact pentagonal_one
        · constructor
          · intro n
            exact polygonal_three_eq_triangular n
          · constructor
            · intro n
              exact polygonal_four_eq_square n
            · constructor
              · intro n
                exact polygonal_five_eq_pentagonal n
              · constructor
                · intro n
                  exact triangular_add_previous_eq_square n
                · constructor
                  · intro n
                    exact triangular_double_eq_mul_succ n
                  · intro n
                    exact triangular_eq_chooseTwo_nat n

end BEDC.Derived.PolygonalUp
