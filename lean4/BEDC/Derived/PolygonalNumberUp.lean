import BEDC.Derived.PolygonalUp

namespace BEDC.Derived.PolygonalNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev triangularNumber : Nat -> Nat :=
  BEDC.Derived.PolygonalUp.triangularNumber

abbrev squareNumber : Nat -> Nat :=
  BEDC.Derived.PolygonalUp.squareNumber

abbrev pentagonalNumber : Nat -> Nat :=
  BEDC.Derived.PolygonalUp.pentagonalNumber

abbrev polygonalNumber : Nat -> Nat -> Nat :=
  BEDC.Derived.PolygonalUp.polygonalNumber

def natHalf : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | Nat.succ (Nat.succ n) => Nat.succ (natHalf n)

def polygonalNumberClosedFormula (k n : Nat) : Nat :=
  natHalf (2 * n + (k - 2) * n * (n - 1))

def triangularFn (n : BHist) : BHist :=
  natToUnary (triangularNumber (bwordLength n))

def squareFn (n : BHist) : BHist :=
  natToUnary (squareNumber (bwordLength n))

def pentagonalFn (n : BHist) : BHist :=
  natToUnary (pentagonalNumber (bwordLength n))

def polygonalFn (k n : BHist) : BHist :=
  natToUnary (polygonalNumber (bwordLength k) (bwordLength n))

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

theorem polygonalFn_unary (k n : BHist) :
    UnaryHistory (polygonalFn k n) := by
  unfold polygonalFn
  exact natToUnary_unary _

theorem polygonal_recurrence (k n : Nat) :
    polygonalNumber k (Nat.succ n) =
      polygonalNumber k n + ((k - 2) * n + 1) := by
  exact BEDC.Derived.PolygonalUp.polygonal_succ k n

theorem polygonal_three_eq_triangular (n : Nat) :
    polygonalNumber 3 n = triangularNumber n :=
  BEDC.Derived.PolygonalUp.polygonal_three_eq_triangular n

theorem polygonal_four_eq_square (n : Nat) :
    polygonalNumber 4 n = squareNumber n :=
  BEDC.Derived.PolygonalUp.polygonal_four_eq_square n

theorem polygonal_five_eq_pentagonal (n : Nat) :
    polygonalNumber 5 n = pentagonalNumber n :=
  BEDC.Derived.PolygonalUp.polygonal_five_eq_pentagonal n

private theorem triangular_eq_previous_add_self_local (n : Nat) :
    triangularNumber n = triangularNumber (n - 1) + n :=
  BEDC.Derived.PolygonalUp.triangular_eq_previous_add_self n

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) :=
          congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem polygonal_triangle_step_shuffle (a t n : Nat) :
    (n + a * t) + (a * n + 1) = Nat.succ n + (a * t + a * n) := by
  calc
    (n + a * t) + (a * n + 1) =
        n + (a * t + (a * n + 1)) := Nat.add_assoc n (a * t) (a * n + 1)
    _ = n + ((a * t + a * n) + 1) :=
        congrArg (fun x => n + x) (Nat.add_assoc (a * t) (a * n) 1).symm
    _ = (a * t + a * n) + (n + 1) := by
        rw [Nat.add_comm n ((a * t + a * n) + 1)]
        rw [Nat.add_assoc (a * t + a * n) 1 n]
        rw [Nat.add_comm 1 n]
    _ = (n + 1) + (a * t + a * n) :=
        Nat.add_comm (a * t + a * n) (n + 1)
    _ = Nat.succ n + (a * t + a * n) := by
        rw [Nat.succ_eq_add_one]

theorem polygonal_triangular_relation (k n : Nat) :
    polygonalNumber k n =
      n + (k - 2) * triangularNumber (n - 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [polygonal_recurrence, ih]
      rw [Nat.succ_sub_one]
      rw [triangular_eq_previous_add_self_local n]
      rw [Nat.mul_add]
      exact polygonal_triangle_step_shuffle (k - 2) (triangularNumber (n - 1)) n

private theorem polygonal_scaled_shuffle (a t n : Nat) :
    2 * (n + a * t) = 2 * n + a * (2 * t) := by
  calc
    2 * (n + a * t) = 2 * n + 2 * (a * t) := Nat.mul_add 2 n (a * t)
    _ = 2 * n + a * (2 * t) := by
        rw [Nat.mul_comm 2 (a * t)]
        rw [nat_mul_assoc_pure a t 2]
        rw [Nat.mul_comm t 2]

theorem polygonal_general_formula_scaled (k n : Nat) :
    2 * polygonalNumber k n =
      2 * n + (k - 2) * (2 * triangularNumber (n - 1)) := by
  rw [polygonal_triangular_relation]
  exact polygonal_scaled_shuffle (k - 2) (triangularNumber (n - 1)) n

theorem polygonal_triangular_double_relation (k n : Nat) :
    2 * polygonalNumber k n =
      2 * n + (k - 2) * n * (n - 1) := by
  rw [polygonal_general_formula_scaled]
  rw [BEDC.Derived.PolygonalUp.triangular_double_eq_mul_succ (n - 1)]
  cases n with
  | zero =>
      rfl
  | succ n =>
      rw [Nat.succ_sub_one]
      rw [Nat.mul_comm n (Nat.succ n)]
      rw [nat_mul_assoc_pure (k - 2) (Nat.succ n) n]

theorem natHalf_two_mul (n : Nat) :
    natHalf (2 * n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.mul_succ]
      change natHalf (Nat.succ (Nat.succ (2 * n))) = Nat.succ n
      change Nat.succ (natHalf (2 * n)) = Nat.succ n
      rw [ih]

theorem polygonal_closed_formula (k n : Nat) :
    polygonalNumber k n = polygonalNumberClosedFormula k n := by
  unfold polygonalNumberClosedFormula
  have h := congrArg natHalf (polygonal_triangular_double_relation k n)
  rw [natHalf_two_mul] at h
  exact h

theorem triangular_relation_to_square (n : Nat) :
    triangularNumber n + triangularNumber (n - 1) = squareNumber n :=
  BEDC.Derived.PolygonalUp.triangular_add_previous_eq_square n

theorem triangular_double_relation (n : Nat) :
    2 * triangularNumber n = n * Nat.succ n :=
  BEDC.Derived.PolygonalUp.triangular_double_eq_mul_succ n

theorem polygonalFn_natToUnary (k n : Nat) :
    polygonalFn (natToUnary k) (natToUnary n) =
      natToUnary (polygonalNumber k n) := by
  unfold polygonalFn
  rw [natToUnary_length, natToUnary_length]

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

theorem PolygonalNumberUp_constructive_export :
    (∀ k n : Nat,
      polygonalNumber k n = polygonalNumberClosedFormula k n) ∧
      (∀ k n : Nat,
        2 * polygonalNumber k n =
          2 * n + (k - 2) * n * (n - 1)) ∧
      (∀ k n : Nat,
        polygonalNumber k (Nat.succ n) =
          polygonalNumber k n + ((k - 2) * n + 1)) ∧
      (∀ n : Nat, polygonalNumber 3 n = triangularNumber n) ∧
      (∀ n : Nat, polygonalNumber 4 n = squareNumber n) ∧
      (∀ n : Nat, polygonalNumber 5 n = pentagonalNumber n) ∧
      (∀ k n : Nat,
        polygonalNumber k n =
          n + (k - 2) * triangularNumber (n - 1)) ∧
      (∀ n : Nat,
        triangularNumber n + triangularNumber (n - 1) = squareNumber n) := by
  constructor
  · intro k n
    exact polygonal_closed_formula k n
  · constructor
    · intro k n
      exact polygonal_triangular_double_relation k n
    · constructor
      · intro k n
        exact polygonal_recurrence k n
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
              · intro k n
                exact polygonal_triangular_relation k n
              · intro n
                exact triangular_relation_to_square n

end BEDC.Derived.PolygonalNumberUp
