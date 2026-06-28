import BEDC.Derived.CenteredPolygonalUp
import BEDC.Derived.PolygonalUp

namespace BEDC.Derived.SquarePyramidalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev triangularNumber := BEDC.Derived.PolygonalUp.triangularNumber
abbrev squareNumber := BEDC.Derived.PolygonalUp.squareNumber

def squarePyramidalNumber : Nat -> Nat
  | 0 => 0
  | Nat.succ n => squarePyramidalNumber n + squareNumber (Nat.succ n)

def squareSumTo (n : Nat) : Nat :=
  squarePyramidalNumber n

def squarePyramidalNumerator (n : Nat) : Nat :=
  n * (n + 1) * (2 * n + 1)

def divSix : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))) =>
      Nat.succ (divSix n)

def squarePyramidalClosedForm (n : Nat) : Nat :=
  divSix (squarePyramidalNumerator n)

def tetrahedralNumber : Nat -> Nat
  | 0 => 0
  | Nat.succ n => tetrahedralNumber n + triangularNumber (Nat.succ n)

def squarePyramidalFn (n : BHist) : BHist :=
  natToUnary (squarePyramidalNumber (bwordLength n))

def squarePyramidalClosedFormFn (n : BHist) : BHist :=
  natToUnary (squarePyramidalClosedForm (bwordLength n))

theorem squarePyramidal_zero :
    squarePyramidalNumber 0 = 0 := by
  rfl

theorem squarePyramidal_succ (n : Nat) :
    squarePyramidalNumber (Nat.succ n) =
      squarePyramidalNumber n + squareNumber (Nat.succ n) := by
  rfl

theorem squareSumTo_eq_squarePyramidal (n : Nat) :
    squareSumTo n = squarePyramidalNumber n := by
  rfl

theorem squarePyramidalFn_unary (n : BHist) :
    UnaryHistory (squarePyramidalFn n) := by
  unfold squarePyramidalFn
  exact natToUnary_unary _

theorem squarePyramidalClosedFormFn_unary (n : BHist) :
    UnaryHistory (squarePyramidalClosedFormFn n) := by
  unfold squarePyramidalClosedFormFn
  exact natToUnary_unary _

theorem squarePyramidalFn_natToUnary (n : Nat) :
    squarePyramidalFn (natToUnary n) =
      natToUnary (squarePyramidalNumber n) := by
  unfold squarePyramidalFn
  rw [natToUnary_length]

theorem squarePyramidalClosedFormFn_natToUnary (n : Nat) :
    squarePyramidalClosedFormFn (natToUnary n) =
      natToUnary (squarePyramidalClosedForm n) := by
  unfold squarePyramidalClosedFormFn
  rw [natToUnary_length]

theorem divSix_six_mul (n : Nat) :
    divSix (6 * n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.mul_succ]
      change Nat.succ (divSix (6 * n)) = Nat.succ n
      rw [ih]

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun t => t + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) :=
          congrArg (fun t => a * t) (Nat.mul_succ b c).symm

private theorem nat_add_mul_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * Nat.succ c = (a + b) * c + (a + b) :=
          Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) :=
          congrArg (fun t => t + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun t => a * c + t) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun t => a * c + (t + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun t => a * c + t) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun t => t + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun t => a * Nat.succ c + t) (Nat.mul_succ b c).symm

private theorem mul_left_swap (a b c : Nat) :
    a * (b * c) = b * (a * c) := by
  calc
    a * (b * c) = (a * b) * c := (nat_mul_assoc_clean a b c).symm
    _ = (b * a) * c := congrArg (fun t => t * c) (Nat.mul_comm a b)
    _ = b * (a * c) := nat_mul_assoc_clean b a c

private theorem add_four_rearrange (a b c d : Nat) :
    a + (b + (c + d)) = a + (c + (b + d)) := by
  rw [Nat.add_left_comm b c d]

private def polyEval : List Nat -> Nat -> Nat
  | [], _ => 0
  | c :: cs, n => c + n * polyEval cs n

private def polyAdd : List Nat -> List Nat -> List Nat
  | [], qs => qs
  | p :: ps, [] => p :: ps
  | p :: ps, q :: qs => (p + q) :: polyAdd ps qs

private def polyScale (c : Nat) : List Nat -> List Nat
  | [] => []
  | p :: ps => (c * p) :: polyScale c ps

private def polyShift (ps : List Nat) : List Nat :=
  0 :: ps

private def polyMul : List Nat -> List Nat -> List Nat
  | [], _ => []
  | p :: ps, qs => polyAdd (polyScale p qs) (polyShift (polyMul ps qs))

private theorem polyAdd_eval (ps qs : List Nat) (n : Nat) :
    polyEval (polyAdd ps qs) n = polyEval ps n + polyEval qs n := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil =>
          rfl
      | cons _q _qs =>
          rw [polyAdd, polyEval, Nat.zero_add]
  | cons p ps ih =>
      cases qs with
      | nil =>
          rw [polyAdd, polyEval, polyEval, Nat.add_zero]
      | cons q qs =>
          rw [polyAdd, polyEval, polyEval, polyEval]
          rw [ih qs]
          calc
            p + q + n * (polyEval ps n + polyEval qs n) =
                p + q + (n * polyEval ps n + n * polyEval qs n) := by
                  rw [Nat.mul_add]
            _ = p + (q + (n * polyEval ps n + n * polyEval qs n)) :=
              Nat.add_assoc p q (n * polyEval ps n + n * polyEval qs n)
            _ = p + (n * polyEval ps n + (q + n * polyEval qs n)) :=
              add_four_rearrange p q (n * polyEval ps n) (n * polyEval qs n)
            _ = p + n * polyEval ps n + (q + n * polyEval qs n) :=
              (Nat.add_assoc p (n * polyEval ps n) (q + n * polyEval qs n)).symm

private theorem polyScale_eval (c : Nat) (ps : List Nat) (n : Nat) :
    polyEval (polyScale c ps) n = c * polyEval ps n := by
  induction ps with
  | nil =>
      rw [polyScale, polyEval, Nat.mul_zero]
  | cons p ps ih =>
      rw [polyScale, polyEval, polyEval]
      rw [ih]
      calc
        c * p + n * (c * polyEval ps n) =
            c * p + c * (n * polyEval ps n) := by
              rw [mul_left_swap n c (polyEval ps n)]
        _ = c * (p + n * polyEval ps n) :=
          (Nat.mul_add c p (n * polyEval ps n)).symm

private theorem polyShift_eval (ps : List Nat) (n : Nat) :
    polyEval (polyShift ps) n = n * polyEval ps n := by
  rw [polyShift, polyEval, Nat.zero_add]

private theorem polyMul_eval (ps qs : List Nat) (n : Nat) :
    polyEval (polyMul ps qs) n = polyEval ps n * polyEval qs n := by
  induction ps with
  | nil =>
      rw [polyMul, polyEval, Nat.zero_mul]
  | cons p ps ih =>
      rw [polyMul]
      rw [polyAdd_eval]
      rw [polyScale_eval]
      rw [polyShift_eval]
      rw [ih]
      rw [polyEval]
      calc
        p * polyEval qs n + n * (polyEval ps n * polyEval qs n) =
            p * polyEval qs n + (n * polyEval ps n) * polyEval qs n := by
              rw [nat_mul_assoc_clean]
        _ = (p + n * polyEval ps n) * polyEval qs n :=
          (nat_add_mul_clean p (n * polyEval ps n) (polyEval qs n)).symm

private inductive NatPolyExpr where
  | const : Nat -> NatPolyExpr
  | var : NatPolyExpr
  | add : NatPolyExpr -> NatPolyExpr -> NatPolyExpr
  | mul : NatPolyExpr -> NatPolyExpr -> NatPolyExpr

private def NatPolyExpr.eval : NatPolyExpr -> Nat -> Nat
  | NatPolyExpr.const c, _ => c
  | NatPolyExpr.var, n => n
  | NatPolyExpr.add a b, n => a.eval n + b.eval n
  | NatPolyExpr.mul a b, n => a.eval n * b.eval n

private def NatPolyExpr.normalize : NatPolyExpr -> List Nat
  | NatPolyExpr.const c => [c]
  | NatPolyExpr.var => [0, 1]
  | NatPolyExpr.add a b => polyAdd a.normalize b.normalize
  | NatPolyExpr.mul a b => polyMul a.normalize b.normalize

private theorem NatPolyExpr.eval_normalize (e : NatPolyExpr) (n : Nat) :
    polyEval (NatPolyExpr.normalize e) n = NatPolyExpr.eval e n := by
  induction e with
  | const c =>
      rw [NatPolyExpr.normalize, polyEval, polyEval, Nat.mul_zero, Nat.add_zero,
        NatPolyExpr.eval]
  | var =>
      rw [NatPolyExpr.normalize, polyEval, polyEval, polyEval, Nat.mul_zero,
        Nat.add_zero, Nat.mul_one, Nat.zero_add, NatPolyExpr.eval]
  | add a b iha ihb =>
      rw [NatPolyExpr.normalize, polyAdd_eval, iha, ihb, NatPolyExpr.eval]
  | mul a b iha ihb =>
      rw [NatPolyExpr.normalize, polyMul_eval, iha, ihb, NatPolyExpr.eval]

open NatPolyExpr in
private def polyClosedExpr : NatPolyExpr :=
  mul (mul var (add var (const 1))) (add (mul (const 2) var) (const 1))

open NatPolyExpr in
private def polySquareSuccExpr : NatPolyExpr :=
  mul (add var (const 1)) (add var (const 1))

open NatPolyExpr in
private def polyClosedSuccExpr : NatPolyExpr :=
  mul (mul (add var (const 1)) (add var (const 2)))
    (add (mul (const 2) (add var (const 1))) (const 1))

open NatPolyExpr in
private def polyStepRightExpr : NatPolyExpr :=
  add polyClosedExpr (mul (const 6) polySquareSuccExpr)

private theorem poly_closed_eval (n : Nat) :
    NatPolyExpr.eval polyClosedExpr n = squarePyramidalNumerator n := by
  rfl

private theorem poly_square_succ_eval (n : Nat) :
    NatPolyExpr.eval polySquareSuccExpr n = squareNumber (Nat.succ n) := by
  rfl

private theorem poly_closed_succ_eval (n : Nat) :
    NatPolyExpr.eval polyClosedSuccExpr n =
      squarePyramidalNumerator (Nat.succ n) := by
  rfl

private theorem poly_step_right_eval (n : Nat) :
    NatPolyExpr.eval polyStepRightExpr n =
      squarePyramidalNumerator n + 6 * squareNumber (Nat.succ n) := by
  rfl

private theorem succ_closed_numerator_step (n : Nat) :
    squarePyramidalNumerator (Nat.succ n) =
      squarePyramidalNumerator n + 6 * squareNumber (Nat.succ n) := by
  calc
    squarePyramidalNumerator (Nat.succ n) =
        NatPolyExpr.eval polyClosedSuccExpr n := (poly_closed_succ_eval n).symm
    _ = polyEval (NatPolyExpr.normalize polyClosedSuccExpr) n :=
        (NatPolyExpr.eval_normalize polyClosedSuccExpr n).symm
    _ = polyEval (NatPolyExpr.normalize polyStepRightExpr) n := rfl
    _ = NatPolyExpr.eval polyStepRightExpr n :=
        NatPolyExpr.eval_normalize polyStepRightExpr n
    _ = squarePyramidalNumerator n + 6 * squareNumber (Nat.succ n) :=
        poly_step_right_eval n

theorem squarePyramidal_closed_numerator (n : Nat) :
    6 * squarePyramidalNumber n = squarePyramidalNumerator n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [squarePyramidal_succ]
      rw [Nat.mul_add]
      rw [ih]
      exact (succ_closed_numerator_step n).symm

theorem squarePyramidal_closed_form (n : Nat) :
    squarePyramidalNumber n = squarePyramidalClosedForm n := by
  unfold squarePyramidalClosedForm
  rw [← squarePyramidal_closed_numerator n]
  exact (divSix_six_mul (squarePyramidalNumber n)).symm

theorem squarePyramidal_square_sum_closed (n : Nat) :
    squareSumTo n = squarePyramidalClosedForm n := by
  rw [squareSumTo_eq_squarePyramidal]
  exact squarePyramidal_closed_form n

theorem tetrahedral_zero :
    tetrahedralNumber 0 = 0 := by
  rfl

theorem tetrahedral_succ (n : Nat) :
    tetrahedralNumber (Nat.succ n) =
      tetrahedralNumber n + triangularNumber (Nat.succ n) := by
  rfl

theorem tetrahedral_eq_previous_add_triangular (n : Nat) :
    tetrahedralNumber n = tetrahedralNumber (n - 1) + triangularNumber n := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      exact tetrahedral_succ n

theorem squarePyramidal_tetrahedral_square_relation (n : Nat) :
    squarePyramidalNumber (Nat.succ n) =
      squarePyramidalNumber n +
        BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n) := by
  exact squarePyramidal_succ n

private theorem square_pyramid_tetra_rearrange (a b c d : Nat) :
    a = b + d ->
      (a + b) + (c + d) = (a + c) + a := by
  intro h
  rw [h]
  calc
    (b + d + b) + (c + d) = ((b + d) + b) + c + d := by
      rw [Nat.add_assoc ((b + d) + b) c d]
    _ = (b + d) + b + c + d := rfl
    _ = (b + d) + (b + c) + d := by
      rw [Nat.add_assoc (b + d) b c]
    _ = (b + d) + (c + b) + d := by
      rw [Nat.add_comm b c]
    _ = (b + d) + c + b + d := by
      rw [← Nat.add_assoc (b + d) c b]
    _ = ((b + d) + c) + (b + d) := by
      rw [Nat.add_assoc ((b + d) + c) b d]

theorem squarePyramidal_tetrahedral_relation (n : Nat) :
    squarePyramidalNumber n = tetrahedralNumber n + tetrahedralNumber (n - 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [squarePyramidal_succ]
      rw [ih]
      have sqTri :
          squareNumber (Nat.succ n) =
            triangularNumber (Nat.succ n) + triangularNumber n := by
        change BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n) =
          BEDC.Derived.PolygonalUp.triangularNumber (Nat.succ n) +
            BEDC.Derived.PolygonalUp.triangularNumber n
        rw [← BEDC.Derived.PolygonalUp.triangular_add_previous_eq_square (Nat.succ n)]
        rfl
      rw [sqTri]
      rw [Nat.succ_sub_one]
      rw [tetrahedral_succ]
      exact square_pyramid_tetra_rearrange
        (tetrahedralNumber n)
        (tetrahedralNumber (n - 1))
        (triangularNumber (Nat.succ n))
        (triangularNumber n)
        (tetrahedral_eq_previous_add_triangular n)

theorem cannonball_positive_value :
    squarePyramidalNumber 24 = 70 * 70 := by
  rfl

def CannonballWitness (n m : Nat) : Prop :=
  squarePyramidalNumber n = squareNumber m

def cannonballFiniteNontrivialSearchRow (n m : Nat) : Bool :=
  squarePyramidalNumber n == squareNumber m

theorem cannonball_24_70_witness :
    CannonballWitness 24 70 := by
  rfl

theorem cannonball_24_70_search_row :
    cannonballFiniteNontrivialSearchRow 24 70 = true := by
  rfl

theorem SquarePyramidalUp_constructive_export :
    squarePyramidalNumber 0 = 0 ∧
      (∀ n : Nat,
        squarePyramidalNumber (Nat.succ n) =
          squarePyramidalNumber n + squareNumber (Nat.succ n)) ∧
      (∀ n : Nat,
        6 * squarePyramidalNumber n =
          n * (n + 1) * (2 * n + 1)) ∧
      (∀ n : Nat,
        squarePyramidalNumber n =
          divSix (n * (n + 1) * (2 * n + 1))) ∧
      (∀ n : Nat,
        squarePyramidalNumber n =
          tetrahedralNumber n + tetrahedralNumber (n - 1)) ∧
      squarePyramidalNumber 24 = 70 * 70 ∧
      CannonballWitness 24 70 := by
  constructor
  · exact squarePyramidal_zero
  · constructor
    · intro n
      exact squarePyramidal_succ n
    · constructor
      · intro n
        exact squarePyramidal_closed_numerator n
      · constructor
        · intro n
          exact squarePyramidal_closed_form n
        · constructor
          · intro n
            exact squarePyramidal_tetrahedral_relation n
          · constructor
            · exact cannonball_positive_value
            · exact cannonball_24_70_witness

end BEDC.Derived.SquarePyramidalUp
