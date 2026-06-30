import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.FaulhaberUp
import BEDC.Derived.PolygonalUp

namespace BEDC.Derived.TetrahedralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev triangularNumber (n : Nat) : Nat :=
  BEDC.Derived.PolygonalUp.triangularNumber n

private theorem C_pascal (n k : Nat) :
    C (Nat.succ n) (Nat.succ k) = C n k + C n (Nat.succ k) :=
  BEDC.Derived.BinomialIdentitiesUp.binomial_pascal n k

private theorem C_zero_right (n : Nat) :
    C n 0 = 1 :=
  BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n

private theorem C_above (n extra : Nat) :
    C n (Nat.succ (n + extra)) = 0 :=
  BEDC.Derived.BinomialIdentitiesUp.binomial_above n extra

def tetrahedralNumber (n : Nat) : Nat :=
  C (n + 2) 3

abbrev T (n : Nat) : Nat :=
  triangularNumber n

abbrev Te (n : Nat) : Nat :=
  tetrahedralNumber n

def triangularPrefix : Nat -> Nat
  | 0 => triangularNumber 0
  | Nat.succ n =>
      triangularPrefix n + triangularNumber (Nat.succ n)

def squarePyramidalNumber : Nat -> Nat
  | 0 => 0
  | Nat.succ n => squarePyramidalNumber n + BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n)

def squarePrefix : Nat -> Nat
  | 0 => BEDC.Derived.PolygonalUp.squareNumber 0
  | Nat.succ n => squarePrefix n + BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n)

private theorem six_mul_as_three_two (x : Nat) :
    6 * x = 3 * (2 * x) := by
  change (3 * 2) * x = 3 * (2 * x)
  induction x with
  | zero =>
      rfl
  | succ x ih =>
      calc
        (3 * 2) * Nat.succ x = (3 * 2) * x + 3 * 2 := Nat.mul_succ (3 * 2) x
        _ = 3 * (2 * x) + 3 * 2 := congrArg (fun y => y + 3 * 2) ih
        _ = 3 * (2 * x + 2) := (Nat.mul_add 3 (2 * x) 2).symm
        _ = 3 * (2 * Nat.succ x) :=
            congrArg (fun y => 3 * y) (Nat.mul_succ 2 x).symm

private theorem nat_mul_assoc_pure (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun y => y + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) :=
            congrArg (fun y => a * y) (Nat.mul_succ b c).symm

private theorem nat_add_mul_pure (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
    _ = c * a + c * b := Nat.mul_add c a b
    _ = a * c + c * b := congrArg (fun y => y + c * b) (Nat.mul_comm c a)
    _ = a * c + b * c := congrArg (fun y => a * c + y) (Nat.mul_comm c b)

private theorem squareNumber_eq_pow_two (n : Nat) :
    BEDC.Derived.PolygonalUp.squareNumber n =
      BEDC.Derived.FaulhaberUp.powNat n 2 := by
  unfold BEDC.Derived.PolygonalUp.squareNumber
  rw [BEDC.Derived.FaulhaberUp.powNat_two]

private theorem tetrahedral_closed_step (n : Nat) :
    n * (n + 1) * (n + 2) + 3 * ((n + 1) * (n + 2)) =
      (n + 1) * (n + 2) * (n + 3) := by
  calc
    n * (n + 1) * (n + 2) + 3 * ((n + 1) * (n + 2)) =
        n * ((n + 1) * (n + 2)) + 3 * ((n + 1) * (n + 2)) := by
          exact congrArg
            (fun y => y + 3 * ((n + 1) * (n + 2)))
            (nat_mul_assoc_pure n (n + 1) (n + 2))
    _ = (n + 3) * ((n + 1) * (n + 2)) := by
          exact (nat_add_mul_pure n 3 ((n + 1) * (n + 2))).symm
    _ = ((n + 1) * (n + 2)) * (n + 3) := by
          exact Nat.mul_comm (n + 3) ((n + 1) * (n + 2))
    _ = (n + 1) * (n + 2) * (n + 3) := by
          rfl

def tetrahedralFn (n : BHist) : BHist :=
  natToUnary (tetrahedralNumber (bwordLength n))

def squarePyramidalFn (n : BHist) : BHist :=
  natToUnary (squarePyramidalNumber (bwordLength n))

theorem tetrahedralFn_unary (n : BHist) :
    UnaryHistory (tetrahedralFn n) := by
  unfold tetrahedralFn
  exact natToUnary_unary _

theorem squarePyramidalFn_unary (n : BHist) :
    UnaryHistory (squarePyramidalFn n) := by
  unfold squarePyramidalFn
  exact natToUnary_unary _

theorem tetrahedral_zero :
    tetrahedralNumber 0 = 0 := by
  rfl

theorem tetrahedral_one :
    tetrahedralNumber 1 = 1 := by
  rfl

theorem squarePyramidal_zero :
    squarePyramidalNumber 0 = 0 := by
  rfl

theorem squarePyramidal_one :
    squarePyramidalNumber 1 = 1 := by
  rfl

theorem triangularPrefix_succ (n : Nat) :
    triangularPrefix (Nat.succ n) =
      triangularPrefix n + BEDC.Derived.PolygonalUp.triangularNumber (Nat.succ n) := by
  rfl

theorem squarePyramidal_succ (n : Nat) :
    squarePyramidalNumber (Nat.succ n) =
      squarePyramidalNumber n + BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n) := by
  rfl

theorem squarePrefix_succ (n : Nat) :
    squarePrefix (Nat.succ n) =
      squarePrefix n + BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n) := by
  rfl

theorem squarePrefix_eq_squarePyramidal (n : Nat) :
    squarePrefix n = squarePyramidalNumber n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [squarePrefix_succ, squarePyramidal_succ, ih]

private theorem add_two_succ (n : Nat) :
    Nat.succ n + 2 = Nat.succ (n + 2) := by
  rw [Nat.succ_add]

private theorem three_is_succ_two :
    3 = Nat.succ 2 := by
  rfl

private theorem binomial_one_right (n : Nat) :
    C n 1 = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change C (Nat.succ n) (Nat.succ 0) = Nat.succ n
      rw [C_pascal n 0]
      rw [C_zero_right n]
      rw [ih]
      rw [Nat.add_comm]

private theorem triangular_eq_binomial_row (n : Nat) :
    BEDC.Derived.PolygonalUp.triangularNumber n = C (n + 1) 2 := by
  induction n with
  | zero =>
      change 0 = C 1 (Nat.succ (1 + 0))
      exact (C_above 1 0).symm
  | succ n ih =>
      rw [BEDC.Derived.PolygonalUp.triangular_succ]
      rw [ih]
      change C (n + 1) 2 + Nat.succ n =
        C (Nat.succ (n + 1)) 2
      change C (n + 1) 2 + Nat.succ n =
        C (Nat.succ (n + 1)) (Nat.succ 1)
      rw [C_pascal (n + 1) 1]
      rw [binomial_one_right]
      rw [Nat.add_comm]

theorem tetrahedral_eq_binomial (n : Nat) :
    tetrahedralNumber n = C (n + 2) 3 := by
  rfl

theorem tetrahedral_succ (n : Nat) :
    tetrahedralNumber (Nat.succ n) =
      tetrahedralNumber n + BEDC.Derived.PolygonalUp.triangularNumber (Nat.succ n) := by
  unfold tetrahedralNumber
  rw [add_two_succ]
  rw [three_is_succ_two]
  rw [triangular_eq_binomial_row (Nat.succ n)]
  rw [show Nat.succ n + 1 = n + 2 by
    rw [Nat.succ_eq_add_one]]
  rw [C_pascal (n + 2) 2]
  change C (n + 2) 2 + C (n + 2) 3 =
    C (n + 2) 3 + C (n + 2) 2
  rw [Nat.add_comm]

theorem tetrahedral_sum_triangular (n : Nat) :
    triangularPrefix n = tetrahedralNumber n := by
  exact
    Nat.strongRecOn (motive := fun n => triangularPrefix n = tetrahedralNumber n) n
      (fun n ih => by
        cases n with
        | zero =>
            rfl
        | succ n =>
            have prev : triangularPrefix n = tetrahedralNumber n :=
              ih n (Nat.lt_succ_self n)
            rw [triangularPrefix_succ, tetrahedral_succ, prev])

theorem squarePyramidal_sum_square (n : Nat) :
    squarePrefix n = squarePyramidalNumber n :=
  squarePrefix_eq_squarePyramidal n

theorem squarePyramidal_eq_powerSum (n : Nat) :
    squarePyramidalNumber n = BEDC.Derived.FaulhaberUp.powerSumNat 2 n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [squarePyramidal_succ]
      rw [BEDC.Derived.FaulhaberUp.powerSumNat_succ]
      rw [ih]
      rw [squareNumber_eq_pow_two]

theorem squarePyramidal_two_mul_step (n : Nat) :
    2 * squarePyramidalNumber (Nat.succ n) =
      2 * squarePyramidalNumber n +
        2 * BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n) := by
  rw [squarePyramidal_succ]
  exact Nat.mul_add 2 (squarePyramidalNumber n)
    (BEDC.Derived.PolygonalUp.squareNumber (Nat.succ n))

theorem tetrahedralFn_natToUnary (n : Nat) :
    tetrahedralFn (natToUnary n) = natToUnary (tetrahedralNumber n) := by
  unfold tetrahedralFn
  rw [natToUnary_length]

theorem squarePyramidalFn_natToUnary (n : Nat) :
    squarePyramidalFn (natToUnary n) = natToUnary (squarePyramidalNumber n) := by
  unfold squarePyramidalFn
  rw [natToUnary_length]

theorem tetrahedral_six_mul_closed (n : Nat) :
    6 * tetrahedralNumber n = n * (n + 1) * (n + 2) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [tetrahedral_succ]
      rw [Nat.left_distrib]
      rw [ih]
      rw [six_mul_as_three_two]
      rw [BEDC.Derived.PolygonalUp.triangular_double_eq_mul_succ]
      change n * (n + 1) * (n + 2) +
          3 * ((n + 1) * (n + 2)) =
        (n + 1) * (n + 2) * (n + 3)
      exact tetrahedral_closed_step n

theorem Te_eq_binomial (n : Nat) :
    Te n = C (n + 2) 3 :=
  tetrahedral_eq_binomial n

theorem T_eq_binomial (n : Nat) :
    T n = C (n + 1) 2 :=
  triangular_eq_binomial_row n

theorem Te_succ (n : Nat) :
    Te (Nat.succ n) = Te n + T (Nat.succ n) :=
  tetrahedral_succ n

theorem Te_sum_T (n : Nat) :
    triangularPrefix n = Te n :=
  tetrahedral_sum_triangular n

theorem Te_six_mul_closed (n : Nat) :
    6 * Te n = n * (n + 1) * (n + 2) :=
  tetrahedral_six_mul_closed n

theorem TetrahedralUp_formula_and_sum_export :
    (∀ n : Nat, Te n = C (n + 2) 3) ∧
      (∀ n : Nat, T n = C (n + 1) 2) ∧
      (∀ n : Nat, Te (Nat.succ n) = Te n + T (Nat.succ n)) ∧
      (∀ n : Nat, triangularPrefix n = Te n) ∧
      (∀ n : Nat, 6 * Te n = n * (n + 1) * (n + 2)) := by
  constructor
  · intro n
    exact Te_eq_binomial n
  · constructor
    · intro n
      exact T_eq_binomial n
    · constructor
      · intro n
        exact Te_succ n
      · constructor
        · intro n
          exact Te_sum_T n
        · intro n
          exact Te_six_mul_closed n

theorem squarePyramidal_six_mul_closed (n : Nat) :
    6 * squarePyramidalNumber n = n * (n + 1) * (2 * n + 1) := by
  rw [squarePyramidal_eq_powerSum]
  exact BEDC.Derived.FaulhaberUp.powerSum_two_closed_scaled n

theorem TetrahedralUp_constructive_export :
    tetrahedralNumber 0 = 0 ∧
      tetrahedralNumber 1 = 1 ∧
      squarePyramidalNumber 0 = 0 ∧
      squarePyramidalNumber 1 = 1 ∧
      (∀ n : Nat, tetrahedralNumber n = C (n + 2) 3) ∧
      (∀ n : Nat, triangularPrefix n = tetrahedralNumber n) ∧
      (∀ n : Nat, squarePrefix n = squarePyramidalNumber n) ∧
      (∀ n : Nat,
        BEDC.Derived.PolygonalUp.polygonalNumber 3 n =
          BEDC.Derived.PolygonalUp.triangularNumber n) ∧
      (∀ n : Nat,
        BEDC.Derived.PolygonalUp.polygonalNumber 4 n =
          BEDC.Derived.PolygonalUp.squareNumber n) ∧
      (∀ n : Nat,
        6 * tetrahedralNumber n = n * (n + 1) * (n + 2)) ∧
      (∀ n : Nat, Te n = C (n + 2) 3) ∧
      (∀ n : Nat, T n = C (n + 1) 2) ∧
      (∀ n : Nat, Te (Nat.succ n) = Te n + T (Nat.succ n)) ∧
      (∀ n : Nat, triangularPrefix n = Te n) ∧
      (∀ n : Nat, 6 * Te n = n * (n + 1) * (n + 2)) ∧
      (∀ n : Nat,
        6 * squarePyramidalNumber n = n * (n + 1) * (2 * n + 1)) := by
  constructor
  · exact tetrahedral_zero
  · constructor
    · exact tetrahedral_one
    · constructor
      · exact squarePyramidal_zero
      · constructor
        · exact squarePyramidal_one
        · constructor
          · intro n
            exact tetrahedral_eq_binomial n
          · constructor
            · intro n
              exact tetrahedral_sum_triangular n
            · constructor
              · intro n
                exact squarePyramidal_sum_square n
              · constructor
                · intro n
                  exact BEDC.Derived.PolygonalUp.polygonal_three_eq_triangular n
                · constructor
                  · intro n
                    exact BEDC.Derived.PolygonalUp.polygonal_four_eq_square n
                  · constructor
                    · intro n
                      exact tetrahedral_six_mul_closed n
                    · constructor
                      · intro n
                        exact Te_eq_binomial n
                      · constructor
                        · intro n
                          exact T_eq_binomial n
                        · constructor
                          · intro n
                            exact Te_succ n
                          · constructor
                            · intro n
                              exact Te_sum_T n
                            · constructor
                              · intro n
                                exact Te_six_mul_closed n
                              · intro n
                                exact squarePyramidal_six_mul_closed n

end BEDC.Derived.TetrahedralUp
