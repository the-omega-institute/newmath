import BEDC.Derived.PolygonalUp

namespace BEDC.Derived.CenteredPolygonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev chooseTwo := BEDC.Derived.StirlingUp.chooseTwo

-- 中心多边形数以 `chooseTwo n` 表示公式中的 `n * (n - 1) / 2`。
def centeredPolygonalNumber (k n : Nat) : Nat :=
  k * chooseTwo n + 1

def centeredTriangularNumber (n : Nat) : Nat :=
  centeredPolygonalNumber 3 n

def centeredSquareNumber (n : Nat) : Nat :=
  centeredPolygonalNumber 4 n

def centeredHexagonalNumber (n : Nat) : Nat :=
  centeredPolygonalNumber 6 n

def centeredPolygonalFn (k n : BHist) : BHist :=
  natToUnary (centeredPolygonalNumber (bwordLength k) (bwordLength n))

def centeredTriangularFn (n : BHist) : BHist :=
  natToUnary (centeredTriangularNumber (bwordLength n))

def centeredSquareFn (n : BHist) : BHist :=
  natToUnary (centeredSquareNumber (bwordLength n))

def centeredHexagonalFn (n : BHist) : BHist :=
  natToUnary (centeredHexagonalNumber (bwordLength n))

theorem centeredPolygonal_formula (k n : Nat) :
    centeredPolygonalNumber k n = k * chooseTwo n + 1 := by
  rfl

theorem centeredTriangular_formula (n : Nat) :
    centeredTriangularNumber n = 3 * chooseTwo n + 1 := by
  rfl

theorem centeredSquare_formula (n : Nat) :
    centeredSquareNumber n = 4 * chooseTwo n + 1 := by
  rfl

theorem centeredHexagonal_formula (n : Nat) :
    centeredHexagonalNumber n = 6 * chooseTwo n + 1 := by
  rfl

theorem centeredPolygonalFn_unary (k n : BHist) :
    UnaryHistory (centeredPolygonalFn k n) := by
  unfold centeredPolygonalFn
  exact natToUnary_unary _

theorem centeredTriangularFn_unary (n : BHist) :
    UnaryHistory (centeredTriangularFn n) := by
  unfold centeredTriangularFn
  exact natToUnary_unary _

theorem centeredSquareFn_unary (n : BHist) :
    UnaryHistory (centeredSquareFn n) := by
  unfold centeredSquareFn
  exact natToUnary_unary _

theorem centeredHexagonalFn_unary (n : BHist) :
    UnaryHistory (centeredHexagonalFn n) := by
  unfold centeredHexagonalFn
  exact natToUnary_unary _

theorem centered_zero (k : Nat) :
    centeredPolygonalNumber k 0 = 1 := by
  rfl

theorem centered_one (k : Nat) :
    centeredPolygonalNumber k 1 = 1 := by
  rfl

private theorem centered_succ_rearrange (a b n : Nat) :
    (a + b) + Nat.succ n = (a + n) + (b + 1) := by
  rw [Nat.succ_eq_add_one]
  calc
    (a + b) + (n + 1) = a + (b + (n + 1)) :=
      Nat.add_assoc a b (n + 1)
    _ = a + ((b + n) + 1) := by
      rw [Nat.add_assoc b n 1]
    _ = a + ((n + b) + 1) := by
      rw [Nat.add_comm b n]
    _ = a + (n + (b + 1)) := by
      rw [Nat.add_assoc n b 1]
    _ = (a + n) + (b + 1) :=
      (Nat.add_assoc a n (b + 1)).symm

private theorem centered_increment_rearrange (a b c : Nat) :
    (a + b) + c = a + c + b := by
  rw [Nat.add_assoc a b c]
  rw [Nat.add_comm b c]
  rw [← Nat.add_assoc a c b]

private theorem centered_add_sub_left_cancel :
    ∀ a b : Nat, a + b - a = b
  | 0, b =>
      by
        rw [Nat.zero_add, Nat.sub_zero]
  | Nat.succ a, b =>
      by
        rw [Nat.succ_add]
        rw [Nat.succ_sub_succ_eq_sub]
        exact centered_add_sub_left_cancel a b

private theorem centered_succ_sub_one (n : Nat) :
    Nat.succ n - 1 = n := by
  rfl

theorem centeredPolygonal_succ (k n : Nat) :
    centeredPolygonalNumber k (Nat.succ n) =
      centeredPolygonalNumber k n + k * n := by
  unfold centeredPolygonalNumber
  rw [show chooseTwo (Nat.succ n) = chooseTwo n + n by
    change n + chooseTwo n = chooseTwo n + n
    exact Nat.add_comm n (chooseTwo n)]
  rw [Nat.mul_add]
  exact centered_increment_rearrange (k * chooseTwo n) (k * n) 1

theorem centeredPolygonal_succ_sub_previous (k n : Nat) :
    centeredPolygonalNumber k (Nat.succ n) -
        centeredPolygonalNumber k n =
      k * n := by
  rw [centeredPolygonal_succ]
  exact centered_add_sub_left_cancel (centeredPolygonalNumber k n) (k * n)

theorem centeredPolygonal_sub_previous_index (k n : Nat) :
    centeredPolygonalNumber k n -
        centeredPolygonalNumber k (n - 1) =
      k * (n - 1) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rw [centered_succ_sub_one]
      exact centeredPolygonal_succ_sub_previous k n

theorem centeredTriangular_succ (n : Nat) :
    centeredTriangularNumber (Nat.succ n) =
      centeredTriangularNumber n + 3 * n := by
  exact centeredPolygonal_succ 3 n

theorem centeredSquare_succ (n : Nat) :
    centeredSquareNumber (Nat.succ n) =
      centeredSquareNumber n + 4 * n := by
  exact centeredPolygonal_succ 4 n

theorem centeredHexagonal_succ (n : Nat) :
    centeredHexagonalNumber (Nat.succ n) =
      centeredHexagonalNumber n + 6 * n := by
  exact centeredPolygonal_succ 6 n

theorem centeredPolygonal_add_index_eq_polygonal_shift (k n : Nat) :
    centeredPolygonalNumber k (Nat.succ n) + n =
      BEDC.Derived.PolygonalUp.polygonalNumber (k + 2) (Nat.succ n) := by
  induction n with
  | zero =>
      unfold centeredPolygonalNumber
      change k * chooseTwo 1 + 1 + 0 =
        BEDC.Derived.PolygonalUp.polygonalNumber (k + 2) 1
      rfl
  | succ n ih =>
      calc
        centeredPolygonalNumber k (Nat.succ (Nat.succ n)) + Nat.succ n =
            (centeredPolygonalNumber k (Nat.succ n) + k * Nat.succ n) +
              Nat.succ n := by
                rw [centeredPolygonal_succ]
        _ = (centeredPolygonalNumber k (Nat.succ n) + n) +
              (k * Nat.succ n + 1) := by
                exact centered_succ_rearrange
                  (centeredPolygonalNumber k (Nat.succ n))
                  (k * Nat.succ n) n
        _ =
            BEDC.Derived.PolygonalUp.polygonalNumber (k + 2) (Nat.succ n) +
              (k * Nat.succ n + 1) := by
                rw [ih]
        _ =
            BEDC.Derived.PolygonalUp.polygonalNumber (k + 2) (Nat.succ n) +
              (((k + 2) - 2) * Nat.succ n + 1) := by
                rfl
        _ =
            BEDC.Derived.PolygonalUp.polygonalNumber (k + 2)
              (Nat.succ (Nat.succ n)) := by
                exact
                  (BEDC.Derived.PolygonalUp.polygonal_succ
                    (k + 2) (Nat.succ n)).symm

theorem centeredPolygonalFn_natToUnary (k n : Nat) :
    centeredPolygonalFn (natToUnary k) (natToUnary n) =
      natToUnary (centeredPolygonalNumber k n) := by
  unfold centeredPolygonalFn
  rw [natToUnary_length, natToUnary_length]

theorem centeredTriangularFn_natToUnary (n : Nat) :
    centeredTriangularFn (natToUnary n) =
      natToUnary (centeredTriangularNumber n) := by
  unfold centeredTriangularFn
  rw [natToUnary_length]

theorem centeredSquareFn_natToUnary (n : Nat) :
    centeredSquareFn (natToUnary n) =
      natToUnary (centeredSquareNumber n) := by
  unfold centeredSquareFn
  rw [natToUnary_length]

theorem centeredHexagonalFn_natToUnary (n : Nat) :
    centeredHexagonalFn (natToUnary n) =
      natToUnary (centeredHexagonalNumber n) := by
  unfold centeredHexagonalFn
  rw [natToUnary_length]

theorem CenteredPolygonalUp_constructive_export :
    (∀ k n : Nat,
      centeredPolygonalNumber k n = k * chooseTwo n + 1) ∧
    (∀ n : Nat,
      centeredTriangularNumber n = 3 * chooseTwo n + 1) ∧
    (∀ n : Nat,
      centeredSquareNumber n = 4 * chooseTwo n + 1) ∧
    (∀ n : Nat,
      centeredHexagonalNumber n = 6 * chooseTwo n + 1) ∧
    (∀ k n : Nat,
      centeredPolygonalNumber k (Nat.succ n) -
          centeredPolygonalNumber k n =
        k * n) ∧
    (∀ k n : Nat,
      centeredPolygonalNumber k n -
          centeredPolygonalNumber k (n - 1) =
        k * (n - 1)) ∧
    (∀ k n : Nat,
      centeredPolygonalNumber k (Nat.succ n) + n =
        BEDC.Derived.PolygonalUp.polygonalNumber (k + 2) (Nat.succ n)) := by
  constructor
  · intro k n
    exact centeredPolygonal_formula k n
  · constructor
    · intro n
      exact centeredTriangular_formula n
    · constructor
      · intro n
        exact centeredSquare_formula n
      · constructor
        · intro n
          exact centeredHexagonal_formula n
        · constructor
          · intro k n
            exact centeredPolygonal_succ_sub_previous k n
          · constructor
            · intro k n
              exact centeredPolygonal_sub_previous_index k n
            · intro k n
              exact centeredPolygonal_add_index_eq_polygonal_shift k n

end BEDC.Derived.CenteredPolygonalUp
