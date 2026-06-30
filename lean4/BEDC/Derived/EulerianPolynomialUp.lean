import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.EulerianNumberUp

namespace BEDC.Derived.EulerianPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

abbrev A (n k : Nat) : Nat :=
  BEDC.Derived.EulerianNumberUp.eulerianNumber n k

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def rowSum (n : Nat) : Nat :=
  BEDC.Derived.EulerianNumberUp.eulerianRowSum n

def worpitzkyNatSum (n x : Nat) : Nat :=
  BEDC.Derived.EulerianNumberUp.worpitzkyNatSum n x

def eulerianPolynomialCoefficientFn (n k : BHist) : BHist :=
  natToUnary (A (bwordLength n) (bwordLength k))

def eulerianPolynomialRowSumFn (n : BHist) : BHist :=
  natToUnary (rowSum (bwordLength n))

theorem eulerianPolynomial_zero_zero :
    A 0 0 = 1 := by
  exact BEDC.Derived.EulerianNumberUp.eulerian_zero_zero

theorem eulerianPolynomial_zero_succ (k : Nat) :
    A 0 (Nat.succ k) = 0 := by
  exact BEDC.Derived.EulerianNumberUp.eulerian_zero_succ k

theorem eulerianPolynomial_left_boundary (n : Nat) :
    A n 0 = 1 := by
  exact BEDC.Derived.EulerianNumberUp.eulerian_left_boundary n

theorem eulerianPolynomial_recurrence (n k : Nat) :
    A (Nat.succ n) (Nat.succ k) =
      Nat.succ (Nat.succ k) * A n (Nat.succ k) +
        (n - k) * A n k := by
  exact BEDC.Derived.EulerianNumberUp.eulerian_recurrence n k

theorem eulerianPolynomial_above (n extra : Nat) :
    A n (Nat.succ (n + extra)) = 0 := by
  exact BEDC.Derived.EulerianNumberUp.eulerian_succ_above n extra

theorem eulerianPolynomial_rowSum_factorial (n : Nat) :
    rowSum n = BEDC.Derived.PochhammerUp.natFactorialCount n := by
  exact BEDC.Derived.EulerianNumberUp.eulerianRowSum_eq_natFactorialCount n

theorem eulerianPolynomialRowSumFn_factorialFn (n : Nat) :
    eulerianPolynomialRowSumFn (natToUnary n) =
      BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n) := by
  unfold eulerianPolynomialRowSumFn rowSum
  change
    BEDC.Derived.EulerianNumberUp.eulerianRowSumFn (natToUnary n) =
      BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n)
  exact BEDC.Derived.EulerianNumberUp.eulerianRowSumFn_natFactorialFn n

theorem eulerianPolynomialCoefficientFn_unary_result (n k : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (eulerianPolynomialCoefficientFn n k) := by
  unfold eulerianPolynomialCoefficientFn
  exact natToUnary_unary _

theorem eulerianPolynomialRowSumFn_unary_result (n : BHist) :
    BEDC.FKernel.Unary.UnaryHistory (eulerianPolynomialRowSumFn n) := by
  unfold eulerianPolynomialRowSumFn
  exact natToUnary_unary _

theorem eulerianPolynomial_right_boundary (n : Nat) :
    A (Nat.succ n) n = 1 := by
  exact BEDC.Derived.EulerianNumberUp.eulerian_right_boundary n

theorem eulerianPolynomial_symmetry_split (n k q : Nat) :
    k + q = n -> A (Nat.succ n) k = A (Nat.succ n) q := by
  exact BEDC.Derived.EulerianNumberUp.eulerian_symmetry_split n k q

theorem eulerianPolynomial_symmetry_sub (n k : Nat)
    (bounded : k + (n - k) = n) :
    A (Nat.succ n) k = A (Nat.succ n) (n - k) :=
  BEDC.Derived.EulerianNumberUp.eulerian_symmetry_sub n k bounded

theorem eulerianPolynomial_symmetry_classic (n k : Nat)
    (bounded : k + (n - 1 - k) = n - 1) :
    A n k = A n (n - 1 - k) :=
  BEDC.Derived.EulerianNumberUp.eulerian_symmetry_classic n k bounded

theorem EulerianPolynomialUp_constructive_export :
    (∀ n : Nat, A n 0 = 1) ∧
      (∀ n k : Nat,
        A (Nat.succ n) (Nat.succ k) =
          Nat.succ (Nat.succ k) * A n (Nat.succ k) +
            (n - k) * A n k) ∧
      (∀ n : Nat,
        rowSum n = BEDC.Derived.PochhammerUp.natFactorialCount n) ∧
      (∀ n k q : Nat, k + q = n -> A (Nat.succ n) k = A (Nat.succ n) q) := by
  constructor
  · intro n
    exact eulerianPolynomial_left_boundary n
  · constructor
    · intro n k
      exact eulerianPolynomial_recurrence n k
    · constructor
      · intro n
        exact eulerianPolynomial_rowSum_factorial n
      · intro n k q
        exact eulerianPolynomial_symmetry_split n k q

end BEDC.Derived.EulerianPolynomialUp
