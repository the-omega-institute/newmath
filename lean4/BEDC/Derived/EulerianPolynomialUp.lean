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

private theorem succ_sub_self_one (n : Nat) :
    Nat.succ n - n = 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Nat.succ (Nat.succ n) - Nat.succ n = 1
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

theorem eulerianPolynomial_right_boundary (n : Nat) :
    A (Nat.succ n) n = 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        Nat.succ (Nat.succ n) * A (Nat.succ n) (Nat.succ n) +
          (Nat.succ n - n) * A (Nat.succ n) n = 1
      rw [show A (Nat.succ n) (Nat.succ n) = 0 by
        exact BEDC.Derived.EulerianNumberUp.eulerian_succ_diagonal_zero n]
      rw [ih]
      rw [succ_sub_self_one n]
      rw [Nat.mul_zero, Nat.one_mul, Nat.zero_add]

private theorem zero_left_of_sum_zero {k q : Nat} (h : k + q = 0) :
    k = 0 := by
  cases k with
  | zero =>
      rfl
  | succ k =>
      rw [Nat.succ_add] at h
      cases h

private theorem zero_right_of_sum_zero {k q : Nat} (h : k + q = 0) :
    q = 0 := by
  induction k with
  | zero =>
      rw [Nat.zero_add] at h
      exact h
  | succ n ih =>
      rw [Nat.succ_add] at h
      cases h

private theorem sum_succ_right_inj {a b c : Nat} :
    a + Nat.succ b = Nat.succ c -> a + b = c := by
  intro h
  rw [Nat.add_succ] at h
  exact Nat.succ.inj h

private theorem succ_add_eq_from_sum {a b c : Nat} :
    Nat.succ a + b = Nat.succ c -> a + b = c := by
  intro h
  rw [Nat.succ_add] at h
  exact Nat.succ.inj h

private theorem succ_right_sum_from_split {a b c : Nat} :
    Nat.succ a + Nat.succ b = Nat.succ c -> a + Nat.succ b = c := by
  intro h
  rw [Nat.succ_add] at h
  exact Nat.succ.inj h

private theorem succ_left_sum_from_split {a b c : Nat} :
    Nat.succ a + Nat.succ b = Nat.succ c -> Nat.succ a + b = c := by
  intro h
  rw [Nat.add_succ] at h
  exact Nat.succ.inj h

private theorem succ_sum_left_sub_left (a b : Nat) :
    Nat.succ (a + Nat.succ b) - a = Nat.succ (Nat.succ b) := by
  induction a with
  | zero =>
      rw [Nat.zero_add, Nat.sub_zero]
  | succ a ih =>
      rw [Nat.succ_add]
      change Nat.succ (Nat.succ (a + Nat.succ b)) - Nat.succ a =
        Nat.succ (Nat.succ b)
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem succ_sum_left_sub_right (a b : Nat) :
    Nat.succ (Nat.succ a + b) - b = Nat.succ (Nat.succ a) := by
  induction b with
  | zero =>
      rw [Nat.add_zero, Nat.sub_zero]
  | succ b ih =>
      rw [Nat.add_succ]
      change Nat.succ (Nat.succ (Nat.succ a + b)) - Nat.succ b =
        Nat.succ (Nat.succ a)
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem succ_split_sub_left {a b c : Nat}
    (h : a + Nat.succ b = c) :
    Nat.succ c - a = Nat.succ (Nat.succ b) := by
  rw [← h]
  exact succ_sum_left_sub_left a b

private theorem succ_split_sub_right {a b c : Nat}
    (h : Nat.succ a + b = c) :
    Nat.succ c - b = Nat.succ (Nat.succ a) := by
  rw [← h]
  exact succ_sum_left_sub_right a b

theorem eulerianPolynomial_symmetry_split (n k q : Nat) :
    k + q = n -> A (Nat.succ n) k = A (Nat.succ n) q := by
  induction n generalizing k q with
  | zero =>
      intro sumEq
      have hk : k = 0 := zero_left_of_sum_zero sumEq
      have hq : q = 0 := zero_right_of_sum_zero sumEq
      rw [hk, hq]
  | succ n ih =>
      intro sumEq
      cases k with
      | zero =>
          rw [eulerianPolynomial_left_boundary (Nat.succ (Nat.succ n))]
          have hq : q = Nat.succ n := by
            change q = Nat.succ n
            rw [Nat.zero_add] at sumEq
            exact sumEq
          rw [hq]
          exact (eulerianPolynomial_right_boundary (Nat.succ n)).symm
      | succ k =>
          cases q with
          | zero =>
              have hk : Nat.succ k = Nat.succ n := by
                change Nat.succ k + 0 = Nat.succ n at sumEq
                rw [Nat.add_zero] at sumEq
                exact sumEq
              rw [← Nat.succ_eq_add_one k]
              rw [hk]
              exact eulerianPolynomial_right_boundary (Nat.succ n)
          | succ q =>
              have leftSplit : k + Nat.succ q = n :=
                succ_right_sum_from_split sumEq
              have rightSplit : Nat.succ k + q = n :=
                succ_left_sum_from_split sumEq
              change
                Nat.succ (Nat.succ k) * A (Nat.succ n) (Nat.succ k) +
                  (Nat.succ n - k) * A (Nat.succ n) k =
                Nat.succ (Nat.succ q) * A (Nat.succ n) (Nat.succ q) +
                  (Nat.succ n - q) * A (Nat.succ n) q
              rw [succ_split_sub_left leftSplit]
              rw [succ_split_sub_right rightSplit]
              rw [ih (Nat.succ k) q rightSplit]
              rw [ih k (Nat.succ q) leftSplit]
              exact Nat.add_comm
                (Nat.succ (Nat.succ k) * A (Nat.succ n) q)
                (Nat.succ (Nat.succ q) * A (Nat.succ n) (Nat.succ q))

theorem eulerianPolynomial_symmetry_sub (n k : Nat)
    (bounded : k + (n - k) = n) :
    A (Nat.succ n) k = A (Nat.succ n) (n - k) :=
  eulerianPolynomial_symmetry_split n k (n - k) bounded

theorem eulerianPolynomial_symmetry_classic (n k : Nat)
    (bounded : k + (n - 1 - k) = n - 1) :
    A n k = A n (n - 1 - k) := by
  cases n with
  | zero =>
      have hk : k = 0 := zero_left_of_sum_zero bounded
      rw [hk]
  | succ n =>
      exact eulerianPolynomial_symmetry_sub n k bounded

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
