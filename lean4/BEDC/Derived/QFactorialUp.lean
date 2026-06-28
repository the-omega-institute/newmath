import BEDC.Derived.QBinomialUp
import BEDC.Derived.PochhammerUp

namespace BEDC.Derived.QFactorialUp

abbrev Poly : Type :=
  BEDC.Derived.QBinomialUp.Poly

def polyZero : Poly :=
  BEDC.Derived.QBinomialUp.polyZero

def polyOne : Poly :=
  BEDC.Derived.QBinomialUp.polyOne

def polyAdd : Poly -> Poly -> Poly :=
  BEDC.Derived.QBinomialUp.polyAdd

def qShift : Nat -> Poly -> Poly :=
  BEDC.Derived.QBinomialUp.qShift

def polyMul : Poly -> Poly -> Poly :=
  BEDC.Derived.QBinomialUp.polyMul

def polyCoeff : Nat -> Poly -> Nat :=
  BEDC.Derived.QBinomialUp.polyCoeff

def polyEvalOne : Poly -> Nat :=
  BEDC.Derived.QBinomialUp.polyEvalOne

def qNat : Nat -> Poly :=
  BEDC.Derived.QBinomialUp.qNat

def qFactorial : Nat -> Poly :=
  BEDC.Derived.QBinomialUp.qFactorial

def factorialNat : Nat -> Nat :=
  BEDC.Derived.PochhammerUp.natFactorialCount

theorem qNat_zero :
    qNat 0 = polyZero := by
  rfl

theorem qNat_succ (n : Nat) :
    qNat (Nat.succ n) = polyAdd polyOne (qShift 1 (qNat n)) := by
  rfl

theorem qFactorial_zero :
    qFactorial 0 = polyOne := by
  rfl

theorem qFactorial_succ (n : Nat) :
    qFactorial (Nat.succ n) = polyMul (qFactorial n) (qNat (Nat.succ n)) := by
  rfl

theorem polyEvalOne_qShift (m : Nat) (p : Poly) :
    polyEvalOne (qShift m p) = polyEvalOne p :=
  BEDC.Derived.QBinomialUp.polyEvalOne_qShift m p

theorem polyEvalOne_add (p q : Poly) :
    polyEvalOne (polyAdd p q) = polyEvalOne p + polyEvalOne q :=
  BEDC.Derived.QBinomialUp.polyEvalOne_append p q

theorem qNat_evalOne (n : Nat) :
    polyEvalOne (qNat n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [qNat_succ]
      rw [polyEvalOne_add]
      rw [polyEvalOne_qShift]
      rw [ih]
      change 1 + n = n + 1
      exact Nat.add_comm 1 n

theorem polyEvalOne_mul (p q : Poly) :
    polyEvalOne (polyMul p q) = polyEvalOne p * polyEvalOne q := by
  induction p with
  | nil =>
      change 0 = 0 * polyEvalOne q
      exact (Nat.zero_mul (polyEvalOne q)).symm
  | cons e p ih =>
      change
        polyEvalOne (polyAdd (qShift e q) (polyMul p q)) =
          Nat.succ (polyEvalOne p) * polyEvalOne q
      rw [polyEvalOne_add]
      rw [polyEvalOne_qShift]
      rw [ih]
      rw [Nat.succ_mul]
      exact Nat.add_comm (polyEvalOne q) (polyEvalOne p * polyEvalOne q)

theorem qFactorial_evalOne_factorialNat (n : Nat) :
    polyEvalOne (qFactorial n) = factorialNat n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [qFactorial_succ]
      rw [polyEvalOne_mul]
      rw [ih]
      rw [qNat_evalOne]
      exact (BEDC.Derived.PochhammerUp.natFactorialCount_succ n).symm

end BEDC.Derived.QFactorialUp
