import BEDC.Algebra.FiniteFold
import BEDC.Derived.FactorialUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.PrimeUp.DividesClosure

namespace BEDC.Derived.HyperfactorialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp

def oneTo : Nat -> List Nat
  | 0 => []
  | Nat.succ n => oneTo n ++ [Nat.succ n]

def natListProduct : List Nat -> Nat
  | [] => 1
  | x :: xs => x * natListProduct xs

def factorialNat : Nat -> Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * factorialNat n

def hyperfactorialTerm (k : Nat) : Nat :=
  k ^ k

def hyperfactorial : Nat -> Nat
  | 0 => 1
  | Nat.succ n => hyperfactorial n * hyperfactorialTerm (Nat.succ n)

def superfactorial : Nat -> Nat
  | 0 => 1
  | Nat.succ n => superfactorial n * factorialNat (Nat.succ n)

def hyperfactorialTerms (n : Nat) : List Nat :=
  (oneTo n).map hyperfactorialTerm

def superfactorialTerms (n : Nat) : List Nat :=
  (oneTo n).map factorialNat

def NatDvdByFactor (d n : Nat) : Prop :=
  ∃ q : Nat, n = d * q

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zOfNat (n : Nat) : Z :=
  BEDC.Derived.RationalUp.intOfNat (natToUnary n) (natToUnary_unary n)

def hyperfactorialIntegerTerms (n : Nat) : List Z :=
  (oneTo n).map (fun k => zOfNat (hyperfactorialTerm k))

def superfactorialIntegerTerms (n : Nat) : List Z :=
  (oneTo n).map (fun k => zOfNat (factorialNat k))

def hyperfactorialInteger (n : Nat) : Z :=
  BEDC.Algebra.FiniteFold.listProd integerRing (hyperfactorialIntegerTerms n)

def superfactorialInteger (n : Nat) : Z :=
  BEDC.Algebra.FiniteFold.listProd integerRing (superfactorialIntegerTerms n)

def factorialHist (n : Nat) : BHist :=
  natToUnary (factorialNat n)

def hyperfactorialTermHist (n : Nat) : BHist :=
  natToUnary (hyperfactorialTerm n)

def hyperfactorialHist (n : Nat) : BHist :=
  natToUnary (hyperfactorial n)

def superfactorialHist (n : Nat) : BHist :=
  natToUnary (superfactorial n)

theorem oneTo_zero :
    oneTo 0 = [] := by
  rfl

theorem oneTo_succ (n : Nat) :
    oneTo (Nat.succ n) = oneTo n ++ [Nat.succ n] := by
  rfl

theorem natListProduct_nil :
    natListProduct [] = 1 := by
  rfl

theorem natListProduct_cons (x : Nat) (xs : List Nat) :
    natListProduct (x :: xs) = x * natListProduct xs := by
  rfl

theorem factorialNat_zero :
    factorialNat 0 = 1 := by
  rfl

theorem factorialNat_succ (n : Nat) :
    factorialNat (Nat.succ n) = Nat.succ n * factorialNat n := by
  rfl

theorem hyperfactorial_zero :
    hyperfactorial 0 = 1 := by
  rfl

theorem hyperfactorial_succ (n : Nat) :
    hyperfactorial (Nat.succ n) =
      hyperfactorial n * hyperfactorialTerm (Nat.succ n) := by
  rfl

theorem superfactorial_zero :
    superfactorial 0 = 1 := by
  rfl

theorem superfactorial_succ (n : Nat) :
    superfactorial (Nat.succ n) =
      superfactorial n * factorialNat (Nat.succ n) := by
  rfl

private theorem natToUnary_append (m n : Nat) :
    append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

private theorem natMulFn_natToUnary (m n : Nat) :
    natMulFn (natToUnary m) (natToUnary n) = natToUnary (m * n) := by
  induction n with
  | zero =>
      rw [Nat.mul_zero]
      rfl
  | succ n ih =>
      change append (natMulFn (natToUnary m) (natToUnary n)) (natToUnary m) =
        natToUnary (m * Nat.succ n)
      rw [ih]
      rw [natToUnary_append]
      rw [Nat.mul_succ]

theorem factorialNat_factorialUp_bridge (n : Nat) :
    BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n) =
      natToUnary (factorialNat n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change natMulFn (BHist.e1 (natToUnary n))
          (BEDC.Derived.FactorialUp.natFactorialFn (natToUnary n)) =
        natToUnary (Nat.succ n * factorialNat n)
      rw [ih]
      change natMulFn (natToUnary (Nat.succ n)) (natToUnary (factorialNat n)) =
        natToUnary (Nat.succ n * factorialNat n)
      exact natMulFn_natToUnary (Nat.succ n) (factorialNat n)

theorem factorialHist_unary (n : Nat) :
    UnaryHistory (factorialHist n) := by
  unfold factorialHist
  exact natToUnary_unary _

theorem hyperfactorialTermHist_unary (n : Nat) :
    UnaryHistory (hyperfactorialTermHist n) := by
  unfold hyperfactorialTermHist
  exact natToUnary_unary _

theorem hyperfactorialHist_unary (n : Nat) :
    UnaryHistory (hyperfactorialHist n) := by
  unfold hyperfactorialHist
  exact natToUnary_unary _

theorem superfactorialHist_unary (n : Nat) :
    UnaryHistory (superfactorialHist n) := by
  unfold superfactorialHist
  exact natToUnary_unary _

theorem hyperfactorial_last_power_nat_dvd (n : Nat) :
    NatDvdByFactor (hyperfactorialTerm (Nat.succ n))
      (hyperfactorial (Nat.succ n)) := by
  exact ⟨hyperfactorial n, by
    change hyperfactorial n * hyperfactorialTerm (Nat.succ n) =
      hyperfactorialTerm (Nat.succ n) * hyperfactorial n
    exact Nat.mul_comm (hyperfactorial n) (hyperfactorialTerm (Nat.succ n))⟩

theorem superfactorial_last_factorial_nat_dvd (n : Nat) :
    NatDvdByFactor (factorialNat (Nat.succ n))
      (superfactorial (Nat.succ n)) := by
  exact ⟨superfactorial n, by
    change superfactorial n * factorialNat (Nat.succ n) =
      factorialNat (Nat.succ n) * superfactorial n
    exact Nat.mul_comm (superfactorial n) (factorialNat (Nat.succ n))⟩

theorem hyperfactorial_last_power_divides (n : Nat) :
    NatDivides (hyperfactorialTermHist (Nat.succ n))
      (hyperfactorialHist (Nat.succ n)) := by
  have productRel :
      NatMul (hyperfactorialHist n) (hyperfactorialTermHist (Nat.succ n))
        (hyperfactorialHist (Nat.succ n)) := by
    unfold hyperfactorialHist hyperfactorialTermHist
    change NatMul (natToUnary (hyperfactorial n))
      (natToUnary (hyperfactorialTerm (Nat.succ n)))
      (natToUnary (hyperfactorial n * hyperfactorialTerm (Nat.succ n)))
    exact zpuNatToUnary_NatMul_rel _ _
  exact NatDivides_mul_right_closed
    (hyperfactorialHist_unary n)
    (hyperfactorialTermHist_unary (Nat.succ n))
    productRel

theorem superfactorial_last_factorial_divides (n : Nat) :
    NatDivides (factorialHist (Nat.succ n))
      (superfactorialHist (Nat.succ n)) := by
  have productRel :
      NatMul (superfactorialHist n) (factorialHist (Nat.succ n))
        (superfactorialHist (Nat.succ n)) := by
    unfold superfactorialHist factorialHist
    change NatMul (natToUnary (superfactorial n))
      (natToUnary (factorialNat (Nat.succ n)))
      (natToUnary (superfactorial n * factorialNat (Nat.succ n)))
    exact zpuNatToUnary_NatMul_rel _ _
  exact NatDivides_mul_right_closed
    (superfactorialHist_unary n)
    (factorialHist_unary (Nat.succ n))
    productRel

theorem hyperfactorial_small_zero :
    hyperfactorial 0 = 1 := by
  rfl

theorem hyperfactorial_small_one :
    hyperfactorial 1 = 1 := by
  rfl

theorem hyperfactorial_small_two :
    hyperfactorial 2 = 4 := by
  rfl

theorem hyperfactorial_small_three :
    hyperfactorial 3 = 108 := by
  rfl

theorem superfactorial_small_zero :
    superfactorial 0 = 1 := by
  rfl

theorem superfactorial_small_one :
    superfactorial 1 = 1 := by
  rfl

theorem superfactorial_small_two :
    superfactorial 2 = 2 := by
  rfl

theorem superfactorial_small_three :
    superfactorial 3 = 12 := by
  rfl

theorem superfactorial_small_four :
    superfactorial 4 = 288 := by
  rfl

theorem hyperfactorialInteger_zero :
    Zeq (hyperfactorialInteger 0) BEDC.Algebra.Rel.intOne := by
  exact integerRing.refl _

theorem superfactorialInteger_zero :
    Zeq (superfactorialInteger 0) BEDC.Algebra.Rel.intOne := by
  exact integerRing.refl _

end BEDC.Derived.HyperfactorialUp
