import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.PochhammerUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.AbelPolynomialUp

open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev zZero : Z := integerRing.zero
abbrev zOne : Z := integerRing.one
abbrev zAdd : Z -> Z -> Z := integerRing.add
abbrev zMul : Z -> Z -> Z := integerRing.mul
abbrev zNeg : Z -> Z := integerRing.neg
abbrev zSub : Z -> Z -> Z := integerRing.sub

def zNat (n : Nat) : Z :=
  BEDC.Derived.PochhammerUp.intOfNatStd n

def zPow (x : Z) : Nat -> Z
  | 0 => zOne
  | Nat.succ n => zMul (zPow x n) x

def abelShift (x a : Z) (n : Nat) : Z :=
  zSub x (zMul (zNat n) a)

def abelPolynomial (n : Nat) (x a : Z) : Z :=
  match n with
  | 0 => zOne
  | Nat.succ m => zMul x (zPow (abelShift x a (Nat.succ m)) m)

def rangeTo : Nat -> List Nat
  | 0 => [0]
  | Nat.succ n => rangeTo n ++ [Nat.succ n]

def abelBinomialTerm (n k : Nat) (x y a : Z) : Z :=
  zMul (zNat (BEDC.Derived.BinomialIdentitiesUp.C n k))
    (zMul (abelPolynomial k x a)
      (abelPolynomial (n - k) y a))

def abelBinomialSum (n : Nat) (x y a : Z) : Z :=
  listSum integerRing
    (List.map (fun k => abelBinomialTerm n k x y a) (rangeTo n))

def AbelBinomialTypeAt (n : Nat) (x y a : Z) : Prop :=
  Zeq (abelPolynomial n (zAdd x y) a) (abelBinomialSum n x y a)

theorem zPow_zero (x : Z) :
    Zeq (zPow x 0) zOne := by
  exact integerRing.refl zOne

theorem zPow_succ (x : Z) (n : Nat) :
    Zeq (zPow x (Nat.succ n)) (zMul (zPow x n) x) := by
  exact integerRing.refl (zPow x (Nat.succ n))

theorem abelShift_zero (x a : Z) :
    Zeq (abelShift x a 0) x := by
  exact integerRing.trans (integerRing.sub_eq_add_neg x (zMul (zNat 0) a))
    (integerRing.trans
      (integerRing.add_congr (integerRing.refl x)
        (integerRing.trans (integerRing.neg_congr (integerRing.zero_mul a))
          integerRing.neg_zero))
      (integerRing.add_zero x))

theorem abelPolynomial_zero (x a : Z) :
    Zeq (abelPolynomial 0 x a) zOne := by
  exact integerRing.refl zOne

theorem abelPolynomial_succ (m : Nat) (x a : Z) :
    Zeq (abelPolynomial (Nat.succ m) x a)
      (zMul x (zPow (abelShift x a (Nat.succ m)) m)) := by
  exact integerRing.refl (abelPolynomial (Nat.succ m) x a)

theorem abelPolynomial_one (x a : Z) :
    Zeq (abelPolynomial 1 x a) x := by
  exact integerRing.mul_one x

theorem abelPolynomial_two (x a : Z) :
    Zeq (abelPolynomial 2 x a)
      (zMul x (abelShift x a 2)) := by
  change Zeq (zMul x (zMul zOne (abelShift x a 2)))
    (zMul x (abelShift x a 2))
  exact integerRing.mul_congr (integerRing.refl x)
    (integerRing.one_mul (abelShift x a 2))

theorem rangeTo_zero :
    rangeTo 0 = [0] := by
  rfl

theorem rangeTo_succ (n : Nat) :
    rangeTo (Nat.succ n) = rangeTo n ++ [Nat.succ n] := by
  rfl

theorem abelBinomialSum_zero (x y a : Z) :
    Zeq (abelBinomialSum 0 x y a) zOne := by
  change Zeq
    (zAdd (abelBinomialTerm 0 0 x y a) zZero)
    zOne
  unfold abelBinomialTerm
  change Zeq
    (zAdd
      (zMul (zNat (BEDC.Derived.BinomialIdentitiesUp.C 0 0))
        (zMul (abelPolynomial 0 x a) (abelPolynomial 0 y a)))
      zZero)
    zOne
  exact integerRing.trans (integerRing.add_zero _)
    (integerRing.trans
      (integerRing.mul_congr (integerRing.refl (zNat (BEDC.Derived.BinomialIdentitiesUp.C 0 0)))
        (integerRing.trans
          (integerRing.mul_congr (abelPolynomial_zero x a) (abelPolynomial_zero y a))
          (integerRing.mul_one zOne)))
      (integerRing.one_mul zOne))

theorem abelBinomialType_zero (x y a : Z) :
    AbelBinomialTypeAt 0 x y a := by
  exact integerRing.trans (abelPolynomial_zero (zAdd x y) a)
    (integerRing.symm (abelBinomialSum_zero x y a))

theorem abelBinomialTerm_one_zero (x y a : Z) :
    Zeq (abelBinomialTerm 1 0 x y a) y := by
  unfold abelBinomialTerm
  change Zeq
    (zMul (zNat (BEDC.Derived.BinomialIdentitiesUp.C 1 0))
      (zMul (abelPolynomial 0 x a) (abelPolynomial 1 y a)))
    y
  exact integerRing.trans
    (integerRing.mul_congr (integerRing.refl (zNat (BEDC.Derived.BinomialIdentitiesUp.C 1 0)))
      (integerRing.trans
        (integerRing.mul_congr (abelPolynomial_zero x a) (abelPolynomial_one y a))
        (integerRing.one_mul y)))
    (integerRing.one_mul y)

theorem abelBinomialTerm_one_one (x y a : Z) :
    Zeq (abelBinomialTerm 1 1 x y a) x := by
  unfold abelBinomialTerm
  change Zeq
    (zMul (zNat (BEDC.Derived.BinomialIdentitiesUp.C 1 1))
      (zMul (abelPolynomial 1 x a) (abelPolynomial 0 y a)))
    x
  exact integerRing.trans
    (integerRing.mul_congr (integerRing.refl (zNat (BEDC.Derived.BinomialIdentitiesUp.C 1 1)))
      (integerRing.trans
        (integerRing.mul_congr (abelPolynomial_one x a) (abelPolynomial_zero y a))
        (integerRing.mul_one x)))
    (integerRing.one_mul x)

theorem abelBinomialSum_one (x y a : Z) :
    Zeq (abelBinomialSum 1 x y a) (zAdd x y) := by
  change Zeq
    (zAdd (abelBinomialTerm 1 0 x y a)
      (zAdd (abelBinomialTerm 1 1 x y a) zZero))
    (zAdd x y)
  exact integerRing.trans
    (integerRing.add_congr (abelBinomialTerm_one_zero x y a)
      (integerRing.trans
        (integerRing.add_congr (abelBinomialTerm_one_one x y a)
          (integerRing.refl zZero))
        (integerRing.add_zero x)))
    (integerRing.add_comm y x)

theorem abelBinomialType_one (x y a : Z) :
    AbelBinomialTypeAt 1 x y a := by
  exact integerRing.trans (abelPolynomial_one (zAdd x y) a)
    (integerRing.symm (abelBinomialSum_one x y a))

theorem abelBinomialType_small (x y a : Z) :
    AbelBinomialTypeAt 0 x y a ∧ AbelBinomialTypeAt 1 x y a := by
  constructor
  · exact abelBinomialType_zero x y a
  · exact abelBinomialType_one x y a

theorem abelPolynomial_zero_one_values (x a : Z) :
    Zeq (abelPolynomial 0 x a) zOne ∧
      Zeq (abelPolynomial 1 x a) x := by
  constructor
  · exact abelPolynomial_zero x a
  · exact abelPolynomial_one x a

theorem AbelPolynomialUp_constructive_export :
    AbelBinomialTypeAt 0 zZero zZero zZero ∧
      AbelBinomialTypeAt 1 zOne zZero zZero := by
  constructor
  · exact abelBinomialType_zero zZero zZero zZero
  · exact abelBinomialType_one zOne zZero zZero

end BEDC.Derived.AbelPolynomialUp
