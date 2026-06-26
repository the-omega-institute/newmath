import BEDC.Algebra.FiniteFold
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.PolynomialUp.Calculus

namespace BEDC.Derived.SymmetricPolyUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq
abbrev Poly := BEDC.Derived.PolynomialUp.Poly

def integerRing : BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev integerZero : IntegerUp :=
  BEDC.Algebra.Rel.intZero

abbrev integerOne : IntegerUp :=
  BEDC.Algebra.Rel.intOne

abbrev integerAdd : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Algebra.Rel.IntAdd

abbrev integerMul : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Algebra.Rel.IntMul

abbrev integerNeg : IntegerUp -> IntegerUp :=
  BEDC.Algebra.Rel.IntNeg

private abbrev zRing : BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  integerRing

private abbrev zZero : IntegerUp :=
  integerZero

private abbrev zOne : IntegerUp :=
  integerOne

private abbrev zAdd : IntegerUp -> IntegerUp -> IntegerUp :=
  integerAdd

private abbrev zMul : IntegerUp -> IntegerUp -> IntegerUp :=
  integerMul

private abbrev zNeg : IntegerUp -> IntegerUp :=
  integerNeg

def productAll : List IntegerUp -> IntegerUp
  | [] => zOne
  | x :: xs => zMul x (productAll xs)

def sumAll : List IntegerUp -> IntegerUp
  | [] => zZero
  | x :: xs => zAdd x (sumAll xs)

def integerScalar : Nat -> IntegerUp
  | 0 => zZero
  | Nat.succ n => zAdd zOne (integerScalar n)

def integerPower (x : IntegerUp) : Nat -> IntegerUp
  | 0 => zOne
  | Nat.succ n => zMul x (integerPower x n)

def elementaryProducts (k : Nat) (xs : List IntegerUp) : List IntegerUp :=
  match k with
  | 0 => [zOne]
  | Nat.succ k =>
      match xs with
      | [] => []
      | x :: xs =>
          (elementaryProducts k xs).map (fun y => zMul x y) ++
            elementaryProducts (Nat.succ k) xs

def elementarySymmetric (k : Nat) (xs : List IntegerUp) : IntegerUp :=
  sumAll (elementaryProducts k xs)

def powerSum (k : Nat) (xs : List IntegerUp) : IntegerUp :=
  sumAll (xs.map (fun x => integerPower x k))

def scalarMul (n : Nat) (x : IntegerUp) : IntegerUp :=
  zMul (integerScalar n) x

def newtonOneLeft (xs : List IntegerUp) : IntegerUp :=
  zAdd (powerSum 1 xs) (zNeg (elementarySymmetric 1 xs))

def newtonTwoLeft (x y : IntegerUp) : IntegerUp :=
  zAdd (powerSum 2 [x, y])
    (zAdd
      (zNeg (zMul (elementarySymmetric 1 [x, y]) (powerSum 1 [x, y])))
      (scalarMul 2 (elementarySymmetric 2 [x, y])))

def linearFactor (root : IntegerUp) : Poly :=
  [zNeg root, zOne]

def quadraticFromRoots (x y : IntegerUp) : Poly :=
  BEDC.Derived.PolynomialUp.polyMul (linearFactor x) (linearFactor y)

def quadraticVietaCoefficients (x y : IntegerUp) : Poly :=
  [elementarySymmetric 2 [x, y], zNeg (elementarySymmetric 1 [x, y]), zOne]

private theorem elementaryProducts_zero (xs : List IntegerUp) :
    elementaryProducts 0 xs = [zOne] := by
  unfold elementaryProducts
  rfl

private theorem add_neg_of_eq {a b : IntegerUp} :
    IntEq a b -> IntEq (zAdd a (zNeg b)) zZero := by
  intro same
  exact zRing.trans
    (zRing.add_congr same (zRing.refl (zNeg b)))
    (zRing.add_neg b)

private theorem neg_sum_pair (x y : IntegerUp) :
    IntEq (zAdd (zNeg x) (zNeg y)) (zNeg (zAdd x y)) := by
  have zeroWitness :
      IntEq (zAdd (zAdd x y) (zAdd (zNeg x) (zNeg y))) zZero := by
    have rearranged :
        IntEq (zAdd (zAdd x y) (zAdd (zNeg x) (zNeg y)))
          (zAdd (zAdd x (zNeg x)) (zAdd y (zNeg y))) :=
      zRing.trans (zRing.add_assoc x y (zAdd (zNeg x) (zNeg y)))
        (zRing.trans
          (zRing.add_congr (zRing.refl x)
            (zRing.trans (zRing.symm (zRing.add_assoc y (zNeg x) (zNeg y)))
              (zRing.trans
                (zRing.add_congr (zRing.add_comm y (zNeg x)) (zRing.refl (zNeg y)))
                (zRing.add_assoc (zNeg x) y (zNeg y)))))
          (zRing.symm (zRing.add_assoc x (zNeg x) (zAdd y (zNeg y)))))
    have collapsed :
        IntEq (zAdd (zAdd x (zNeg x)) (zAdd y (zNeg y))) zZero :=
      zRing.trans
        (zRing.add_congr (zRing.add_neg x) (zRing.add_neg y))
        (zRing.zero_add zZero)
    exact zRing.trans rearranged collapsed
  exact zRing.symm (zRing.neg_eq_of_add_eq_zero zeroWitness)

private theorem elementarySymmetric_one_pair (x y : IntegerUp) :
    IntEq (elementarySymmetric 1 [x, y]) (zAdd x y) := by
  unfold elementarySymmetric elementaryProducts sumAll
  change IntEq (zAdd (zMul x zOne) (zAdd (zMul y zOne) zZero))
    (zAdd x y)
  exact zRing.add_congr (zRing.mul_one x)
    (zRing.trans
      (zRing.add_congr (zRing.mul_one y) (zRing.refl zZero))
      (zRing.add_zero y))

private theorem elementarySymmetric_two_pair (x y : IntegerUp) :
    IntEq (elementarySymmetric 2 [x, y]) (zMul x y) := by
  unfold elementarySymmetric elementaryProducts sumAll
  change IntEq (zAdd (zMul x (zMul y zOne)) zZero) (zMul x y)
  exact zRing.trans
    (zRing.add_congr
      (zRing.mul_congr (zRing.refl x) (zRing.mul_one y))
      (zRing.refl zZero))
    (zRing.add_zero (zMul x y))

theorem powerSum_one_eq_elementarySymmetric_one :
    ∀ xs : List IntegerUp, IntEq (powerSum 1 xs) (elementarySymmetric 1 xs)
  | [] =>
      zRing.refl zZero
  | x :: xs => by
      simp [powerSum, elementarySymmetric, elementaryProducts, integerPower, sumAll]
      exact zRing.add_congr (zRing.refl (zMul x zOne))
        (powerSum_one_eq_elementarySymmetric_one xs)

theorem newton_one (xs : List IntegerUp) :
    IntEq (newtonOneLeft xs) integerZero := by
  unfold newtonOneLeft
  exact add_neg_of_eq (powerSum_one_eq_elementarySymmetric_one xs)

private theorem linearFactor_eval_root (x : IntegerUp) :
    IntEq (BEDC.Derived.PolynomialUp.polyEval x (linearFactor x)) zZero := by
  unfold linearFactor BEDC.Derived.PolynomialUp.polyEval
  change IntEq (zAdd (zNeg x) (zMul x (zAdd zOne (zMul x zZero)))) zZero
  have tailOne :
      IntEq (zAdd zOne (zMul x zZero)) zOne :=
    zRing.trans
      (zRing.add_congr (zRing.refl zOne) (zRing.mul_zero x))
      (zRing.add_zero zOne)
  have productX :
      IntEq (zMul x (zAdd zOne (zMul x zZero))) x :=
    zRing.trans
      (zRing.mul_congr (zRing.refl x) tailOne)
      (zRing.mul_one x)
  exact zRing.trans
    (zRing.add_congr (zRing.refl (zNeg x)) productX)
    (zRing.neg_add x)

theorem vieta_quadratic_eval_zero_left (x y : IntegerUp) :
    IntEq
      (BEDC.Derived.PolynomialUp.polyEval x (quadraticFromRoots x y))
      integerZero := by
  unfold quadraticFromRoots
  have evalMul :=
    BEDC.Derived.PolynomialUp.polyEval_mul x (linearFactor x) (linearFactor y)
  have firstZero := linearFactor_eval_root x
  have productZero :
      IntEq
        (zMul
          (BEDC.Derived.PolynomialUp.polyEval x (linearFactor x))
          (BEDC.Derived.PolynomialUp.polyEval x (linearFactor y)))
        zZero :=
    zRing.trans
      (zRing.mul_congr firstZero
        (zRing.refl (BEDC.Derived.PolynomialUp.polyEval x (linearFactor y))))
      (zRing.zero_mul (BEDC.Derived.PolynomialUp.polyEval x (linearFactor y)))
  exact zRing.trans evalMul productZero

theorem vieta_quadratic_eval_zero_right (x y : IntegerUp) :
    IntEq
      (BEDC.Derived.PolynomialUp.polyEval y (quadraticFromRoots x y))
      integerZero := by
  unfold quadraticFromRoots
  have evalMul :=
    BEDC.Derived.PolynomialUp.polyEval_mul y (linearFactor x) (linearFactor y)
  have secondZero := linearFactor_eval_root y
  have productZero :
      IntEq
        (zMul
          (BEDC.Derived.PolynomialUp.polyEval y (linearFactor x))
          (BEDC.Derived.PolynomialUp.polyEval y (linearFactor y)))
        zZero :=
    zRing.trans
      (zRing.mul_congr
        (zRing.refl (BEDC.Derived.PolynomialUp.polyEval y (linearFactor x)))
        secondZero)
      (zRing.mul_zero (BEDC.Derived.PolynomialUp.polyEval y (linearFactor x)))
  exact zRing.trans evalMul productZero

theorem vieta_quadratic_coefficients (x y : IntegerUp) :
    BEDC.Derived.PolynomialUp.PolyEq
      (quadraticFromRoots x y)
      (quadraticVietaCoefficients x y) := by
  intro n
  cases n with
  | zero =>
      unfold quadraticFromRoots quadraticVietaCoefficients linearFactor
      change IntEq (zAdd (zMul (zNeg x) (zNeg y)) zZero)
        (elementarySymmetric 2 [x, y])
      exact zRing.trans
        (zRing.add_congr (zRing.neg_neg_mul_neg x y) (zRing.refl zZero))
        (zRing.trans (zRing.add_zero (zMul x y))
          (zRing.symm (elementarySymmetric_two_pair x y)))
  | succ n =>
      cases n with
      | zero =>
          unfold quadraticFromRoots quadraticVietaCoefficients linearFactor
          change IntEq (zAdd (zMul (zNeg x) zOne) (zMul zOne (zNeg y)))
            (zNeg (elementarySymmetric 1 [x, y]))
          exact zRing.trans
            (zRing.add_congr (zRing.mul_one (zNeg x)) (zRing.one_mul (zNeg y)))
            (zRing.trans (neg_sum_pair x y)
              (zRing.neg_congr (zRing.symm (elementarySymmetric_one_pair x y))))
      | succ n =>
          cases n with
          | zero =>
              unfold quadraticFromRoots quadraticVietaCoefficients linearFactor
              change IntEq (zMul zOne zOne) zOne
              exact zRing.one_mul zOne
          | succ n =>
              unfold quadraticFromRoots quadraticVietaCoefficients linearFactor
              change IntEq zZero zZero
              exact zRing.refl zZero

end BEDC.Derived.SymmetricPolyUp
