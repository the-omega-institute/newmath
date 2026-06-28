import BEDC.Derived.QBinomialUp
import BEDC.Derived.PolynomialUp.IntegerRing
import BEDC.Algebra.FiniteFold

namespace BEDC.Derived.GaussianBinomialUp

abbrev Poly : Type :=
  BEDC.Derived.QBinomialUp.Poly

abbrev gaussianBinomial (n k : Nat) : Poly :=
  BEDC.Derived.QBinomialUp.qBinomial n k

abbrev gaussianBinomialRectangle (k l : Nat) : Poly :=
  BEDC.Derived.QBinomialUp.qGaussian k l

abbrev polyZero : Poly :=
  BEDC.Derived.QBinomialUp.polyZero

abbrev polyOne : Poly :=
  BEDC.Derived.QBinomialUp.polyOne

abbrev polyAdd : Poly -> Poly -> Poly :=
  BEDC.Derived.QBinomialUp.polyAdd

abbrev qShift : Nat -> Poly -> Poly :=
  BEDC.Derived.QBinomialUp.qShift

abbrev polyCoeff : Nat -> Poly -> Nat :=
  BEDC.Derived.QBinomialUp.polyCoeff

abbrev polyEvalOne : Poly -> Nat :=
  BEDC.Derived.QBinomialUp.polyEvalOne

abbrev ordinaryBinomial (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

private def integerPolynomialRing :
    BEDC.Algebra.Rel.RelCommRing
      BEDC.Derived.PolynomialUp.Poly
      BEDC.Derived.PolynomialUp.PolyEq where
  zero := BEDC.Derived.PolynomialUp.polyZero
  one := BEDC.Derived.PolynomialUp.polyOne
  add := BEDC.Derived.PolynomialUp.polyAdd
  mul := BEDC.Derived.PolynomialUp.polyMul
  neg := BEDC.Derived.PolynomialUp.polyNeg
  refl := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.eq_refl
  symm := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.eq_symm
  trans := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.eq_trans
  add_congr := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.add_respects
  mul_congr := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.mul_respects
  neg_congr := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.neg_respects
  add_assoc := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.add_assoc
  add_comm := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.add_comm
  add_zero := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.add_zero
  zero_add := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.zero_add
  add_neg := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.add_neg
  neg_add := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.neg_add
  mul_assoc := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.mul_assoc
  mul_one := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.mul_one
  one_mul := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.one_mul
  mul_zero := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.mul_zero
  zero_mul := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.zero_mul
  left_distrib := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.left_distrib
  right_distrib := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.right_distrib
  mul_comm := BEDC.Derived.PolynomialUp.polynomial_comm_ring_laws.mul_comm

def qPowerIntegerPoly : Nat -> BEDC.Derived.PolynomialUp.Poly
  | 0 => BEDC.Derived.PolynomialUp.polyOne
  | Nat.succ n => BEDC.Derived.PolynomialUp.polyShift (qPowerIntegerPoly n)

def oneMinusQPowerIntegerPoly (m : Nat) : BEDC.Derived.PolynomialUp.Poly :=
  BEDC.Derived.PolynomialUp.polyAdd BEDC.Derived.PolynomialUp.polyOne
    (BEDC.Derived.PolynomialUp.polyNeg (qPowerIntegerPoly m))

def oneMinusQPowerNumeratorFactorsFrom :
    Nat -> Nat -> Nat -> List BEDC.Derived.PolynomialUp.Poly
  | _n, _offset, 0 => []
  | n, offset, Nat.succ width =>
      oneMinusQPowerIntegerPoly (n - offset) ::
        oneMinusQPowerNumeratorFactorsFrom n (Nat.succ offset) width

def oneMinusQPowerNumeratorFactors
    (n k : Nat) : List BEDC.Derived.PolynomialUp.Poly :=
  oneMinusQPowerNumeratorFactorsFrom n 0 k

def oneMinusQPowerDenominatorFactorsFrom :
    Nat -> Nat -> List BEDC.Derived.PolynomialUp.Poly
  | _i, 0 => []
  | i, Nat.succ width =>
      oneMinusQPowerIntegerPoly i ::
        oneMinusQPowerDenominatorFactorsFrom (Nat.succ i) width

def oneMinusQPowerDenominatorFactors
    (k : Nat) : List BEDC.Derived.PolynomialUp.Poly :=
  oneMinusQPowerDenominatorFactorsFrom 1 k

def integerPolyProduct :
    List BEDC.Derived.PolynomialUp.Poly -> BEDC.Derived.PolynomialUp.Poly :=
  BEDC.Algebra.FiniteFold.listProd integerPolynomialRing

structure ProductRatioBoundary where
  numerator : BEDC.Derived.PolynomialUp.Poly
  denominator : BEDC.Derived.PolynomialUp.Poly

def gaussianProductRatioBoundary (n k : Nat) : ProductRatioBoundary :=
  { numerator := integerPolyProduct (oneMinusQPowerNumeratorFactors n k)
    denominator := integerPolyProduct (oneMinusQPowerDenominatorFactors k) }

theorem gaussianBinomial_q_pascal (n k : Nat) :
    gaussianBinomial (Nat.succ n) (Nat.succ k) =
      polyAdd (gaussianBinomial n k)
        (qShift (Nat.succ k) (gaussianBinomial n (Nat.succ k))) := by
  exact BEDC.Derived.QBinomialUp.qBinomial_pascal n k

theorem gaussianBinomial_eval_one (n k : Nat) :
    polyEvalOne (gaussianBinomial n k) = ordinaryBinomial n k := by
  exact BEDC.Derived.QBinomialUp.qBinomial_evalOne n k

theorem gaussianBinomial_zero_right (n : Nat) :
    gaussianBinomial n 0 = polyOne := by
  exact BEDC.Derived.QBinomialUp.qBinomial_zero_right n

theorem gaussianBinomial_zero_left_succ (k : Nat) :
    gaussianBinomial 0 (Nat.succ k) = polyZero := by
  exact BEDC.Derived.QBinomialUp.qBinomial_zero_left_succ k

theorem gaussianBinomial_self (n : Nat) :
    gaussianBinomial n n = polyOne := by
  exact BEDC.Derived.QBinomialUp.qBinomial_self n

theorem gaussianBinomial_above (n extra : Nat) :
    gaussianBinomial n (Nat.succ (n + extra)) = polyZero := by
  exact BEDC.Derived.QBinomialUp.qBinomial_above n extra

theorem gaussianBinomialRectangle_pascal (k l : Nat) :
    gaussianBinomialRectangle (Nat.succ k) (Nat.succ l) =
      polyAdd (gaussianBinomialRectangle k (Nat.succ l))
        (qShift (Nat.succ k) (gaussianBinomialRectangle (Nat.succ k) l)) := by
  exact BEDC.Derived.QBinomialUp.qGaussian_pascal k l

theorem gaussianBinomialRectangle_zero_left (l : Nat) :
    gaussianBinomialRectangle 0 l = polyOne := by
  exact BEDC.Derived.QBinomialUp.qGaussian_zero_left l

theorem gaussianBinomialRectangle_zero_right (k : Nat) :
    gaussianBinomialRectangle k 0 = polyOne := by
  exact BEDC.Derived.QBinomialUp.qGaussian_zero_right k

theorem gaussianBinomialRectangle_from_binomial (k l : Nat) :
    gaussianBinomial (k + l) k = gaussianBinomialRectangle k l := by
  exact BEDC.Derived.QBinomialUp.qBinomial_from_qGaussian k l

theorem gaussianBinomial_complement_eval_one (k l : Nat) :
    polyEvalOne (gaussianBinomial (k + l) k) =
      ordinaryBinomial (k + l) l := by
  exact BEDC.Derived.QBinomialUp.qBinomial_evalOne_complement k l

theorem gaussianBinomial_zero_zero :
    gaussianBinomial 0 0 = polyOne := by
  rfl

theorem gaussianBinomial_one_zero :
    gaussianBinomial 1 0 = polyOne := by
  rfl

theorem gaussianBinomial_one_one :
    gaussianBinomial 1 1 = polyOne := by
  rfl

theorem gaussianBinomial_two_one :
    gaussianBinomial 2 1 = [0, 1] := by
  rfl

theorem gaussianBinomial_two_two :
    gaussianBinomial 2 2 = polyOne := by
  rfl

theorem gaussianBinomial_three_one :
    gaussianBinomial 3 1 = [0, 1, 2] := by
  rfl

theorem gaussianBinomial_three_two :
    gaussianBinomial 3 2 = [0, 1, 2] := by
  rfl

theorem gaussianProductRatioBoundary_zero_width (n : Nat) :
    gaussianProductRatioBoundary n 0 =
      { numerator := BEDC.Derived.PolynomialUp.polyOne
        denominator := BEDC.Derived.PolynomialUp.polyOne } := by
  rfl

theorem gaussianProductRatioBoundary_one_width_factors (n : Nat) :
    gaussianProductRatioBoundary n 1 =
      { numerator := integerPolyProduct [oneMinusQPowerIntegerPoly (n - 0)]
        denominator := integerPolyProduct [oneMinusQPowerIntegerPoly 1] } := by
  rfl

end BEDC.Derived.GaussianBinomialUp
