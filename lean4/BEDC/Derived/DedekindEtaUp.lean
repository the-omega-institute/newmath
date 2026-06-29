import BEDC.Derived.PentagonalNumberTheoremUp
import BEDC.Derived.RationalUp

namespace BEDC.Derived.DedekindEtaUp

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq
abbrev RatNum := BEDC.Derived.RationalUp.RatNum
abbrev RatEq := BEDC.Derived.RationalUp.RatEq

private abbrev integerRing :
    BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def intZero : IntegerUp :=
  BEDC.Algebra.Rel.intZero

def intOne : IntegerUp :=
  BEDC.Algebra.Rel.intOne

def intSub (x y : IntegerUp) : IntegerUp :=
  integerRing.add x (integerRing.neg y)

def ratOfInt (z : IntegerUp) : RatNum :=
  BEDC.Derived.RationalUp.intToRat z

def ratZero : RatNum :=
  BEDC.Derived.RationalUp.ratZero

def ratOne : RatNum :=
  BEDC.Derived.RationalUp.ratOne

def ratSub (x y : RatNum) : RatNum :=
  BEDC.Derived.RationalUp.ratAdd x (BEDC.Derived.RationalUp.ratNeg y)

-- `q^(1/24)` 只作为外部形式因子记录；本文件只闭合有限 Euler 乘积。
inductive EtaFormalFactor : Type where
  | qPowOneOverTwentyFour : EtaFormalFactor

structure DedekindEtaFiniteTruncation where
  factorCount : Nat
  formalFactor : EtaFormalFactor

def dedekindEtaFiniteTruncation (factorCount : Nat) :
    DedekindEtaFiniteTruncation where
  factorCount := factorCount
  formalFactor := EtaFormalFactor.qPowOneOverTwentyFour

def etaEulerFactorCoeffInt (n degree : Nat) : IntegerUp :=
  if degree == 0 then
    intOne
  else if degree == n then
    integerRing.neg intOne
  else
    intZero

def etaEulerFactorCoeffRat (n degree : Nat) : RatNum :=
  ratOfInt (etaEulerFactorCoeffInt n degree)

-- 有限乘积 `∏_{n=1}^{factorCount} (1 - q^n)` 的整数系数。
def etaFiniteEulerProductCoeffInt (factorCount degree : Nat) : IntegerUp :=
  BEDC.Derived.PentagonalNumberTheoremUp.finiteEulerProductCoeff
    factorCount degree

-- 同一有限乘积的有理系数视图, 通过整数嵌入给出。
def dedekindEtaFiniteEulerProduct (factorCount degree : Nat) : RatNum :=
  ratOfInt (etaFiniteEulerProductCoeffInt factorCount degree)

def etaFiniteEulerProductCoeffRat (factorCount degree : Nat) : RatNum :=
  dedekindEtaFiniteEulerProduct factorCount degree

-- Euler 函数 `(q;q)_∞` 在本文件中只以有限截断系数出现。
def eulerFunctionFiniteProductCoeffInt (factorCount degree : Nat) : IntegerUp :=
  etaFiniteEulerProductCoeffInt factorCount degree

def eulerFunctionFiniteProductCoeffRat (factorCount degree : Nat) : RatNum :=
  ratOfInt (eulerFunctionFiniteProductCoeffInt factorCount degree)

def eulerPentagonalCoeffInt (degree fuel : Nat) : IntegerUp :=
  BEDC.Derived.PentagonalNumberTheoremUp.finiteEulerPentagonalSeriesCoeff
    degree fuel

def eulerPentagonalCoeffRat (degree fuel : Nat) : RatNum :=
  ratOfInt (eulerPentagonalCoeffInt degree fuel)

def etaFiniteCoeffWindowInt (factorCount maxDegree : Nat) :
    List IntegerUp :=
  BEDC.Derived.PentagonalNumberTheoremUp.finiteEulerProductCoeffWindow
    factorCount maxDegree

def etaPentagonalCoeffWindowInt (maxDegree pentagonalFuel : Nat) :
    List IntegerUp :=
  BEDC.Derived.PentagonalNumberTheoremUp.finiteEulerPentagonalSeriesCoeffWindow
    maxDegree pentagonalFuel

def etaFiniteCoeffWindowRat (factorCount maxDegree : Nat) :
    List RatNum :=
  (etaFiniteCoeffWindowInt factorCount maxDegree).map ratOfInt

def etaPentagonalCoeffWindowRat (maxDegree pentagonalFuel : Nat) :
    List RatNum :=
  (etaPentagonalCoeffWindowInt maxDegree pentagonalFuel).map ratOfInt

theorem dedekindEta_formal_factor_boundary (factorCount : Nat) :
    (dedekindEtaFiniteTruncation factorCount).formalFactor =
      EtaFormalFactor.qPowOneOverTwentyFour := by
  rfl

theorem etaEulerFactorCoeffInt_zero (n : Nat) :
    etaEulerFactorCoeffInt n 0 = intOne := by
  rfl

theorem etaEulerFactorCoeffRat_zero (n : Nat) :
    RatEq (etaEulerFactorCoeffRat n 0) ratOne := by
  exact BEDC.Derived.RationalUp.RatEq_refl _

theorem etaFiniteEulerProductCoeffInt_zero_degree :
    etaFiniteEulerProductCoeffInt 0 0 = intOne := by
  rfl

theorem etaFiniteEulerProductCoeffInt_zero_positive_degree (degree : Nat) :
    etaFiniteEulerProductCoeffInt 0 (Nat.succ degree) = intZero := by
  rfl

theorem etaFiniteEulerProductCoeffInt_step (last degree : Nat) :
    etaFiniteEulerProductCoeffInt (Nat.succ last) degree =
      intSub (etaFiniteEulerProductCoeffInt last degree)
        (if Nat.succ last <= degree then
          etaFiniteEulerProductCoeffInt last (degree - Nat.succ last)
        else
          intZero) := by
  rfl

theorem dedekindEtaFiniteEulerProduct_zero_degree :
    RatEq (dedekindEtaFiniteEulerProduct 0 0) ratOne := by
  exact BEDC.Derived.RationalUp.RatEq_refl _

theorem dedekindEtaFiniteEulerProduct_zero_positive_degree (degree : Nat) :
    RatEq (dedekindEtaFiniteEulerProduct 0 (Nat.succ degree)) ratZero := by
  exact BEDC.Derived.RationalUp.RatEq_refl _

theorem dedekindEtaFiniteEulerProduct_is_euler_function_finite_product
    (factorCount degree : Nat) :
    dedekindEtaFiniteEulerProduct factorCount degree =
      eulerFunctionFiniteProductCoeffRat factorCount degree := by
  rfl

def coefficientProductFactorCount : Nat :=
  BEDC.Derived.PentagonalNumberTheoremUp.coefficientProductFactorCount

def coefficientWindowMaxDegree : Nat :=
  BEDC.Derived.PentagonalNumberTheoremUp.coefficientWindowMaxDegree

def coefficientPentagonalFuel : Nat :=
  BEDC.Derived.PentagonalNumberTheoremUp.coefficientPentagonalFuel

structure EtaEulerSmallCoefficientWindow : Prop where
  coefficient_window :
    BEDC.Algebra.FiniteFold.ListPairwiseRel IntEq
      (etaFiniteCoeffWindowInt coefficientProductFactorCount
        coefficientWindowMaxDegree)
      (etaPentagonalCoeffWindowInt coefficientWindowMaxDegree
        coefficientPentagonalFuel)

theorem etaEulerProduct_pentagonal_coefficients_window_int :
    BEDC.Algebra.FiniteFold.ListPairwiseRel IntEq
      (etaFiniteCoeffWindowInt coefficientProductFactorCount
        coefficientWindowMaxDegree)
      (etaPentagonalCoeffWindowInt coefficientWindowMaxDegree
        coefficientPentagonalFuel) := by
  exact BEDC.Derived.PentagonalNumberTheoremUp.finiteEulerProduct_pentagonal_coefficients_window

theorem etaEulerProduct_small_coefficients_window :
    EtaEulerSmallCoefficientWindow := by
  exact {
    coefficient_window := etaEulerProduct_pentagonal_coefficients_window_int
  }

private theorem intToRat_congr {x y : IntegerUp} :
    IntEq x y -> RatEq (ratOfInt x) (ratOfInt y) := by
  intro same
  apply BEDC.Derived.RationalUp.ratEq_of_num_den_intEq
  · exact same
  · exact BEDC.Derived.RationalUp.IntEq_refl _

private theorem listPairwiseRel_intToRat_map :
    ∀ {xs ys : List IntegerUp},
      BEDC.Algebra.FiniteFold.ListPairwiseRel IntEq xs ys ->
        BEDC.Algebra.FiniteFold.ListPairwiseRel RatEq
          (xs.map ratOfInt) (ys.map ratOfInt)
  | _, _, BEDC.Algebra.FiniteFold.ListPairwiseRel.nil =>
      BEDC.Algebra.FiniteFold.ListPairwiseRel.nil
  | _, _, BEDC.Algebra.FiniteFold.ListPairwiseRel.cons head tail =>
      BEDC.Algebra.FiniteFold.ListPairwiseRel.cons
        (intToRat_congr head) (listPairwiseRel_intToRat_map tail)

theorem etaEulerProduct_pentagonal_coefficients_window_rat :
    BEDC.Algebra.FiniteFold.ListPairwiseRel RatEq
      (etaFiniteCoeffWindowRat coefficientProductFactorCount
        coefficientWindowMaxDegree)
      (etaPentagonalCoeffWindowRat coefficientWindowMaxDegree
        coefficientPentagonalFuel) := by
  exact listPairwiseRel_intToRat_map
    etaEulerProduct_pentagonal_coefficients_window_int

structure DedekindEtaFiniteExport : Prop where
  formal_factor_boundary :
    ∀ factorCount : Nat,
      (dedekindEtaFiniteTruncation factorCount).formalFactor =
        EtaFormalFactor.qPowOneOverTwentyFour
  finite_product_step :
    ∀ last degree : Nat,
      etaFiniteEulerProductCoeffInt (Nat.succ last) degree =
        intSub (etaFiniteEulerProductCoeffInt last degree)
          (if Nat.succ last <= degree then
            etaFiniteEulerProductCoeffInt last (degree - Nat.succ last)
          else
            intZero)
  pentagonal_window_int :
    BEDC.Algebra.FiniteFold.ListPairwiseRel IntEq
      (etaFiniteCoeffWindowInt coefficientProductFactorCount
        coefficientWindowMaxDegree)
      (etaPentagonalCoeffWindowInt coefficientWindowMaxDegree
        coefficientPentagonalFuel)
  pentagonal_window_rat :
    BEDC.Algebra.FiniteFold.ListPairwiseRel RatEq
      (etaFiniteCoeffWindowRat coefficientProductFactorCount
        coefficientWindowMaxDegree)
      (etaPentagonalCoeffWindowRat coefficientWindowMaxDegree
        coefficientPentagonalFuel)
  small_coefficients : EtaEulerSmallCoefficientWindow

theorem DedekindEtaUp_finite_export :
    DedekindEtaFiniteExport := by
  exact {
    formal_factor_boundary := dedekindEta_formal_factor_boundary
    finite_product_step := etaFiniteEulerProductCoeffInt_step
    pentagonal_window_int := etaEulerProduct_pentagonal_coefficients_window_int
    pentagonal_window_rat := etaEulerProduct_pentagonal_coefficients_window_rat
    small_coefficients := etaEulerProduct_small_coefficients_window
  }

end BEDC.Derived.DedekindEtaUp
