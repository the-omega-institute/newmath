import BEDC.Derived.BernoulliUp
import BEDC.FKernel.Hist

namespace BEDC.Derived.LegendrePolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.BernoulliUp

abbrev RawRat := BEDC.Derived.BernoulliUp.RawRat
abbrev RatNum := BEDC.Derived.RationalUp.RatNum
abbrev RawRatPoly := List RawRat

def rawRatOfNat (n : Nat) : RawRat :=
  rawMulNat n rawOne

def rawRatSub (x y : RawRat) : RawRat :=
  rawAdd x (rawNeg y)

def rawRatMul (x y : RawRat) : RawRat :=
  rawNormalize
    { num := x.num * y.num
      denMinusOne := x.den * y.den - 1 }

def rawRatDivBySucc (x : RawRat) (n : Nat) : RawRat :=
  rawScaleDen x n

def rawRatPolyZero : RawRatPoly :=
  []

def rawRatPolyOne : RawRatPoly :=
  [rawOne]

def rawRatPolyX : RawRatPoly :=
  [rawZero, rawOne]

def rawRatPolyAdd : RawRatPoly -> RawRatPoly -> RawRatPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => rawAdd a b :: rawRatPolyAdd p q

def rawRatPolyNeg : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawNeg a :: rawRatPolyNeg p

def rawRatPolySub (p q : RawRatPoly) : RawRatPoly :=
  rawRatPolyAdd p (rawRatPolyNeg q)

def rawRatPolyScale (a : RawRat) : RawRatPoly -> RawRatPoly
  | [] => []
  | b :: p => rawRatMul a b :: rawRatPolyScale a p

def rawRatPolyScaleNat (n : Nat) (p : RawRatPoly) : RawRatPoly :=
  rawRatPolyScale (rawRatOfNat n) p

def rawRatPolyDivBySucc (p : RawRatPoly) (n : Nat) : RawRatPoly :=
  rawRatPolyScale (rawRatDivBySucc rawOne n) p

def rawRatPolyMulX : RawRatPoly -> RawRatPoly
  | [] => []
  | a :: p => rawZero :: a :: p

def rawRatPolyConstant : RawRatPoly -> RawRat
  | [] => rawZero
  | a :: _ => a

def rawRatPolyTail : RawRatPoly -> RawRatPoly
  | [] => []
  | _ :: p => p

def rawRatPolyMulOnePlusU (p : RawRatPoly) : RawRatPoly :=
  rawRatPolyAdd p (rawRatPolyMulX p)

def rawRatPolyEval (x : RawRat) : RawRatPoly -> RawRat
  | [] => rawZero
  | a :: p => rawAdd a (rawRatMul x (rawRatPolyEval x p))

def rawLegendreStep (n : Nat) (current previous : RawRatPoly) : RawRatPoly :=
  rawRatPolyDivBySucc
    (rawRatPolySub
      (rawRatPolyScaleNat (2 * n + 1) (rawRatPolyMulX current))
      (rawRatPolyScaleNat n previous))
    n

-- 标准 x 系数递推面: P_0=1, P_1=x.
def rawLegendrePair : Nat -> RawRatPoly × RawRatPoly
  | 0 => (rawRatPolyOne, rawRatPolyX)
  | Nat.succ n =>
      let pair := rawLegendrePair n
      (pair.2, rawLegendreStep (Nat.succ n) pair.2 pair.1)

def rawLegendrePolynomial (n : Nat) : RawRatPoly :=
  (rawLegendrePair n).1

def rawOneAnchoredLegendreStep (n : Nat) (current previous : RawRatPoly) : RawRatPoly :=
  rawOne ::
    rawRatPolyDivBySucc
      (rawRatPolyTail
        (rawRatPolySub
          (rawRatPolyScaleNat (2 * n + 1) (rawRatPolyMulOnePlusU current))
          (rawRatPolyScaleNat n previous)))
      n

-- u=x-1 局部坐标读回面: 常数项即 P_n(1), 等价到 x 系数面不在本文件声称。
def rawOneAnchoredLegendrePair : Nat -> RawRatPoly × RawRatPoly
  | 0 => ([rawOne], [rawOne, rawOne])
  | Nat.succ n =>
      let pair := rawOneAnchoredLegendrePair n
      (pair.2, rawOneAnchoredLegendreStep (Nat.succ n) pair.2 pair.1)

def rawOneAnchoredLegendrePolynomial (n : Nat) : RawRatPoly :=
  (rawOneAnchoredLegendrePair n).1

def legendrePolynomial (n : Nat) : List RatNum :=
  (rawLegendrePolynomial n).map rawRatToRat

def legendrePolynomialUp (n : BHist) : List RatNum :=
  legendrePolynomial (bwordLength n)

def rawLegendreAtOne (n : Nat) : RawRat :=
  rawRatPolyEval rawOne (rawLegendrePolynomial n)

def rawOneAnchoredLegendreAtOne (n : Nat) : RawRat :=
  rawRatPolyConstant (rawOneAnchoredLegendrePolynomial n)

def legendreAtOne (n : Nat) : RatNum :=
  rawRatToRat (rawLegendreAtOne n)

def oneAnchoredLegendreAtOne (n : Nat) : RatNum :=
  rawRatToRat (rawOneAnchoredLegendreAtOne n)

def legendreAtOneUp (n : BHist) : RatNum :=
  legendreAtOne (bwordLength n)

def oneAnchoredLegendreAtOneUp (n : BHist) : RatNum :=
  oneAnchoredLegendreAtOne (bwordLength n)

theorem rawLegendrePolynomial_zero :
    rawLegendrePolynomial 0 = [rawOne] := by
  rfl

theorem rawLegendrePolynomial_one :
    rawLegendrePolynomial 1 = [rawZero, rawOne] := by
  rfl

theorem rawLegendrePolynomial_recurrence (n : Nat) :
    rawLegendrePolynomial (Nat.succ (Nat.succ n)) =
      rawLegendreStep (Nat.succ n)
        (rawLegendrePolynomial (Nat.succ n))
        (rawLegendrePolynomial n) := by
  rfl

theorem rawOneAnchoredLegendrePolynomial_recurrence (n : Nat) :
    rawOneAnchoredLegendrePolynomial (Nat.succ (Nat.succ n)) =
      rawOneAnchoredLegendreStep (Nat.succ n)
        (rawOneAnchoredLegendrePolynomial (Nat.succ n))
        (rawOneAnchoredLegendrePolynomial n) := by
  rfl

theorem legendrePolynomial_zero :
    legendrePolynomial 0 = [rawRatToRat rawOne] := by
  rfl

theorem legendrePolynomial_one :
    legendrePolynomial 1 = [rawRatToRat rawZero, rawRatToRat rawOne] := by
  rfl

def legendreHalf : RatNum :=
  ratOfIntOverNat 1 1

def legendreNegHalf : RatNum :=
  ratOfIntOverNat (-1) 1

def legendreThreeHalves : RatNum :=
  ratOfIntOverNat 3 1

def legendreNegThreeHalves : RatNum :=
  ratOfIntOverNat (-3) 1

def legendreFiveHalves : RatNum :=
  ratOfIntOverNat 5 1

theorem rawLegendrePolynomial_two :
    rawLegendrePolynomial 2 =
      [{ num := -1, denMinusOne := 1 },
        rawZero,
        { num := 3, denMinusOne := 1 }] := by
  rfl

theorem rawLegendrePolynomial_three :
    rawLegendrePolynomial 3 =
      [rawZero,
        { num := -3, denMinusOne := 1 },
        rawZero,
        { num := 5, denMinusOne := 1 }] := by
  rfl

theorem legendrePolynomial_two :
    legendrePolynomial 2 =
      [legendreNegHalf, rawRatToRat rawZero, legendreThreeHalves] := by
  rfl

theorem legendrePolynomial_three :
    legendrePolynomial 3 =
      [rawRatToRat rawZero, legendreNegThreeHalves,
        rawRatToRat rawZero, legendreFiveHalves] := by
  rfl

theorem rawLegendreAtOne_zero :
    rawLegendreAtOne 0 = rawOne := by
  rfl

theorem rawLegendreAtOne_one :
    rawLegendreAtOne 1 = rawOne := by
  rfl

theorem rawLegendreAtOne_two :
    rawLegendreAtOne 2 = rawOne := by
  rfl

theorem rawLegendreAtOne_three :
    rawLegendreAtOne 3 = rawOne := by
  rfl

theorem rawOneAnchoredLegendrePolynomial_constant_one (n : Nat) :
    rawRatPolyConstant (rawOneAnchoredLegendrePolynomial n) = rawOne := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      cases n with
      | zero =>
          rfl
      | succ _ =>
          rfl

theorem rawOneAnchoredLegendreAtOne_all (n : Nat) :
    rawOneAnchoredLegendreAtOne n = rawOne := by
  exact rawOneAnchoredLegendrePolynomial_constant_one n

theorem legendreAtOne_zero :
    BEDC.Derived.RationalUp.RatEq (legendreAtOne 0) BEDC.Derived.RationalUp.ratOne := by
  exact BEDC.Derived.RationalUp.RatEq_refl BEDC.Derived.RationalUp.ratOne

theorem legendreAtOne_one :
    BEDC.Derived.RationalUp.RatEq (legendreAtOne 1) BEDC.Derived.RationalUp.ratOne := by
  exact BEDC.Derived.RationalUp.RatEq_refl BEDC.Derived.RationalUp.ratOne

theorem legendreAtOne_two :
    BEDC.Derived.RationalUp.RatEq (legendreAtOne 2) BEDC.Derived.RationalUp.ratOne := by
  exact BEDC.Derived.RationalUp.RatEq_refl BEDC.Derived.RationalUp.ratOne

theorem legendreAtOne_three :
    BEDC.Derived.RationalUp.RatEq (legendreAtOne 3) BEDC.Derived.RationalUp.ratOne := by
  exact BEDC.Derived.RationalUp.RatEq_refl BEDC.Derived.RationalUp.ratOne

theorem oneAnchoredLegendreAtOne_all (n : Nat) :
    BEDC.Derived.RationalUp.RatEq
      (oneAnchoredLegendreAtOne n) BEDC.Derived.RationalUp.ratOne := by
  unfold oneAnchoredLegendreAtOne
  rw [rawOneAnchoredLegendreAtOne_all n]
  exact BEDC.Derived.RationalUp.RatEq_refl BEDC.Derived.RationalUp.ratOne

theorem legendrePolynomial_small_values :
    legendrePolynomial 0 = [rawRatToRat rawOne] ∧
      legendrePolynomial 1 = [rawRatToRat rawZero, rawRatToRat rawOne] ∧
      legendrePolynomial 2 =
        [legendreNegHalf, rawRatToRat rawZero, legendreThreeHalves] ∧
      legendrePolynomial 3 =
        [rawRatToRat rawZero, legendreNegThreeHalves,
          rawRatToRat rawZero, legendreFiveHalves] := by
  exact ⟨legendrePolynomial_zero,
    legendrePolynomial_one,
    legendrePolynomial_two,
    legendrePolynomial_three⟩

theorem legendreAtOne_small_window :
    BEDC.Derived.RationalUp.RatEq (legendreAtOne 0) BEDC.Derived.RationalUp.ratOne ∧
      BEDC.Derived.RationalUp.RatEq (legendreAtOne 1) BEDC.Derived.RationalUp.ratOne ∧
      BEDC.Derived.RationalUp.RatEq (legendreAtOne 2) BEDC.Derived.RationalUp.ratOne ∧
      BEDC.Derived.RationalUp.RatEq (legendreAtOne 3) BEDC.Derived.RationalUp.ratOne := by
  exact ⟨legendreAtOne_zero,
    legendreAtOne_one,
    legendreAtOne_two,
    legendreAtOne_three⟩

end BEDC.Derived.LegendrePolynomialUp
