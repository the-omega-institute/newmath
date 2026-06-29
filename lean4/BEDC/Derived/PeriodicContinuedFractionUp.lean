import BEDC.Derived.ContFracUp
import BEDC.Derived.PellUp
import BEDC.Derived.QuadIntUp
import BEDC.Derived.RationalUp.Core

namespace BEDC.Derived.PeriodicContinuedFractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp

abbrev Z := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq := BEDC.Algebra.Rel.IntEq

private abbrev zring : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def zNat (n : Nat) : Z :=
  BEDC.Derived.RationalUp.intOfNat
    (natToUnary n) (natToUnary_unary n)

abbrev zZero : Z := BEDC.Algebra.Rel.intZero
abbrev zOne : Z := BEDC.Algebra.Rel.intOne
abbrev zTwo : Z := zNat 2
abbrev zThree : Z := zNat 3

structure PeriodicContinuedFraction (A : Type u) where
  period : List A
  periodNonempty : period = [] -> False

structure EventuallyPeriodicContinuedFraction (A : Type u) where
  preperiod : List A
  period : List A
  periodNonempty : period = [] -> False

def PeriodicContinuedFraction.toEventuallyPeriodic
    {A : Type u} (cf : PeriodicContinuedFraction A) :
    EventuallyPeriodicContinuedFraction A :=
  { preperiod := []
    period := cf.period
    periodNonempty := cf.periodNonempty }

-- 这是 sqrt(d) 连分数周期的有限数据面, 不声明全局算法已经闭合。
structure SqrtDPeriodicContinuedFraction where
  radicand : Z
  initial : Z
  period : List Z
  periodNonempty : period = [] -> False

def SqrtDPeriodicContinuedFraction.toEventuallyPeriodic
    (cf : SqrtDPeriodicContinuedFraction) :
    EventuallyPeriodicContinuedFraction Z :=
  { preperiod := [cf.initial]
    period := cf.period
    periodNonempty := cf.periodNonempty }

def periodicCoeffFrom {A : Type u} (fallback : A)
    (base cursor : List A) : Nat -> A
  | Nat.zero =>
      match cursor with
      | [] => fallback
      | a :: _tail => a
  | Nat.succ n =>
      match cursor with
      | [] => periodicCoeffFrom fallback base base n
      | _a :: tail =>
          match tail with
          | [] => periodicCoeffFrom fallback base base n
          | _b :: _rest => periodicCoeffFrom fallback base tail n

def periodicCoeff {A : Type u} (fallback : A)
    (period : List A) (n : Nat) : A :=
  periodicCoeffFrom fallback period period n

def eventuallyPeriodicCoeffFrom {A : Type u} (fallback : A) :
    List A -> List A -> Nat -> A
  | [], period, n => periodicCoeff fallback period n
  | a :: _tail, _period, Nat.zero => a
  | _a :: tail, period, Nat.succ n =>
      eventuallyPeriodicCoeffFrom fallback tail period n

def eventuallyPeriodicCoeff {A : Type u} (fallback : A)
    (cf : EventuallyPeriodicContinuedFraction A) (n : Nat) : A :=
  eventuallyPeriodicCoeffFrom fallback cf.preperiod cf.period n

theorem periodicCoeff_singleton {A : Type u} (a : A) (n : Nat) :
    periodicCoeff a [a] n = a := by
  unfold periodicCoeff
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold periodicCoeffFrom
      exact ih

-- Lagrange 的双向定理需要实数读回、整数部算法和有限状态重复论证。
-- 本文件只登记这个边界, 不把未闭合的 iff 当作定理导出。
inductive LagrangeDirection where
  | quadraticToEventuallyPeriodic
  | eventuallyPeriodicToQuadratic

inductive LagrangeDependency where
  | realReadback
  | integerPartAlgorithm
  | positiveDiscriminant
  | finiteStateRepeat

structure LagrangeBoundaryRow where
  direction : LagrangeDirection
  dependencies : List LagrangeDependency

def lagrangeQuadraticToPeriodicBoundaryRow : LagrangeBoundaryRow :=
  { direction := LagrangeDirection.quadraticToEventuallyPeriodic
    dependencies :=
      [ LagrangeDependency.realReadback,
        LagrangeDependency.integerPartAlgorithm,
        LagrangeDependency.positiveDiscriminant,
        LagrangeDependency.finiteStateRepeat ] }

def lagrangePeriodicToQuadraticBoundaryRow : LagrangeBoundaryRow :=
  { direction := LagrangeDirection.eventuallyPeriodicToQuadratic
    dependencies :=
      [ LagrangeDependency.realReadback,
        LagrangeDependency.positiveDiscriminant ] }

def lagrangeBoundaryRows : List LagrangeBoundaryRow :=
  [lagrangeQuadraticToPeriodicBoundaryRow, lagrangePeriodicToQuadraticBoundaryRow]

def sqrtTwoPeriodic : SqrtDPeriodicContinuedFraction :=
  { radicand := zTwo
    initial := zOne
    period := [zTwo]
    periodNonempty := by
      intro h
      cases h }

def sqrtTwoEventuallyPeriodic : EventuallyPeriodicContinuedFraction Z :=
  sqrtTwoPeriodic.toEventuallyPeriodic

def sqrtTwoCoeff (n : Nat) : Z :=
  eventuallyPeriodicCoeff zTwo sqrtTwoEventuallyPeriodic n

theorem sqrtTwo_coeff_zero :
    sqrtTwoCoeff 0 = zOne := by
  rfl

theorem sqrtTwo_coeff_tail (n : Nat) :
    sqrtTwoCoeff (Nat.succ n) = zTwo := by
  unfold sqrtTwoCoeff eventuallyPeriodicCoeff sqrtTwoEventuallyPeriodic
  unfold SqrtDPeriodicContinuedFraction.toEventuallyPeriodic sqrtTwoPeriodic
  change periodicCoeff zTwo [zTwo] n = zTwo
  exact periodicCoeff_singleton zTwo n

structure SqrtTwoCoeffWindow : Prop where
  coeff_zero : sqrtTwoCoeff 0 = zOne
  coeff_one : sqrtTwoCoeff 1 = zTwo
  coeff_two : sqrtTwoCoeff 2 = zTwo
  coeff_three : sqrtTwoCoeff 3 = zTwo

theorem sqrtTwo_coeff_window :
    SqrtTwoCoeffWindow := by
  exact
    { coeff_zero := sqrtTwo_coeff_zero
      coeff_one := sqrtTwo_coeff_tail 0
      coeff_two := sqrtTwo_coeff_tail 1
      coeff_three := sqrtTwo_coeff_tail 2 }

def sqrtTwoConvergentCoeffs : List Z :=
  [zOne, zTwo]

def sqrtTwoConvergentState : BEDC.Derived.ContFracUp.ConvergentState Z :=
  BEDC.Derived.ContFracUp.integerConvergentStateOfList sqrtTwoConvergentCoeffs

theorem sqrtTwo_convergent_numerator_three :
    Zeq sqrtTwoConvergentState.curr.p zThree := by
  unfold sqrtTwoConvergentState sqrtTwoConvergentCoeffs
  apply BEDC.Derived.RationalUp.IntPairClassifier_of_length_eq
  · exact BEDC.Derived.RationalUp.intToPair_carrier
      (BEDC.Derived.ContFracUp.integerConvergentStateOfList [zOne, zTwo]).curr.p
  · exact BEDC.Derived.RationalUp.intToPair_carrier zThree
  · rfl

theorem sqrtTwo_convergent_denominator_two :
    Zeq sqrtTwoConvergentState.curr.q zTwo := by
  unfold sqrtTwoConvergentState sqrtTwoConvergentCoeffs
  apply BEDC.Derived.RationalUp.IntPairClassifier_of_length_eq
  · exact BEDC.Derived.RationalUp.intToPair_carrier
      (BEDC.Derived.ContFracUp.integerConvergentStateOfList [zOne, zTwo]).curr.q
  · exact BEDC.Derived.RationalUp.intToPair_carrier zTwo
  · rfl

theorem sqrtTwo_convergent_det_one :
    Zeq
      (BEDC.Derived.ContFracUp.integerConvergentDet sqrtTwoConvergentState)
      zOne := by
  unfold sqrtTwoConvergentState sqrtTwoConvergentCoeffs
  exact BEDC.Derived.ContFracUp.integerContFracConvergents_det [zOne, zTwo]

theorem pell_three_two_for_two :
    BEDC.Derived.PellUp.IsPellSolution zTwo zThree zTwo := by
  unfold BEDC.Derived.PellUp.IsPellSolution
  apply BEDC.Derived.RationalUp.IntPairClassifier_of_length_eq
  · exact BEDC.Derived.RationalUp.intToPair_carrier
      (BEDC.Derived.PellUp.pellNorm zTwo zThree zTwo)
  · exact BEDC.Derived.RationalUp.intToPair_carrier zOne
  · rfl

theorem sqrtTwo_convergent_pell_solution :
    BEDC.Derived.PellUp.IsPellSolution zTwo
      sqrtTwoConvergentState.curr.p sqrtTwoConvergentState.curr.q := by
  exact BEDC.Derived.RationalUp.IntEq_trans
    (BEDC.Derived.PellUp.pellNorm_respects
      sqrtTwo_convergent_numerator_three
      sqrtTwo_convergent_denominator_two)
    pell_three_two_for_two

def sqrtTwoConvergentPellSolution :
    BEDC.Derived.PellUp.PellSolution zTwo :=
  { x := sqrtTwoConvergentState.curr.p
    y := sqrtTwoConvergentState.curr.q
    isPell := sqrtTwo_convergent_pell_solution }

theorem sqrtTwo_convergent_pell_coordinates :
    Zeq sqrtTwoConvergentPellSolution.x zThree ∧
      Zeq sqrtTwoConvergentPellSolution.y zTwo := by
  constructor
  · exact sqrtTwo_convergent_numerator_three
  · exact sqrtTwo_convergent_denominator_two

def sqrtTwoPellPower (n : Nat) :
    BEDC.Derived.PellUp.PellSolution zTwo :=
  BEDC.Derived.PellUp.pellSolutionGenerated
    zTwo zThree zTwo pell_three_two_for_two n

theorem sqrtTwoPellPower_isPell (n : Nat) :
    BEDC.Derived.PellUp.IsPellSolution zTwo
      (sqrtTwoPellPower n).x (sqrtTwoPellPower n).y := by
  exact BEDC.Derived.PellUp.pellSolutionGenerated_isPell
    zTwo zThree zTwo pell_three_two_for_two n

def sqrtTwoConvergentQuadInt : BEDC.Derived.QuadIntUp.QuadInt zTwo :=
  BEDC.Derived.QuadIntUp.quadMk zThree zTwo

theorem sqrtTwo_quadNorm_is_one :
    Zeq (BEDC.Derived.QuadIntUp.quadNorm sqrtTwoConvergentQuadInt) zOne :=
  pell_three_two_for_two

theorem quadOfInt_respects {d a b : Z} :
    Zeq a b ->
      BEDC.Derived.QuadIntUp.QuadEq
        (BEDC.Derived.QuadIntUp.quadOfInt (d := d) a)
        (BEDC.Derived.QuadIntUp.quadOfInt b) := by
  intro h
  constructor
  · exact h
  · exact zring.refl zZero

theorem sqrtTwo_quad_conj_norm_one :
    BEDC.Derived.QuadIntUp.QuadEq
      (BEDC.Derived.QuadIntUp.quadMul sqrtTwoConvergentQuadInt
        (BEDC.Derived.QuadIntUp.quadConj sqrtTwoConvergentQuadInt))
      (BEDC.Derived.QuadIntUp.quadOfInt (d := zTwo) zOne) := by
  exact BEDC.Derived.QuadIntUp.QuadEq_trans
    (BEDC.Derived.QuadIntUp.quadMul_conj_norm sqrtTwoConvergentQuadInt)
    (quadOfInt_respects sqrtTwo_quadNorm_is_one)

theorem sqrtTwo_sqrt_symbol_squares_to_two :
    BEDC.Derived.QuadIntUp.QuadEq
      (BEDC.Derived.QuadIntUp.quadMul
        (BEDC.Derived.QuadIntUp.quadSqrt (d := zTwo))
        BEDC.Derived.QuadIntUp.quadSqrt)
      (BEDC.Derived.QuadIntUp.quadOfInt zTwo) :=
  BEDC.Derived.QuadIntUp.quadSqrt_mul_self

end BEDC.Derived.PeriodicContinuedFractionUp
