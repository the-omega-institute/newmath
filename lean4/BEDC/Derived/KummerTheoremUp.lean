import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.IntUp
import BEDC.Derived.PrimeUp
import BEDC.Derived.NatUp

namespace BEDC.Derived.KummerTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

/-!
Kummer 与 Legendre 的核心等式落在有限基数展开 trace 层。基数
`p = delta + 1` 的每一步记录商与余数，`valuation` 汇总后续商，
`digitSum` 汇总余数；证明不调用带 forbidden axiom 的除法库定理。
-/

inductive BaseExpansionTrace (delta : Nat) : Nat -> Nat -> Nat -> Prop where
  | zero : BaseExpansionTrace delta 0 0 0
  | digit (quotient valuation digitSum digit : Nat) :
      BaseExpansionTrace delta quotient valuation digitSum ->
        digit ≤ delta ->
        BaseExpansionTrace delta
          (Nat.succ delta * quotient + digit)
          (quotient + valuation)
          (digit + digitSum)

def FactorialPadicTrace (p delta n valuation digitSum : Nat) : Prop :=
  p = Nat.succ delta ∧ BaseExpansionTrace delta n valuation digitSum

def factorialPadicValuation (p delta n valuation digitSum : Nat) : Prop :=
  FactorialPadicTrace p delta n valuation digitSum

def basePDigitSum (p delta n valuation digitSum : Nat) : Prop :=
  FactorialPadicTrace p delta n valuation digitSum

def BinomialPadicValuationByLegendre
    (totalVal leftVal rightVal binomialVal : Nat) : Prop :=
  totalVal = leftVal + rightVal + binomialVal

def BaseAdditionCarryCount
    (delta leftDigitSum rightDigitSum totalDigitSum carryCount : Nat) : Prop :=
  leftDigitSum + rightDigitSum = totalDigitSum + delta * carryCount

def binomialCoefficientForKummer (m n : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C (m + n) m

def factorialPadicValuationUnary
    (_p _delta _n valuation _digitSum : Nat) : BHist :=
  BEDC.Derived.IntUp.natToUnary valuation

def basePDigitSumUnary
    (_p _delta _n _valuation digitSum : Nat) : BHist :=
  BEDC.Derived.IntUp.natToUnary digitSum

def carryCountUnary
    (_delta _leftDigitSum _rightDigitSum _totalDigitSum carryCount : Nat) : BHist :=
  BEDC.Derived.IntUp.natToUnary carryCount

theorem binomialCoefficientForKummer_unfold (m n : Nat) :
    binomialCoefficientForKummer m n =
      BEDC.Derived.BinomialIdentitiesUp.C (m + n) m := by
  rfl

theorem factorialPadicValuationUnary_result
    (p delta n valuation digitSum : Nat) :
    UnaryHistory
      (factorialPadicValuationUnary p delta n valuation digitSum) := by
  unfold factorialPadicValuationUnary
  exact BEDC.Derived.IntUp.natToUnary_unary valuation

theorem basePDigitSumUnary_result
    (p delta n valuation digitSum : Nat) :
    UnaryHistory (basePDigitSumUnary p delta n valuation digitSum) := by
  unfold basePDigitSumUnary
  exact BEDC.Derived.IntUp.natToUnary_unary digitSum

theorem carryCountUnary_result
    (delta leftDigitSum rightDigitSum totalDigitSum carryCount : Nat) :
    UnaryHistory
      (carryCountUnary delta leftDigitSum rightDigitSum totalDigitSum carryCount) := by
  unfold carryCountUnary
  exact BEDC.Derived.IntUp.natToUnary_unary carryCount

theorem baseExpansionTrace_legendre_clear :
    BaseExpansionTrace delta n valuation digitSum ->
      delta * valuation + digitSum = n := by
  intro trace
  induction trace with
  | zero =>
      rfl
  | digit q v ds d tail _digitBound ih =>
      calc
        delta * (q + v) + (d + ds) =
            (delta * q + delta * v) + (d + ds) := by
          rw [Nat.mul_add]
        _ = delta * q + (delta * v + (d + ds)) := by
          rw [Nat.add_assoc]
        _ = delta * q + (d + (delta * v + ds)) := by
          rw [Nat.add_left_comm (delta * v) d ds]
        _ = delta * q + (d + q) := by
          rw [ih]
        _ = delta * q + (q + d) := by
          rw [Nat.add_comm d q]
        _ = delta * q + q + d := by
          rw [Nat.add_assoc]
        _ = Nat.succ delta * q + d := by
          rw [Nat.succ_mul]

theorem factorialPadicValuation_legendre_floor :
    factorialPadicValuation p delta n valuation digitSum ->
      delta * valuation + digitSum = n := by
  intro trace
  exact baseExpansionTrace_legendre_clear trace.right

theorem legendre_factorial_floor_sum_trace :
    factorialPadicValuation p delta n valuation digitSum ->
      delta * valuation + digitSum = n := by
  exact factorialPadicValuation_legendre_floor

theorem basePDigitSum_legendre_clear :
    basePDigitSum p delta n valuation digitSum ->
      delta * valuation + digitSum = n := by
  intro trace
  exact baseExpansionTrace_legendre_clear trace.right

private theorem nat_add_right_cancel_pure {a b c : Nat} :
    a + c = b + c -> a = b := by
  induction c with
  | zero =>
      intro h
      rw [Nat.add_zero, Nat.add_zero] at h
      exact h
  | succ c ih =>
      intro h
      rw [Nat.add_succ, Nat.add_succ] at h
      exact ih (Nat.succ.inj h)

private theorem nat_add_left_cancel_pure {a b c : Nat} :
    a + b = a + c -> b = c := by
  intro h
  rw [Nat.add_comm a b, Nat.add_comm a c] at h
  exact nat_add_right_cancel_pure h

private theorem weighted_pair_sum
    (delta leftVal rightVal leftDigit rightDigit : Nat) :
    (delta * leftVal + leftDigit) +
        (delta * rightVal + rightDigit) =
      delta * (leftVal + rightVal) + (leftDigit + rightDigit) := by
  rw [Nat.mul_add]
  calc
    (delta * leftVal + leftDigit) +
        (delta * rightVal + rightDigit) =
      delta * leftVal + (leftDigit +
        (delta * rightVal + rightDigit)) := by
        rw [Nat.add_assoc]
    _ = delta * leftVal + (delta * rightVal +
        (leftDigit + rightDigit)) := by
        rw [Nat.add_left_comm leftDigit (delta * rightVal) rightDigit]
    _ = delta * leftVal + delta * rightVal +
        (leftDigit + rightDigit) := by
        rw [Nat.add_assoc]

private theorem weighted_tail_split
    (delta leftVal rightVal binomialVal totalDigit : Nat) :
    delta * (leftVal + rightVal + binomialVal) + totalDigit =
      delta * (leftVal + rightVal) + (totalDigit + delta * binomialVal) := by
  rw [Nat.mul_add]
  rw [Nat.add_assoc]
  rw [Nat.add_comm (delta * binomialVal) totalDigit]

private theorem weighted_cancel_tail
    {delta common left right tail : Nat} :
    common + (tail + delta * left) =
      common + (tail + delta * right) ->
        delta * left = delta * right := by
  intro h
  have tailEq : tail + delta * left = tail + delta * right :=
    nat_add_left_cancel_pure h
  exact nat_add_left_cancel_pure tailEq

theorem kummer_carry_characterization
    {p delta deltaTail m n leftVal leftDigitSum rightVal rightDigitSum
      totalVal totalDigitSum binomialVal carryCount : Nat}
    (delta_positive : delta = Nat.succ deltaTail)
    (leftTrace :
      factorialPadicValuation p delta m leftVal leftDigitSum)
    (rightTrace :
      factorialPadicValuation p delta n rightVal rightDigitSum)
    (totalTrace :
      factorialPadicValuation p delta (m + n) totalVal totalDigitSum)
    (binomialValByLegendre :
      BinomialPadicValuationByLegendre
        totalVal leftVal rightVal binomialVal)
    (carryTrace :
      BaseAdditionCarryCount
        delta leftDigitSum rightDigitSum totalDigitSum carryCount) :
      binomialVal = carryCount := by
  have leftLegendre :
      delta * leftVal + leftDigitSum = m :=
    factorialPadicValuation_legendre_floor leftTrace
  have rightLegendre :
      delta * rightVal + rightDigitSum = n :=
    factorialPadicValuation_legendre_floor rightTrace
  have totalLegendre :
      delta * totalVal + totalDigitSum = m + n :=
    factorialPadicValuation_legendre_floor totalTrace
  have fromParts :
      m + n =
        delta * (leftVal + rightVal) +
          (totalDigitSum + delta * carryCount) := by
    calc
      m + n =
          (delta * leftVal + leftDigitSum) +
            (delta * rightVal + rightDigitSum) := by
            rw [leftLegendre, rightLegendre]
      _ = delta * (leftVal + rightVal) +
            (leftDigitSum + rightDigitSum) := by
            exact weighted_pair_sum
              delta leftVal rightVal leftDigitSum rightDigitSum
      _ = delta * (leftVal + rightVal) +
            (totalDigitSum + delta * carryCount) := by
            rw [carryTrace]
  have fromTotal :
      m + n =
        delta * (leftVal + rightVal) +
          (totalDigitSum + delta * binomialVal) := by
    calc
      m + n = delta * totalVal + totalDigitSum := totalLegendre.symm
      _ = delta * (leftVal + rightVal + binomialVal) +
            totalDigitSum := by
            rw [binomialValByLegendre]
      _ = delta * (leftVal + rightVal) +
            (totalDigitSum + delta * binomialVal) := by
            exact weighted_tail_split
              delta leftVal rightVal binomialVal totalDigitSum
  have weightedEq :
      delta * binomialVal = delta * carryCount :=
    weighted_cancel_tail
      (common := delta * (leftVal + rightVal))
      (tail := totalDigitSum)
      (left := binomialVal)
      (right := carryCount)
      (fromTotal.symm.trans fromParts)
  rw [delta_positive] at weightedEq
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos deltaTail) weightedEq

theorem kummer_binomial_carry_count
    {p delta deltaTail m n leftVal leftDigitSum rightVal rightDigitSum
      totalVal totalDigitSum binomialVal carryCount : Nat}
    (delta_positive : delta = Nat.succ deltaTail)
    (leftTrace :
      factorialPadicValuation p delta m leftVal leftDigitSum)
    (rightTrace :
      factorialPadicValuation p delta n rightVal rightDigitSum)
    (totalTrace :
      factorialPadicValuation p delta (m + n) totalVal totalDigitSum)
    (binomialValByLegendre :
      BinomialPadicValuationByLegendre
        totalVal leftVal rightVal binomialVal)
    (carryTrace :
      BaseAdditionCarryCount
        delta leftDigitSum rightDigitSum totalDigitSum carryCount) :
      binomialVal = carryCount := by
  exact kummer_carry_characterization delta_positive leftTrace rightTrace
    totalTrace binomialValByLegendre carryTrace

end BEDC.Derived.KummerTheoremUp
