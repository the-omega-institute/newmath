import BEDC.Algebra.FiniteFold
import BEDC.Derived.BellNumberUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.DobinskiFiniteUp
import BEDC.Derived.PochhammerUp
import BEDC.Derived.StirlingUp

namespace BEDC.Derived.StirlingSecondCompleteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

-- 范围: 下方导出定理覆盖递归式、Bell 行和定义、`k = 0, 1`
-- 两列的交错和配平, 以及 `n = 0, 1, 2` 三个次数的下降阶乘展开。
-- 它不把全列交错和配平或全次数下降阶乘展开命名为已验证定理。

abbrev stirlingSecond : Nat -> Nat -> Nat :=
  BEDC.Derived.StirlingUp.stirlingSecond

abbrev bellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumber

abbrev bellPrefix : Nat -> Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellStirlingPrefix

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

abbrev factorialCount (n : Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natFactorialCount n

abbrev inclusiveRange : Nat -> List Nat :=
  BEDC.Derived.DobinskiFiniteUp.inclusiveRange

abbrev listNatSum (f : Nat -> Nat) : List Nat -> Nat :=
  BEDC.Derived.DobinskiFiniteUp.listNatSum f

-- `true` 标记 `sum_j (-1)^j C(k,j)(k-j)^n` 中的正号槽位。
def explicitPositiveSlot : Nat -> Bool
  | 0 => true
  | Nat.succ j =>
      match explicitPositiveSlot j with
      | true => false
      | false => true

def explicitPowerTerm (n k j : Nat) : Nat :=
  C k j * (k - j) ^ n

def explicitPowerPositiveTerm (n k j : Nat) : Nat :=
  match explicitPositiveSlot j with
  | true => explicitPowerTerm n k j
  | false => 0

def explicitPowerNegativeTerm (n k j : Nat) : Nat :=
  match explicitPositiveSlot j with
  | true => 0
  | false => explicitPowerTerm n k j

def explicitPowerPositiveSum (n k : Nat) : Nat :=
  finiteNatSum (explicitPowerPositiveTerm n k) k

def explicitPowerNegativeSum (n k : Nat) : Nat :=
  finiteNatSum (explicitPowerNegativeTerm n k) k

def explicitFormulaBalance (n k : Nat) : Prop :=
  factorialCount k * stirlingSecond n k + explicitPowerNegativeSum n k =
    explicitPowerPositiveSum n k

def fallingFactorial (x : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ k => fallingFactorial x k * (x - k)

def fallingExpansionPrefix (x n : Nat) : Nat -> Nat
  | 0 => stirlingSecond n 0 * fallingFactorial x 0
  | Nat.succ k =>
      fallingExpansionPrefix x n k +
        stirlingSecond n (Nat.succ k) * fallingFactorial x (Nat.succ k)

def fallingExpansion (x n : Nat) : Nat :=
  fallingExpansionPrefix x n n

def stirlingSecondFn (n k : BHist) : BHist :=
  natToUnary (stirlingSecond (bwordLength n) (bwordLength k))

def bellNumberFn (n : BHist) : BHist :=
  natToUnary (bellNumber (bwordLength n))

theorem stirlingSecond_zero_zero :
    stirlingSecond 0 0 = 1 := by
  exact BEDC.Derived.StirlingUp.stirlingSecond_zero_zero

theorem stirlingSecond_zero_succ (k : Nat) :
    stirlingSecond 0 (Nat.succ k) = 0 := by
  exact BEDC.Derived.StirlingUp.stirlingSecond_zero_succ k

theorem stirlingSecond_succ_zero (n : Nat) :
    stirlingSecond (Nat.succ n) 0 = 0 := by
  exact BEDC.Derived.StirlingUp.stirlingSecond_succ_zero n

theorem stirlingSecond_recurrence (n k : Nat) :
    stirlingSecond (Nat.succ n) (Nat.succ k) =
      Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k := by
  exact BEDC.Derived.StirlingUp.stirlingSecond_recurrence n k

theorem stirlingSecond_self (n : Nat) :
    stirlingSecond n n = 1 := by
  exact BEDC.Derived.StirlingUp.stirlingSecond_self n

theorem stirlingSecond_above (n extra : Nat) :
    stirlingSecond n (Nat.succ (n + extra)) = 0 := by
  exact BEDC.Derived.StirlingUp.stirlingSecond_above n extra

theorem bellPrefix_zero (n : Nat) :
    bellPrefix n 0 = stirlingSecond n 0 := by
  rfl

theorem bellPrefix_succ (n k : Nat) :
    bellPrefix n (Nat.succ k) =
      bellPrefix n k + stirlingSecond n (Nat.succ k) := by
  rfl

theorem bellNumber_sum_definition (n : Nat) :
    bellNumber n = bellPrefix n n := by
  rfl

theorem stirlingSecond_sum_eq_bellNumber (n : Nat) :
    bellPrefix n n = bellNumber n := by
  rfl

theorem bellNumber_list_stirling_sum (n : Nat) :
    bellNumber n = listNatSum (stirlingSecond n) (inclusiveRange n) := by
  exact BEDC.Derived.DobinskiFiniteUp.bellNumber_list_stirling_sum n

theorem bellNumber_matches_StirlingUp (n : Nat) :
    bellNumber n = BEDC.Derived.StirlingUp.bellNumber n := by
  exact BEDC.Derived.BellNumberUp.bellNumber_matches_StirlingUp n

theorem explicitPositiveSlot_zero :
    explicitPositiveSlot 0 = true := by
  rfl

theorem explicitPositiveSlot_succ (j : Nat) :
    explicitPositiveSlot (Nat.succ j) =
      match explicitPositiveSlot j with
      | true => false
      | false => true := by
  rfl

theorem explicitPowerTerm_zero_column_zero :
    explicitPowerTerm 0 0 0 = 1 := by
  rfl

theorem explicitPowerPositiveSum_zero_zero :
    explicitPowerPositiveSum 0 0 = 1 := by
  rfl

theorem explicitPowerNegativeSum_zero_zero :
    explicitPowerNegativeSum 0 0 = 0 := by
  rfl

theorem explicitFormulaBalance_zero_zero :
    explicitFormulaBalance 0 0 := by
  rfl

theorem explicitPowerTerm_succ_zero_column_zero (n : Nat) :
    explicitPowerTerm (Nat.succ n) 0 0 = 0 := by
  rfl

theorem explicitPowerPositiveSum_succ_zero_column (n : Nat) :
    explicitPowerPositiveSum (Nat.succ n) 0 = 0 := by
  rfl

theorem explicitPowerNegativeSum_succ_zero_column (n : Nat) :
    explicitPowerNegativeSum (Nat.succ n) 0 = 0 := by
  rfl

theorem explicitFormulaBalance_succ_zero_column (n : Nat) :
    explicitFormulaBalance (Nat.succ n) 0 := by
  rfl

theorem explicitFormulaBalance_zero_column (n : Nat) :
    explicitFormulaBalance n 0 := by
  cases n with
  | zero =>
      exact explicitFormulaBalance_zero_zero
  | succ n =>
      exact explicitFormulaBalance_succ_zero_column n

theorem explicitPowerPositiveSum_zero_one :
    explicitPowerPositiveSum 0 1 = 1 := by
  rfl

theorem explicitPowerNegativeSum_zero_one :
    explicitPowerNegativeSum 0 1 = 1 := by
  rfl

theorem explicitFormulaBalance_zero_one :
    explicitFormulaBalance 0 1 := by
  rfl

theorem explicitPowerPositiveSum_succ_one (n : Nat) :
    explicitPowerPositiveSum (Nat.succ n) 1 = 1 := by
  unfold explicitPowerPositiveSum explicitPowerPositiveTerm explicitPowerTerm
  unfold finiteNatSum BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum
  change 1 * 1 ^ Nat.succ n + 0 = 1
  rw [Nat.one_pow, Nat.mul_one]

theorem explicitPowerNegativeSum_succ_one (n : Nat) :
    explicitPowerNegativeSum (Nat.succ n) 1 = 0 := by
  rfl

theorem factorialCount_one :
    factorialCount 1 = 1 := by
  rfl

theorem explicitFormulaBalance_succ_one (n : Nat) :
    explicitFormulaBalance (Nat.succ n) 1 := by
  unfold explicitFormulaBalance
  rw [factorialCount_one]
  rw [explicitPowerNegativeSum_succ_one n]
  rw [explicitPowerPositiveSum_succ_one n]
  change 1 * BEDC.Derived.StirlingUp.stirlingSecond (Nat.succ n) 1 + 0 = 1
  rw [BEDC.Derived.StirlingUp.stirlingSecond_succ_one n]

theorem explicitFormulaBalance_one_column (n : Nat) :
    explicitFormulaBalance n 1 := by
  cases n with
  | zero =>
      exact explicitFormulaBalance_zero_one
  | succ n =>
      exact explicitFormulaBalance_succ_one n

theorem fallingFactorial_zero (x : Nat) :
    fallingFactorial x 0 = 1 := by
  rfl

theorem fallingFactorial_succ (x k : Nat) :
    fallingFactorial x (Nat.succ k) = fallingFactorial x k * (x - k) := by
  rfl

theorem fallingExpansion_zero (x : Nat) :
    fallingExpansion x 0 = 1 := by
  unfold fallingExpansion fallingExpansionPrefix fallingFactorial
  rfl

theorem fallingExpansion_one (x : Nat) :
    fallingExpansion x 1 = x := by
  change stirlingSecond 1 0 * 1 +
      stirlingSecond 1 1 * (1 * (x - 0)) = x
  rw [stirlingSecond_succ_zero 0]
  rw [stirlingSecond_self 1]
  rw [Nat.sub_zero]
  rw [Nat.zero_mul, Nat.one_mul, Nat.one_mul]
  exact Nat.zero_add x

private theorem nat_pow_one_clean (x : Nat) :
    x ^ 1 = x := by
  change x ^ 0 * x = x
  change 1 * x = x
  exact Nat.one_mul x

private theorem nat_pow_two_clean (x : Nat) :
    x ^ 2 = x * x := by
  change x ^ 1 * x = x * x
  rw [nat_pow_one_clean x]

theorem fallingExpansion_two (x : Nat) :
    fallingExpansion x 2 = x ^ 2 := by
  change
    (stirlingSecond 2 0 * 1 +
      stirlingSecond 2 1 * (1 * (x - 0))) +
        stirlingSecond 2 2 * ((1 * (x - 0)) * (x - 1)) = x ^ 2
  rw [stirlingSecond_succ_zero 1]
  rw [stirlingSecond_self 2]
  change (0 * 1 + 1 * (1 * (x - 0))) +
      1 * ((1 * (x - 0)) * (x - 1)) = x ^ 2
  rw [Nat.sub_zero]
  rw [Nat.zero_mul, Nat.zero_add]
  repeat rw [Nat.one_mul]
  cases x with
  | zero =>
      rfl
  | succ x =>
      change Nat.succ x + Nat.succ x * x = Nat.succ x ^ 2
      rw [nat_pow_two_clean]
      rw [Nat.mul_succ]
      rw [Nat.add_comm (Nat.succ x * x) (Nat.succ x)]

theorem stirlingSecondFn_unary_result (n k : BHist) :
    UnaryHistory (stirlingSecondFn n k) := by
  unfold stirlingSecondFn
  exact natToUnary_unary _

theorem bellNumberFn_unary_result (n : BHist) :
    UnaryHistory (bellNumberFn n) := by
  unfold bellNumberFn
  exact natToUnary_unary _

theorem stirlingSecondFn_natToUnary (n k : Nat) :
    stirlingSecondFn (natToUnary n) (natToUnary k) =
      natToUnary (stirlingSecond n k) := by
  unfold stirlingSecondFn
  rw [natToUnary_length, natToUnary_length]

theorem bellNumberFn_natToUnary (n : Nat) :
    bellNumberFn (natToUnary n) =
      natToUnary (bellNumber n) := by
  unfold bellNumberFn
  rw [natToUnary_length]

theorem stirlingSecond_verified_scope_export :
    (∀ n k : Nat,
      stirlingSecond (Nat.succ n) (Nat.succ k) =
        Nat.succ k * stirlingSecond n (Nat.succ k) + stirlingSecond n k) ∧
      (∀ n : Nat, bellPrefix n n = bellNumber n) ∧
      (∀ n : Nat, bellNumber n = listNatSum (stirlingSecond n) (inclusiveRange n)) ∧
      (∀ n : Nat, explicitFormulaBalance n 0) ∧
      (∀ n : Nat, explicitFormulaBalance n 1) ∧
      (∀ x : Nat, fallingExpansion x 0 = 1) ∧
      (∀ x : Nat, fallingExpansion x 1 = x) ∧
      (∀ x : Nat, fallingExpansion x 2 = x ^ 2) := by
  constructor
  · intro n k
    exact stirlingSecond_recurrence n k
  · constructor
    · intro n
      exact stirlingSecond_sum_eq_bellNumber n
    · constructor
      · intro n
        exact bellNumber_list_stirling_sum n
      · constructor
        · intro n
          exact explicitFormulaBalance_zero_column n
        · constructor
          · intro n
            exact explicitFormulaBalance_one_column n
          · constructor
            · intro x
              exact fallingExpansion_zero x
            · constructor
              · intro x
                exact fallingExpansion_one x
              · intro x
                exact fallingExpansion_two x

end BEDC.Derived.StirlingSecondCompleteUp
