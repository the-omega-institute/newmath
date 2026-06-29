import BEDC.Derived.CollatzTrajectoryUp

namespace BEDC.Derived.CollatzParityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)
open BEDC.Derived.PadicUp (natModFn)
open BEDC.Derived.PrimeUp (NatDivRem_remainder_unary)
open BEDC.Derived.CollatzTrajectoryUp

/-!
本界面只保留有限 fuel 轨迹，记录压缩 Collatz 映射和有界样本计算；
不声称全体自然数都会到达 1。
-/

inductive CollatzParity where
  | even : CollatzParity
  | odd : CollatzParity
deriving DecidableEq

def parityOf (n : Nat) : CollatzParity :=
  if n % 2 = 0 then
    CollatzParity.even
  else
    CollatzParity.odd

def parityCode : CollatzParity -> Nat
  | CollatzParity.even => 0
  | CollatzParity.odd => 1

def compressedHalvingInput (n : Nat) : Nat :=
  if n % 2 = 0 then
    n
  else
    3 * n + 1

def compressedStep (n : Nat) : Nat :=
  compressedHalvingInput n / 2

def compressedStepUnary (n : Nat) : BHist :=
  natToUnary (compressedStep n)

def compressedHalvingInputUnary (n : Nat) : BHist :=
  natToUnary (compressedHalvingInput n)

def compressedOrbit : Nat -> Nat -> List Nat
  | 0, n => [n]
  | fuel + 1, n => n :: compressedOrbit fuel (compressedStep n)

def compressedAfter : Nat -> Nat -> Nat
  | 0, n => n
  | fuel + 1, n => compressedAfter fuel (compressedStep n)

def compressedParityPattern : Nat -> Nat -> List CollatzParity
  | 0, _n => []
  | fuel + 1, n => parityOf n :: compressedParityPattern fuel (compressedStep n)

def compressedParityCodePattern (fuel n : Nat) : List Nat :=
  (compressedParityPattern fuel n).map parityCode

def compressedHitsOneWithin : Nat -> Nat -> Bool
  | 0, n => n == 1
  | fuel + 1, n =>
      if n == 1 then
        true
      else
        compressedHitsOneWithin fuel (compressedStep n)

def compressedHitsOneWithinVerified (fuel n : Nat) : Prop :=
  compressedHitsOneWithin fuel n = true

instance compressedHitsOneWithinVerifiedDecidable (fuel n : Nat) :
    Decidable (compressedHitsOneWithinVerified fuel n) :=
  inferInstanceAs (Decidable (compressedHitsOneWithin fuel n = true))

def compressedNoHitBefore : Nat -> Nat -> Bool
  | 0, _n => true
  | fuel + 1, n =>
      if compressedAfter fuel n == 1 then
        false
      else
        compressedNoHitBefore fuel n

def compressedTotalStoppingTimeVerified (fuel n : Nat) : Prop :=
  compressedAfter fuel n = 1 ∧ compressedNoHitBefore fuel n = true

instance compressedTotalStoppingTimeVerifiedDecidable (fuel n : Nat) :
    Decidable (compressedTotalStoppingTimeVerified fuel n) :=
  inferInstanceAs
    (Decidable (compressedAfter fuel n = 1 ∧ compressedNoHitBefore fuel n = true))

structure CompressedParityRecord where
  start : Nat
  steps : Nat
  orbit : List Nat
  pattern : List CollatzParity

def CompressedParityRecordVerified (r : CompressedParityRecord) : Prop :=
  compressedOrbit r.steps r.start = r.orbit ∧
    compressedParityPattern r.steps r.start = r.pattern ∧
      compressedTotalStoppingTimeVerified r.steps r.start

instance compressedParityRecordVerifiedDecidable (r : CompressedParityRecord) :
    Decidable (CompressedParityRecordVerified r) :=
  inferInstanceAs
    (Decidable
      (compressedOrbit r.steps r.start = r.orbit ∧
        compressedParityPattern r.steps r.start = r.pattern ∧
          compressedTotalStoppingTimeVerified r.steps r.start))

def compressedRecordThree : CompressedParityRecord where
  start := 3
  steps := 5
  orbit := [3, 5, 8, 4, 2, 1]
  pattern :=
    [CollatzParity.odd, CollatzParity.odd, CollatzParity.even,
      CollatzParity.even, CollatzParity.even]

def compressedRecordSeven : CompressedParityRecord where
  start := 7
  steps := 11
  orbit := [7, 11, 17, 26, 13, 20, 10, 5, 8, 4, 2, 1]
  pattern :=
    [CollatzParity.odd, CollatzParity.odd, CollatzParity.odd,
      CollatzParity.even, CollatzParity.odd, CollatzParity.even,
      CollatzParity.even, CollatzParity.odd, CollatzParity.even,
      CollatzParity.even, CollatzParity.even]

theorem parityOf_even_branch {n : Nat} :
    n % 2 = 0 -> parityOf n = CollatzParity.even := by
  intro evenResidue
  unfold parityOf
  rw [if_pos evenResidue]

theorem parityOf_odd_branch {n : Nat} :
    (n % 2 = 0 -> False) -> parityOf n = CollatzParity.odd := by
  intro oddResidue
  unfold parityOf
  rw [if_neg oddResidue]

theorem compressedHalvingInput_even_branch {n : Nat} :
    n % 2 = 0 -> compressedHalvingInput n = n := by
  intro evenResidue
  unfold compressedHalvingInput
  rw [if_pos evenResidue]

theorem compressedHalvingInput_odd_branch {n : Nat} :
    (n % 2 = 0 -> False) -> compressedHalvingInput n = 3 * n + 1 := by
  intro oddResidue
  unfold compressedHalvingInput
  rw [if_neg oddResidue]

theorem compressedStep_even_branch {n : Nat} :
    n % 2 = 0 -> compressedStep n = n / 2 := by
  intro evenResidue
  unfold compressedStep
  rw [compressedHalvingInput_even_branch evenResidue]

theorem compressedStep_odd_branch {n : Nat} :
    (n % 2 = 0 -> False) -> compressedStep n = (3 * n + 1) / 2 := by
  intro oddResidue
  unfold compressedStep
  rw [compressedHalvingInput_odd_branch oddResidue]

theorem compressedStep_even_matches_collatzStep {n : Nat} :
    n % 2 = 0 -> compressedStep n = collatzStep n := by
  intro evenResidue
  rw [compressedStep_even_branch evenResidue]
  rw [collatzStep_even_branch evenResidue]

theorem compressedStep_odd_is_half_collatzStep {n : Nat} :
    (n % 2 = 0 -> False) -> compressedStep n = collatzStep n / 2 := by
  intro oddResidue
  rw [compressedStep_odd_branch oddResidue]
  rw [collatzStep_odd_branch oddResidue]

def compressedHalvingInputDivRemByTwo (n : Nat) : Prop :=
  collatzDivRemByTwo (compressedHalvingInput n)

theorem compressedHalvingInputDivRemByTwo_verified (n : Nat) :
  compressedHalvingInputDivRemByTwo n := by
  unfold compressedHalvingInputDivRemByTwo
  exact collatzDivRemByTwo_verified (compressedHalvingInput n)

theorem compressedHalvingInputDivRemByTwo_unary_components (n : Nat) :
    UnaryHistory collatzTwoUnary ∧
      UnaryHistory (compressedHalvingInputUnary n) ∧
        UnaryHistory
          (natModFn collatzTwoUnary (compressedHalvingInputUnary n)) := by
  unfold compressedHalvingInputUnary
  exact collatzDivRemByTwo_unary_components (compressedHalvingInput n)

theorem compressedStepUnary_unary (n : Nat) :
    UnaryHistory (compressedStepUnary n) := by
  unfold compressedStepUnary
  exact natToUnary_unary (compressedStep n)

theorem compressedOrbit_zero (n : Nat) :
    compressedOrbit 0 n = [n] := by
  rfl

theorem compressedOrbit_succ (fuel n : Nat) :
    compressedOrbit (fuel + 1) n =
      n :: compressedOrbit fuel (compressedStep n) := by
  rfl

theorem compressedOrbit_length (fuel n : Nat) :
    (compressedOrbit fuel n).length = fuel + 1 := by
  induction fuel generalizing n with
  | zero =>
      rfl
  | succ fuel ih =>
      change Nat.succ (compressedOrbit fuel (compressedStep n)).length = fuel + 1 + 1
      rw [ih (compressedStep n)]

theorem compressedParityPattern_zero (n : Nat) :
    compressedParityPattern 0 n = [] := by
  rfl

theorem compressedParityPattern_succ (fuel n : Nat) :
    compressedParityPattern (fuel + 1) n =
      parityOf n :: compressedParityPattern fuel (compressedStep n) := by
  rfl

theorem compressedParityPattern_length (fuel n : Nat) :
    (compressedParityPattern fuel n).length = fuel := by
  induction fuel generalizing n with
  | zero =>
      rfl
  | succ fuel ih =>
      change Nat.succ (compressedParityPattern fuel (compressedStep n)).length =
        Nat.succ fuel
      rw [ih (compressedStep n)]

theorem compressedAfter_zero (n : Nat) :
    compressedAfter 0 n = n := by
  rfl

theorem compressedAfter_succ (fuel n : Nat) :
    compressedAfter (fuel + 1) n = compressedAfter fuel (compressedStep n) := by
  rfl

theorem compressedStep_2 :
    compressedStep 2 = 1 := by
  rfl

theorem compressedStep_3 :
    compressedStep 3 = 5 := by
  rfl

theorem compressedAfter_0_1 :
    compressedAfter 0 1 = 1 := by
  rfl

theorem compressedAfter_1_2 :
    compressedAfter 1 2 = 1 := by
  rfl

theorem compressedAfter_5_3 :
    compressedAfter 5 3 = 1 := by
  rfl

theorem compressedAfter_11_7 :
    compressedAfter 11 7 = 1 := by
  rfl

theorem compressedAfter_13_9 :
    compressedAfter 13 9 = 1 := by
  rfl

theorem compressedOrbit_5_3_exact :
    compressedOrbit 5 3 = [3, 5, 8, 4, 2, 1] := by
  rfl

theorem compressedParityPattern_5_3_exact :
    compressedParityPattern 5 3 =
      [CollatzParity.odd, CollatzParity.odd, CollatzParity.even,
        CollatzParity.even, CollatzParity.even] := by
  rfl

theorem compressedParityCodePattern_5_3_exact :
    compressedParityCodePattern 5 3 = [1, 1, 0, 0, 0] := by
  rfl

theorem compressedOrbit_11_7_exact :
    compressedOrbit 11 7 =
      [7, 11, 17, 26, 13, 20, 10, 5, 8, 4, 2, 1] := by
  rfl

theorem compressedParityPattern_11_7_exact :
    compressedParityPattern 11 7 =
      [CollatzParity.odd, CollatzParity.odd, CollatzParity.odd,
        CollatzParity.even, CollatzParity.odd, CollatzParity.even,
        CollatzParity.even, CollatzParity.odd, CollatzParity.even,
        CollatzParity.even, CollatzParity.even] := by
  rfl

theorem compressedParityCodePattern_11_7_exact :
    compressedParityCodePattern 11 7 = [1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0] := by
  rfl

theorem compressedOrbit_13_9_exact :
    compressedOrbit 13 9 =
      [9, 14, 7, 11, 17, 26, 13, 20, 10, 5, 8, 4, 2, 1] := by
  rfl

theorem compressedParityCodePattern_13_9_exact :
    compressedParityCodePattern 13 9 =
      [1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0] := by
  rfl

theorem compressedRecordThree_verified :
    CompressedParityRecordVerified compressedRecordThree := by
  decide

theorem compressedRecordSeven_verified :
    CompressedParityRecordVerified compressedRecordSeven := by
  decide

theorem compressedSmallTotalStoppingTimes :
    compressedTotalStoppingTimeVerified 0 1 ∧
      compressedTotalStoppingTimeVerified 1 2 ∧
        compressedTotalStoppingTimeVerified 5 3 ∧
          compressedTotalStoppingTimeVerified 2 4 ∧
            compressedTotalStoppingTimeVerified 4 5 ∧
              compressedTotalStoppingTimeVerified 6 6 ∧
                compressedTotalStoppingTimeVerified 11 7 ∧
                  compressedTotalStoppingTimeVerified 3 8 ∧
                    compressedTotalStoppingTimeVerified 13 9 ∧
                      compressedTotalStoppingTimeVerified 5 10 := by
  decide

theorem compressedSmallHitsOneWithin :
    compressedHitsOneWithinVerified 0 1 ∧
      compressedHitsOneWithinVerified 1 2 ∧
        compressedHitsOneWithinVerified 5 3 ∧
          compressedHitsOneWithinVerified 2 4 ∧
            compressedHitsOneWithinVerified 4 5 ∧
              compressedHitsOneWithinVerified 6 6 ∧
                compressedHitsOneWithinVerified 11 7 ∧
                  compressedHitsOneWithinVerified 3 8 ∧
                    compressedHitsOneWithinVerified 13 9 ∧
                      compressedHitsOneWithinVerified 5 10 := by
  decide

end BEDC.Derived.CollatzParityUp
