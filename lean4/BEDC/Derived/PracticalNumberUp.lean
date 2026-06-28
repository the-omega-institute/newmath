import BEDC.Derived.DivisorFunctionUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.PracticalNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

/-- Quotient search for `dividesNatBool`; the fuel bound is external to the predicate. -/
def boundedQuotientSearch (d n : Nat) : Nat -> Bool
  | 0 => false
  | fuel + 1 =>
      if d * fuel = n then true else boundedQuotientSearch d n fuel

/-- Bounded divisibility over native natural numbers, searched by quotient fuel. -/
def dividesNatBool (d n : Nat) : Bool :=
  match d with
  | 0 => false
  | d' + 1 =>
      let d := d' + 1
      boundedQuotientSearch d n (n + 1)

def positiveDivisorNatBool (d n : Nat) : Bool :=
  match d with
  | 0 => false
  | d' + 1 => dividesNatBool (d' + 1) n

def properDivisorNatBool (d n : Nat) : Bool :=
  match d with
  | 0 => false
  | d' + 1 =>
      let d := d' + 1
      if d < n then dividesNatBool d n else false

def filterDivisorsNat (n : Nat) : List Nat -> List Nat
  | [] => []
  | d :: ds =>
      if positiveDivisorNatBool d n then
        d :: filterDivisorsNat n ds
      else
        filterDivisorsNat n ds

def filterProperDivisorsNat (n : Nat) : List Nat -> List Nat
  | [] => []
  | d :: ds =>
      if properDivisorNatBool d n then
        d :: filterProperDivisorsNat n ds
      else
        filterProperDivisorsNat n ds

def divisorsNat (n : Nat) : List Nat :=
  filterDivisorsNat n (List.range (n + 1))

def properDivisorsNat (n : Nat) : List Nat :=
  filterProperDivisorsNat n (List.range n)

def listContainsNat (target : Nat) : List Nat -> Bool
  | [] => false
  | x :: xs => if x = target then true else listContainsNat target xs

/-- Subset sums of a divisor list; each input position can be used at most once. -/
def subsetSumsNat : List Nat -> List Nat
  | [] => [0]
  | d :: ds =>
      let tailSums := subsetSumsNat ds
      tailSums ++ tailSums.map (fun s => d + s)

def positiveTargetsCoveredFromNat (fuel start : Nat) (sums : List Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
      listContainsNat start sums &&
        positiveTargetsCoveredFromNat fuel' (start + 1) sums

def positiveTargetsCoveredUpToNat (n : Nat) (divisors : List Nat) : Bool :=
  positiveTargetsCoveredFromNat n 1 (subsetSumsNat divisors)

/-- Standard practical-number predicate: every `1 <= m <= n` is covered by
distinct positive divisors of `n`. -/
def PracticalNumberNat (n : Nat) : Prop :=
  0 < n ∧ positiveTargetsCoveredUpToNat n (divisorsNat n) = true

/-- Strict true-divisor cover below the top endpoint. The endpoint `n` is not
claimed here, because strict true divisors cannot sum to `1` or `2` at the top. -/
def StrictProperBelowTopPracticalNat (n : Nat) : Prop :=
  0 < n ∧ positiveTargetsCoveredUpToNat (n - 1) (properDivisorsNat n) = true

def StrictProperAllLePracticalNat (n : Nat) : Prop :=
  0 < n ∧ positiveTargetsCoveredUpToNat n (properDivisorsNat n) = true

def practicalNumberNatDecision (n : Nat) : Bool :=
  match n with
  | 0 => false
  | n' + 1 => positiveTargetsCoveredUpToNat (n' + 1) (divisorsNat (n' + 1))

def strictProperBelowTopDecision (n : Nat) : Bool :=
  match n with
  | 0 => false
  | n' + 1 => positiveTargetsCoveredUpToNat n' (properDivisorsNat (n' + 1))

def PracticalNumber (n : BHist) : Prop :=
  PracticalNumberNat (bwordLength n)

def practicalNumberDecision (n : BHist) : Bool :=
  practicalNumberNatDecision (bwordLength n)

theorem practicalNumberNatDecision_eq_true_iff (n : Nat) :
    practicalNumberNatDecision n = true ↔ PracticalNumberNat n := by
  cases n with
  | zero =>
      constructor
      · intro decision
        cases decision
      · intro practical
        cases practical.left
  | succ n =>
      constructor
      · intro decision
        exact ⟨Nat.succ_pos n, decision⟩
      · intro practical
        exact practical.right

theorem practicalNumberDecision_eq_true_iff (n : BHist) :
    practicalNumberDecision n = true ↔ PracticalNumber n := by
  unfold practicalNumberDecision PracticalNumber
  exact practicalNumberNatDecision_eq_true_iff (bwordLength n)

theorem strictProperBelowTopDecision_eq_true_iff (n : Nat) :
    strictProperBelowTopDecision n = true ↔ StrictProperBelowTopPracticalNat n := by
  cases n with
  | zero =>
      constructor
      · intro decision
        cases decision
      · intro practical
        cases practical.left
  | succ n =>
      constructor
      · intro decision
        exact ⟨Nat.succ_pos n, decision⟩
      · intro practical
        exact practical.right

def NatOne : BHist := natToUnary 1
def NatTwo : BHist := natToUnary 2
def NatFour : BHist := natToUnary 4
def NatSix : BHist := natToUnary 6
def NatEight : BHist := natToUnary 8
def NatTwelve : BHist := natToUnary 12

theorem one_practicalNumberNat : PracticalNumberNat 1 := by
  exact ⟨by decide, by decide⟩

theorem two_practicalNumberNat : PracticalNumberNat 2 := by
  exact ⟨by decide, by decide⟩

theorem four_practicalNumberNat : PracticalNumberNat 4 := by
  exact ⟨by decide, by decide⟩

theorem six_practicalNumberNat : PracticalNumberNat 6 := by
  exact ⟨by decide, by decide⟩

theorem eight_practicalNumberNat : PracticalNumberNat 8 := by
  exact ⟨by decide, by decide⟩

theorem twelve_practicalNumberNat : PracticalNumberNat 12 := by
  exact ⟨by decide, by decide⟩

theorem one_strictProperBelowTopPracticalNat :
    StrictProperBelowTopPracticalNat 1 := by
  exact ⟨by decide, by decide⟩

theorem two_strictProperBelowTopPracticalNat :
    StrictProperBelowTopPracticalNat 2 := by
  exact ⟨by decide, by decide⟩

theorem four_strictProperBelowTopPracticalNat :
    StrictProperBelowTopPracticalNat 4 := by
  exact ⟨by decide, by decide⟩

theorem six_strictProperBelowTopPracticalNat :
    StrictProperBelowTopPracticalNat 6 := by
  exact ⟨by decide, by decide⟩

theorem eight_strictProperBelowTopPracticalNat :
    StrictProperBelowTopPracticalNat 8 := by
  exact ⟨by decide, by decide⟩

theorem twelve_strictProperBelowTopPracticalNat :
    StrictProperBelowTopPracticalNat 12 := by
  exact ⟨by decide, by decide⟩

theorem strictProperAllLe_one_cover_fails :
    positiveTargetsCoveredUpToNat 1 (properDivisorsNat 1) = false := by
  rfl

theorem strictProperAllLe_two_cover_fails :
    positiveTargetsCoveredUpToNat 2 (properDivisorsNat 2) = false := by
  decide

theorem one_practicalNumber : PracticalNumber NatOne := by
  unfold PracticalNumber NatOne
  rw [natToUnary_length]
  exact one_practicalNumberNat

theorem two_practicalNumber : PracticalNumber NatTwo := by
  unfold PracticalNumber NatTwo
  rw [natToUnary_length]
  exact two_practicalNumberNat

theorem four_practicalNumber : PracticalNumber NatFour := by
  unfold PracticalNumber NatFour
  rw [natToUnary_length]
  exact four_practicalNumberNat

theorem six_practicalNumber : PracticalNumber NatSix := by
  unfold PracticalNumber NatSix
  rw [natToUnary_length]
  exact six_practicalNumberNat

theorem eight_practicalNumber : PracticalNumber NatEight := by
  unfold PracticalNumber NatEight
  rw [natToUnary_length]
  exact eight_practicalNumberNat

theorem twelve_practicalNumber : PracticalNumber NatTwelve := by
  unfold PracticalNumber NatTwelve
  rw [natToUnary_length]
  exact twelve_practicalNumberNat

def powTwoNat : Nat -> Nat
  | 0 => 1
  | k + 1 => 2 * powTwoNat k

def dyadicDivisorListNat : Nat -> List Nat
  | 0 => [1]
  | k + 1 => dyadicDivisorListNat k ++ [powTwoNat (k + 1)]

def DyadicPracticalCheckNat (k : Nat) : Bool :=
  positiveTargetsCoveredUpToNat (powTwoNat k) (dyadicDivisorListNat k)

def DyadicPracticalCheck (k : Nat) : Prop :=
  DyadicPracticalCheckNat k = true

inductive DyadicSubsetSumCertificate : Nat -> Nat -> Prop where
  | zero : DyadicSubsetSumCertificate 0 0
  | skip {k m : Nat} :
      DyadicSubsetSumCertificate k m -> DyadicSubsetSumCertificate (k + 1) m
  | take {k m : Nat} :
      DyadicSubsetSumCertificate k m ->
        DyadicSubsetSumCertificate (k + 1) (powTwoNat k + m)

def DyadicPrefixCovered (k : Nat) : Prop :=
  ∀ m : Nat, 1 ≤ m -> m ≤ powTwoNat k -> DyadicSubsetSumCertificate (k + 1) m

theorem nat_add_right_lt_cancel_pure (a b c : Nat) :
    b + a < c + a -> b < c := by
  induction a with
  | zero =>
      intro h
      rw [Nat.add_zero, Nat.add_zero] at h
      exact h
  | succ a ih =>
      intro h
      change Nat.succ (b + a) < Nat.succ (c + a) at h
      exact ih (Nat.lt_of_succ_lt_succ h)

theorem nat_add_left_lt_cancel_pure (a b c : Nat) :
    a + b < a + c -> b < c := by
  intro h
  have hright : b + a < c + a := by
    rw [Nat.add_comm b a, Nat.add_comm c a]
    exact h
  exact nat_add_right_lt_cancel_pure a b c hright

theorem powTwoNat_positive (k : Nat) :
    0 < powTwoNat k := by
  induction k with
  | zero =>
      exact Nat.succ_pos 0
  | succ k ih =>
      change 0 < 2 * powTwoNat k
      exact Nat.mul_pos (by decide : 0 < 2) ih

theorem powTwoNat_lt_succ (k : Nat) :
    powTwoNat k < powTwoNat (k + 1) := by
  change powTwoNat k < 2 * powTwoNat k
  rw [Nat.two_mul]
  exact Nat.lt_add_of_pos_right (powTwoNat_positive k)

theorem dyadicSubsetCover_lt :
    ∀ k m : Nat, m < powTwoNat k -> DyadicSubsetSumCertificate k m
  | 0, m, h => by
      cases m with
      | zero =>
          exact DyadicSubsetSumCertificate.zero
      | succ m =>
          change Nat.succ m < 1 at h
          have impossible : Nat.succ m < Nat.succ 0 := h
          exact False.elim
            (Nat.not_succ_le_zero m (Nat.lt_of_succ_lt_succ impossible))
  | k + 1, m, h => by
      cases Nat.lt_or_ge m (powTwoNat k) with
      | inl left =>
          exact DyadicSubsetSumCertificate.skip (dyadicSubsetCover_lt k m left)
      | inr right =>
          cases Nat.le.dest right with
          | intro r sumEq =>
              have hsum : powTwoNat k + r < powTwoNat k + powTwoNat k := by
                change m < 2 * powTwoNat k at h
                rw [Nat.two_mul] at h
                rw [sumEq]
                exact h
              have rLt : r < powTwoNat k :=
                nat_add_left_lt_cancel_pure (powTwoNat k) r (powTwoNat k) hsum
              rw [← sumEq]
              exact DyadicSubsetSumCertificate.take (dyadicSubsetCover_lt k r rLt)

theorem dyadicPowerPracticalCertificate (k : Nat) :
    DyadicPrefixCovered k := by
  intro m _oneLe mLe
  exact dyadicSubsetCover_lt (k + 1) m
    (Nat.lt_of_le_of_lt mLe (powTwoNat_lt_succ k))

theorem powTwo_zero_practicalNumberNat :
    PracticalNumberNat (powTwoNat 0) := by
  exact one_practicalNumberNat

theorem powTwo_one_practicalNumberNat :
    PracticalNumberNat (powTwoNat 1) := by
  exact two_practicalNumberNat

theorem powTwo_two_practicalNumberNat :
    PracticalNumberNat (powTwoNat 2) := by
  exact four_practicalNumberNat

theorem powTwo_three_practicalNumberNat :
    PracticalNumberNat (powTwoNat 3) := by
  exact eight_practicalNumberNat

theorem dyadicCheck_zero : DyadicPracticalCheck 0 := by
  rfl

theorem dyadicCheck_one : DyadicPracticalCheck 1 := by
  rfl

theorem dyadicCheck_two : DyadicPracticalCheck 2 := by
  rfl

theorem dyadicCheck_three : DyadicPracticalCheck 3 := by
  rfl

end BEDC.Derived.PracticalNumberUp
