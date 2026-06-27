import BEDC.Derived.BoxStreamSqrt2Up
import BEDC.Derived.NonCollapseInvariantUp
import BEDC.Derived.RationalUp
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.Sqrt2BisectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.RationalUp
open BEDC.Derived.BoxStreamSqrt2Up (ratTwo)
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

def natOne : BHist :=
  BHist.e1 BHist.Empty

def powTwoNat : Nat -> Nat
  | 0 => 1
  | Nat.succ k => 2 * powTwoNat k

theorem powTwoNat_pos (k : Nat) : 0 < powTwoNat k := by
  induction k with
  | zero =>
      exact Nat.succ_pos 0
  | succ k ih =>
      exact Nat.mul_pos (Nat.succ_pos 1) ih

theorem powTwoNat_succ (k : Nat) :
    powTwoNat (Nat.succ k) = 2 * powTwoNat k := by
  rfl

def natHist (n : Nat) : BHist :=
  natToUnary n

theorem natHist_unary (n : Nat) : UnaryHistory (natHist n) :=
  natToUnary_unary n

theorem natHist_length (n : Nat) : bwordLength (natHist n) = n :=
  natToUnary_length n

theorem intLe_natHist_of_le {a b : Nat} (h : a ≤ b) :
    intLe (intOfNat (natHist a) (natHist_unary a))
      (intOfNat (natHist b) (natHist_unary b)) := by
  unfold intLe intOfNat intToPair
  apply BEDC.Derived.IntUp.pairLe_of_length_order
  · exact ⟨natHist_unary a, unary_empty⟩
  · exact ⟨natHist_unary b, unary_empty⟩
  change bwordLength (natHist a) + bwordLength BHist.Empty ≤
    bwordLength (natHist b) + bwordLength BHist.Empty
  rw [natHist_length, natHist_length]
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rw [Nat.add_zero, Nat.add_zero]
  exact h

theorem powTwoDenPos (k : Nat) :
    NatUnaryStrictPrefix natOne (natHist (powTwoNat k)) ∨
      hsame (natHist (powTwoNat k)) natOne := by
  cases k with
  | zero =>
      exact Or.inr
        ((BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
          (natHist_unary (powTwoNat 0)) (unary_e1_closed unary_empty)).mpr
          (by
            change bwordLength (natHist 1) = bwordLength natOne
            rw [natHist_length]
            change 1 = bwordLength (BHist.e1 BHist.Empty)
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
              BHist.Empty unary_empty]
            rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]))
  | succ k =>
      apply Or.inl
      apply BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
      · exact unary_e1_closed unary_empty
      · exact natHist_unary (powTwoNat (Nat.succ k))
      · change bwordLength natOne < bwordLength (natHist (powTwoNat (Nat.succ k)))
        unfold natOne
        rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
          BHist.Empty unary_empty]
        rw [natHist_length]
        change 1 < 2 * powTwoNat k
        calc
          1 < 2 := Nat.lt_succ_self 1
          _ ≤ 2 * powTwoNat k := Nat.mul_le_mul_left 2 (powTwoNat_pos k)

def natOverPowTwo (n k : Nat) : RatNum :=
  { num := intOfNat (natHist n) (natHist_unary n)
    den := natHist (powTwoNat k)
    den_pos := powTwoDenPos k }

theorem ratLe_natOverPowTwo_of_le {a b k : Nat} (h : a ≤ b) :
    ratLe (natOverPowTwo a k) (natOverPowTwo b k) := by
  unfold ratLe natOverPowTwo ratDenInt
  change intLe
    (IntMul (intOfNat (natHist a) (natHist_unary a))
      (intOfNat (natHist (powTwoNat k)) (natHist_unary (powTwoNat k))))
    (IntMul (intOfNat (natHist b) (natHist_unary b))
      (intOfNat (natHist (powTwoNat k)) (natHist_unary (powTwoNat k))))
  exact intLe_mul_nonneg_right_of_nat
    (natHist (powTwoNat k)) (natHist_unary (powTwoNat k))
    (intLe_natHist_of_le h)

structure Sqrt2BisectInterval where
  depth : Nat
  loNum : Nat
  hiNum : Nat
  adjacent : hiNum = loNum + 1

def sqrt2BisectInitial : Sqrt2BisectInterval :=
  { depth := 0
    loNum := 1
    hiNum := 2
    adjacent := rfl }

def sqrt2BisectMidNum (I : Sqrt2BisectInterval) : Nat :=
  I.loNum + I.hiNum

def sqrt2BisectThreshold (depth : Nat) : Nat :=
  2 * powTwoNat depth * powTwoNat depth

def natLtBool : Nat -> Nat -> Bool
  | 0, 0 => false
  | 0, Nat.succ _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natLtBool a b

def sqrt2MidBelowNat (I : Sqrt2BisectInterval) : Prop :=
  sqrt2BisectMidNum I * sqrt2BisectMidNum I <
    sqrt2BisectThreshold (Nat.succ I.depth)

def sqrt2MidBelow (I : Sqrt2BisectInterval) : Bool :=
  natLtBool
    (sqrt2BisectMidNum I * sqrt2BisectMidNum I)
    (sqrt2BisectThreshold (Nat.succ I.depth))

def sqrt2LowerChild (I : Sqrt2BisectInterval) : Sqrt2BisectInterval :=
  { depth := Nat.succ I.depth
    loNum := I.loNum + I.hiNum
    hiNum := I.loNum + I.hiNum + 1
    adjacent := rfl }

def sqrt2UpperChild (I : Sqrt2BisectInterval) : Sqrt2BisectInterval :=
  { depth := Nat.succ I.depth
    loNum := I.loNum + I.loNum
    hiNum := I.loNum + I.loNum + 1
    adjacent := rfl }

def sqrt2BisectRefine (I : Sqrt2BisectInterval) : Sqrt2BisectInterval :=
  if sqrt2MidBelow I then sqrt2LowerChild I else sqrt2UpperChild I

def sqrt2BisectRaw : Nat -> Sqrt2BisectInterval
  | 0 => sqrt2BisectInitial
  | Nat.succ k => sqrt2BisectRefine (sqrt2BisectRaw k)

theorem sqrt2BisectRefine_depth (I : Sqrt2BisectInterval) :
    (sqrt2BisectRefine I).depth = Nat.succ I.depth := by
  unfold sqrt2BisectRefine
  cases sqrt2MidBelow I <;> rfl

theorem sqrt2BisectRaw_depth (k : Nat) :
    (sqrt2BisectRaw k).depth = k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change (sqrt2BisectRefine (sqrt2BisectRaw k)).depth = Nat.succ k
      rw [sqrt2BisectRefine_depth]
      rw [ih]

theorem sqrt2Bisect_width_num_one (k : Nat) :
    (sqrt2BisectRaw k).hiNum = (sqrt2BisectRaw k).loNum + 1 :=
  (sqrt2BisectRaw k).adjacent

theorem sqrt2Bisect_diam_halves (k : Nat) :
    (sqrt2BisectRaw (Nat.succ k)).hiNum =
        (sqrt2BisectRaw (Nat.succ k)).loNum + 1 ∧
      powTwoNat (Nat.succ k) = 2 * powTwoNat k := by
  constructor
  · exact sqrt2Bisect_width_num_one (Nat.succ k)
  · rfl

def sqrt2NatLowerSqBelow (I : Sqrt2BisectInterval) : Prop :=
  I.loNum * I.loNum < sqrt2BisectThreshold I.depth

def sqrt2NatUpperSqAbove (I : Sqrt2BisectInterval) : Prop :=
  sqrt2BisectThreshold I.depth < I.hiNum * I.hiNum

def Sqrt2NatBracket (I : Sqrt2BisectInterval) : Prop :=
  sqrt2NatLowerSqBelow I ∧ sqrt2NatUpperSqAbove I

theorem sqrt2Bisect_initial_bracket :
    Sqrt2NatBracket sqrt2BisectInitial := by
  unfold Sqrt2NatBracket sqrt2NatLowerSqBelow sqrt2NatUpperSqAbove
    sqrt2BisectInitial sqrt2BisectThreshold powTwoNat
  constructor
  · decide
  · decide

def sqrt2BisectIntervalLo (I : Sqrt2BisectInterval) : RatNum :=
  natOverPowTwo I.loNum I.depth

def sqrt2BisectIntervalHi (I : Sqrt2BisectInterval) : RatNum :=
  natOverPowTwo I.hiNum I.depth

def sqrt2BisectCenter (I : Sqrt2BisectInterval) : RatNum :=
  natOverPowTwo (I.loNum + I.hiNum) (Nat.succ I.depth)

def sqrt2BisectReInterval (k : Nat) : QInterval :=
  { lo := sqrt2BisectIntervalLo (sqrt2BisectRaw k)
    hi := sqrt2BisectIntervalHi (sqrt2BisectRaw k)
    valid := ratLe_natOverPowTwo_of_le
      (by
        rw [sqrt2Bisect_width_num_one k]
        exact Nat.le_succ _) }

def sqrt2BisectZeroInterval : QInterval :=
  { lo := ratZero
    hi := ratZero
    valid := ratLe_refl ratZero }

def sqrt2BisectBox (k : Nat) : ComplexBox :=
  { re := sqrt2BisectReInterval k
    im := sqrt2BisectZeroInterval }

def sqrt2BisectGauge : BoxGauge :=
  { fits := fun box precision =>
      ∃ n : Nat, precision ≤ n ∧ box = sqrt2BisectBox n
    fits_weaken := by
      intro box hi lo hlo hfit
      cases hfit with
      | intro n data =>
          exact ⟨n, Nat.le_trans hlo data.left, data.right⟩ }

def sqrt2BisectBoxStream : BoxStream sqrt2BisectGauge :=
  { box := sqrt2BisectBox
    modulus := fun k => k
    modulus_mono := by
      intro i j hij
      exact hij
    fits_at := by
      intro k n hn
      exact ⟨n, hn, rfl⟩ }

theorem sqrt2Bisect_boxAt_fits (k : Nat) :
    sqrt2BisectGauge.fits (boxAt sqrt2BisectBoxStream k) k :=
  boxAt_fits sqrt2BisectBoxStream k

theorem sqrt2Bisect_boxAt_eq (k : Nat) :
    boxAt sqrt2BisectBoxStream k = sqrt2BisectBox k := by
  rfl

theorem sqrt2Bisect_raw_not_constant :
    sqrt2BisectRaw 1 ≠ sqrt2BisectRaw 0 := by
  intro same
  have depthSame := congrArg Sqrt2BisectInterval.depth same
  change (sqrt2BisectRefine sqrt2BisectInitial).depth = sqrt2BisectInitial.depth at depthSame
  rw [sqrt2BisectRefine_depth] at depthSame
  cases depthSame

structure Sqrt2BisectBoxStreamCandidate where
  gauge : BoxGauge
  point : BoxStream gauge
  raw : Nat -> Sqrt2BisectInterval
  raw_depth : ∀ k : Nat, (raw k).depth = k
  raw_width : ∀ k : Nat, (raw k).hiNum = (raw k).loNum + 1
  raw_not_constant : raw 1 ≠ raw 0

def sqrt2BisectBoxStreamCandidate : Sqrt2BisectBoxStreamCandidate :=
  { gauge := sqrt2BisectGauge
    point := sqrt2BisectBoxStream
    raw := sqrt2BisectRaw
    raw_depth := sqrt2BisectRaw_depth
    raw_width := sqrt2Bisect_width_num_one
    raw_not_constant := sqrt2Bisect_raw_not_constant }

end BEDC.Derived.Sqrt2BisectionUp
