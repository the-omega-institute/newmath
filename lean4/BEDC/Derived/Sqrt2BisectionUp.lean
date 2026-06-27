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

private theorem natLtBool_true_of_lt {a b : Nat} :
    a < b -> natLtBool a b = true := by
  intro h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => exact False.elim (Nat.not_lt_zero 0 h)
      | succ b => rfl
  | succ a ih =>
      cases b with
      | zero => exact False.elim (Nat.not_lt_zero (Nat.succ a) h)
      | succ b =>
          change natLtBool a b = true
          exact ih (Nat.lt_of_succ_lt_succ h)

private theorem not_lt_of_natLtBool_false {a b : Nat} :
    natLtBool a b = false -> ¬ a < b := by
  intro h hlt
  have htrue : natLtBool a b = true := natLtBool_true_of_lt hlt
  rw [h] at htrue
  cases htrue

private theorem lt_of_natLtBool_true {a b : Nat} :
    natLtBool a b = true -> a < b := by
  intro h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => cases h
      | succ b => exact Nat.succ_pos b
  | succ a ih =>
      cases b with
      | zero => cases h
      | succ b =>
          change natLtBool a b = true at h
          exact Nat.succ_lt_succ (ih h)

private def natEven : Nat -> Bool
  | 0 => true
  | Nat.succ 0 => false
  | Nat.succ (Nat.succ n) => natEven n

private theorem natEven_double : ∀ n : Nat, natEven (n + n) = true := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      change natEven (Nat.succ (Nat.succ (n + n))) = true
      exact ih

private theorem natEven_succ_double : ∀ n : Nat,
    natEven (Nat.succ (n + n)) = false := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ]
      change natEven (Nat.succ (n + n)) = false
      exact ih

private theorem not_double_eq_succ_double {a b : Nat} :
    a + a = Nat.succ (b + b) -> False := by
  intro h
  have parity := congrArg natEven h
  rw [natEven_double a, natEven_succ_double b] at parity
  cases parity

private theorem nat_add_four_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun t => a + t) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) := congrArg (fun t => a + (t + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun t => a + t) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

private theorem nat_mul_assoc_local (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := by
          rw [ih]
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := by
          rw [Nat.mul_succ b c]

private theorem double_square (n : Nat) :
    (n + n) * (n + n) = 2 * (2 * (n * n)) := by
  rw [← Nat.two_mul n]
  calc
    (2 * n) * (2 * n) = 2 * (n * (2 * n)) := by
      rw [nat_mul_assoc_local]
    _ = 2 * ((2 * n) * n) := by
      rw [Nat.mul_comm n (2 * n)]
    _ = 2 * (2 * (n * n)) := by
      rw [nat_mul_assoc_local]

private theorem two_mul_square_even (n : Nat) :
    2 * n * n = n * n + n * n := by
  calc
    2 * n * n = (n + n) * n := by
      rw [Nat.two_mul]
    _ = n * (n + n) := by
      rw [Nat.mul_comm (n + n) n]
    _ = n * n + n * n := Nat.mul_add n n n

private theorem odd_square_succ_double (n : Nat) :
    (n + n + 1) * (n + n + 1) =
      Nat.succ (((n + n + 1) * n + n) + ((n + n + 1) * n + n)) := by
  let m := n + n + 1
  have hm : m = n + n + 1 := rfl
  have rearr :
      (m * n + m * n) + (n + n) =
        (m * n + n) + (m * n + n) :=
    nat_add_four_swap (m * n) (m * n) n n
  calc
    (n + n + 1) * (n + n + 1) = m * (n + n + 1) := by
      rw [hm]
    _ = m * ((n + n) + 1) := rfl
    _ = m * (n + n) + m * 1 := Nat.mul_add m (n + n) 1
    _ = m * (n + n) + m := by
      rw [Nat.mul_one]
    _ = (m * n + m * n) + m := by
      rw [Nat.mul_add]
    _ = (m * n + m * n) + (n + n + 1) := by
      rw [hm]
    _ = (m * n + m * n) + ((n + n) + 1) := rfl
    _ = Nat.succ ((m * n + m * n) + (n + n)) := by
      rw [Nat.add_succ]
    _ = Nat.succ ((m * n + n) + (m * n + n)) := by
      rw [rearr]
    _ = Nat.succ (((n + n + 1) * n + n) + ((n + n + 1) * n + n)) := by
      rw [hm]

private theorem odd_square_ne_double (n a : Nat) :
    (n + n + 1) * (n + n + 1) = a + a -> False := by
  intro h
  have odd := odd_square_succ_double n
  exact not_double_eq_succ_double (a := a) (b := ((n + n + 1) * n + n))
    (h.symm.trans odd)

private theorem threshold_succ_even (d : Nat) :
    sqrt2BisectThreshold (Nat.succ d) =
      powTwoNat (Nat.succ d) * powTwoNat (Nat.succ d) +
        powTwoNat (Nat.succ d) * powTwoNat (Nat.succ d) := by
  unfold sqrt2BisectThreshold
  exact two_mul_square_even (powTwoNat (Nat.succ d))

private theorem threshold_succ_double_double (d : Nat) :
    sqrt2BisectThreshold (Nat.succ d) =
      2 * (2 * sqrt2BisectThreshold d) := by
  unfold sqrt2BisectThreshold
  change 2 * (2 * powTwoNat d) * (2 * powTwoNat d) =
    2 * (2 * (2 * powTwoNat d * powTwoNat d))
  calc
    2 * (2 * powTwoNat d) * (2 * powTwoNat d) =
        2 * ((2 * powTwoNat d) * (2 * powTwoNat d)) := by
          rw [nat_mul_assoc_local]
    _ = 2 * ((2 * powTwoNat d) * (powTwoNat d + powTwoNat d)) := by
          rw [Nat.two_mul (powTwoNat d)]
    _ = 2 * ((2 * powTwoNat d) * powTwoNat d +
          (2 * powTwoNat d) * powTwoNat d) := by
          rw [Nat.left_distrib]
    _ = 2 * (2 * ((2 * powTwoNat d) * powTwoNat d)) := by
          rw [Nat.two_mul ((2 * powTwoNat d) * powTwoNat d)]

private theorem double_double_lt {a b : Nat} :
    a < b -> 2 * (2 * a) < 2 * (2 * b) := by
  intro h
  exact Nat.mul_lt_mul_of_pos_left
    (Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 2))
    (by decide : 0 < 2)

private theorem lower_child_hi_square (I : Sqrt2BisectInterval) :
    (I.loNum + I.hiNum + 1) * (I.loNum + I.hiNum + 1) =
      2 * (2 * (I.hiNum * I.hiNum)) := by
  rw [I.adjacent]
  have hsum :
      I.loNum + (I.loNum + 1) + 1 =
        (I.loNum + 1) + (I.loNum + 1) := by
    calc
      I.loNum + (I.loNum + 1) + 1 =
          (I.loNum + (I.loNum + 1)) + 1 := rfl
      _ = ((I.loNum + 1) + I.loNum) + 1 := by
          rw [Nat.add_comm I.loNum (I.loNum + 1)]
      _ = (I.loNum + 1) + (I.loNum + 1) :=
          (Nat.add_assoc (I.loNum + 1) I.loNum 1).symm
  rw [hsum]
  exact double_square (I.loNum + 1)

private theorem upper_child_hi_is_mid (I : Sqrt2BisectInterval) :
    I.loNum + I.loNum + 1 = sqrt2BisectMidNum I := by
  unfold sqrt2BisectMidNum
  rw [I.adjacent]
  rw [Nat.add_assoc]

private theorem sqrt2_mid_square_ne_threshold_succ (I : Sqrt2BisectInterval) :
    sqrt2BisectThreshold (Nat.succ I.depth) =
      sqrt2BisectMidNum I * sqrt2BisectMidNum I -> False := by
  intro same
  have midOdd : sqrt2BisectMidNum I = I.loNum + I.loNum + 1 := by
    unfold sqrt2BisectMidNum
    rw [I.adjacent]
    rw [Nat.add_assoc]
  have even := threshold_succ_even I.depth
  have oddEq :
      sqrt2BisectMidNum I * sqrt2BisectMidNum I =
        powTwoNat (Nat.succ I.depth) * powTwoNat (Nat.succ I.depth) +
          powTwoNat (Nat.succ I.depth) * powTwoNat (Nat.succ I.depth) :=
    same.symm.trans even
  rw [midOdd] at oddEq
  exact odd_square_ne_double I.loNum
    (powTwoNat (Nat.succ I.depth) * powTwoNat (Nat.succ I.depth)) oddEq

private theorem sqrt2LowerChild_bracket {I : Sqrt2BisectInterval} :
    Sqrt2NatBracket I -> sqrt2MidBelowNat I ->
      Sqrt2NatBracket (sqrt2LowerChild I) := by
  intro hbr hmid
  unfold Sqrt2NatBracket sqrt2NatLowerSqBelow sqrt2NatUpperSqAbove at hbr
  unfold Sqrt2NatBracket sqrt2NatLowerSqBelow sqrt2NatUpperSqAbove
  constructor
  · change sqrt2MidBelowNat I
    exact hmid
  · change sqrt2BisectThreshold (Nat.succ I.depth) <
      (I.loNum + I.hiNum + 1) * (I.loNum + I.hiNum + 1)
    rw [threshold_succ_double_double]
    rw [lower_child_hi_square]
    exact double_double_lt hbr.right

private theorem sqrt2UpperChild_bracket {I : Sqrt2BisectInterval} :
    Sqrt2NatBracket I -> ¬ sqrt2MidBelowNat I ->
      Sqrt2NatBracket (sqrt2UpperChild I) := by
  intro hbr hnot
  unfold Sqrt2NatBracket sqrt2NatLowerSqBelow sqrt2NatUpperSqAbove at hbr
  unfold Sqrt2NatBracket sqrt2NatLowerSqBelow sqrt2NatUpperSqAbove
  constructor
  · change (I.loNum + I.loNum) * (I.loNum + I.loNum) <
      sqrt2BisectThreshold (Nat.succ I.depth)
    rw [double_square]
    rw [threshold_succ_double_double]
    exact double_double_lt hbr.left
  · change sqrt2BisectThreshold (Nat.succ I.depth) <
      (I.loNum + I.loNum + 1) * (I.loNum + I.loNum + 1)
    rw [upper_child_hi_is_mid]
    have hle :
        sqrt2BisectThreshold (Nat.succ I.depth) ≤
          sqrt2BisectMidNum I * sqrt2BisectMidNum I :=
      Nat.le_of_not_gt hnot
    exact Nat.lt_of_le_of_ne hle
      (sqrt2_mid_square_ne_threshold_succ I)

theorem sqrt2BisectRefine_bracket (I : Sqrt2BisectInterval) :
    Sqrt2NatBracket I -> Sqrt2NatBracket (sqrt2BisectRefine I) := by
  intro hbr
  unfold sqrt2BisectRefine
  cases hcase : sqrt2MidBelow I
  · exact sqrt2UpperChild_bracket hbr
      (by
        change ¬
          (sqrt2BisectMidNum I * sqrt2BisectMidNum I <
            sqrt2BisectThreshold (Nat.succ I.depth))
        change natLtBool
          (sqrt2BisectMidNum I * sqrt2BisectMidNum I)
          (sqrt2BisectThreshold (Nat.succ I.depth)) = false at hcase
        exact not_lt_of_natLtBool_false hcase)
  · exact sqrt2LowerChild_bracket hbr
      (by
        change
          sqrt2BisectMidNum I * sqrt2BisectMidNum I <
            sqrt2BisectThreshold (Nat.succ I.depth)
        change natLtBool
          (sqrt2BisectMidNum I * sqrt2BisectMidNum I)
          (sqrt2BisectThreshold (Nat.succ I.depth)) = true at hcase
        exact lt_of_natLtBool_true hcase)

theorem sqrt2Bisect_lo_sq_lt_two_lt_hi_sq (k : Nat) :
    Sqrt2NatBracket (sqrt2BisectRaw k) := by
  induction k with
  | zero =>
      exact sqrt2Bisect_initial_bracket
  | succ k ih =>
      exact sqrt2BisectRefine_bracket (sqrt2BisectRaw k) ih

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
  raw_bracket : ∀ k : Nat, Sqrt2NatBracket (raw k)
  raw_not_constant : raw 1 ≠ raw 0

def sqrt2BisectBoxStreamCandidate : Sqrt2BisectBoxStreamCandidate :=
  { gauge := sqrt2BisectGauge
    point := sqrt2BisectBoxStream
    raw := sqrt2BisectRaw
    raw_depth := sqrt2BisectRaw_depth
    raw_width := sqrt2Bisect_width_num_one
    raw_bracket := sqrt2Bisect_lo_sq_lt_two_lt_hi_sq
    raw_not_constant := sqrt2Bisect_raw_not_constant }

end BEDC.Derived.Sqrt2BisectionUp
