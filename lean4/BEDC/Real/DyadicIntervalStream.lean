import BEDC.Derived.Sqrt2BisectionUp

namespace BEDC.Real.DyadicIntervalStream

open BEDC.Derived.Sqrt2BisectionUp

structure DReal where
  lo : Nat -> Int
  hi : Nat -> Int
  ordered : forall n : Nat, lo n <= hi n
  mono_lo : forall n : Nat, (2 : Int) * (lo n) <= lo (n + 1)
  mono_hi : forall n : Nat, hi (n + 1) <= (2 : Int) * (hi n)
  width1 : forall n : Nat, hi n - lo n <= 1

namespace DReal

def loQ (x : DReal) (n : Nat) : Rat :=
  Rat.ofInt (x.lo n) / ((2 : Rat) ^ n)

def hiQ (x : DReal) (n : Nat) : Rat :=
  Rat.ofInt (x.hi n) / ((2 : Rat) ^ n)

def ApartRat (x : DReal) (q : Rat) : Prop :=
  exists n : Nat, q < x.loQ n \/ x.hiQ n < q

def ContainsRat (x : DReal) (q : Rat) (n : Nat) : Prop :=
  x.loQ n <= q /\ q <= x.hiQ n

end DReal

private theorem nat_sub_self_add_one_zero (a : Nat) :
    a - (a + 1) = 0 := by
  induction a with
  | zero =>
      rfl
  | succ a ih =>
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem zero_sub_eq_zero_clean (a : Nat) :
    0 - a = 0 := by
  induction a with
  | zero =>
      rfl
  | succ a _ih =>
      rw [Nat.zero_sub]

private theorem nat_sub_eq_zero_of_le_clean {a b : Nat} :
    a <= b -> a - b = 0 := by
  intro h
  induction b generalizing a with
  | zero =>
      cases a with
      | zero =>
          rfl
      | succ a =>
          cases h
  | succ b ih =>
      cases a with
      | zero =>
          exact zero_sub_eq_zero_clean (Nat.succ b)
      | succ a =>
          rw [Nat.succ_sub_succ_eq_sub]
          exact ih (Nat.le_of_succ_le_succ h)

private theorem int_nat_refl_sub_nonneg (a : Nat) :
    (Int.ofNat a - Int.ofNat a).NonNeg := by
  unfold HSub.hSub Int.instSub Int.sub
  cases a with
  | zero =>
      exact Int.NonNeg.mk 0
  | succ a =>
      change (Int.subNatNat (Nat.succ a) (Nat.succ a)).NonNeg
      unfold Int.subNatNat
      rw [Nat.sub_self]
      exact Int.NonNeg.mk 0

private theorem int_nat_succ_sub_self_nonneg (a : Nat) :
    (Int.ofNat (a + 1) - Int.ofNat a).NonNeg := by
  unfold HSub.hSub Int.instSub Int.sub
  cases a with
  | zero =>
      exact Int.NonNeg.mk 1
  | succ a =>
      change (Int.subNatNat (Nat.succ (Nat.succ a)) (Nat.succ a)).NonNeg
      unfold Int.subNatNat
      rw [nat_sub_self_add_one_zero (Nat.succ a)]
      exact Int.NonNeg.mk (Nat.succ (Nat.succ a) - Nat.succ a)

private theorem nat_succ_sub_self_eq_one (a : Nat) :
    Nat.succ a - a = 1 := by
  induction a with
  | zero =>
      rfl
  | succ a ih =>
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem int_nat_succ_sub_eq_one (a : Nat) :
    Int.ofNat (a + 1) - Int.ofNat a = (1 : Int) := by
  unfold HSub.hSub Int.instSub Int.sub
  cases a with
  | zero =>
      rfl
  | succ a =>
      change
        Int.subNatNat (Nat.succ (Nat.succ a)) (Nat.succ a) =
          (1 : Int)
      unfold Int.subNatNat
      rw [nat_sub_self_add_one_zero (Nat.succ a)]
      change
        Int.ofNat (Nat.succ (Nat.succ a) - Nat.succ a) =
          Int.ofNat 1
      rw [nat_succ_sub_self_eq_one (Nat.succ a)]

private theorem int_nat_le_succ (a : Nat) :
    (Int.ofNat a : Int) <= Int.ofNat (a + 1) := by
  apply (Int.le_def (a := Int.ofNat a) (b := Int.ofNat (a + 1))).mpr
  exact int_nat_succ_sub_self_nonneg a

private theorem int_nat_le_of_nat_le {a b : Nat} :
    a <= b -> (Int.ofNat a : Int) <= Int.ofNat b := by
  intro h
  apply (Int.le_def (a := Int.ofNat a) (b := Int.ofNat b)).mpr
  change ((Int.ofNat b).sub (Int.ofNat a)).NonNeg
  unfold Int.sub
  change (Int.ofNat b + -Int.ofNat a).NonNeg
  cases a with
  | zero =>
      change (Int.ofNat b + Int.ofNat 0).NonNeg
      unfold HAdd.hAdd instHAdd Add.add Int.instAdd Int.add
      exact Int.NonNeg.mk b
  | succ a =>
      change (Int.ofNat b + Int.negSucc a).NonNeg
      unfold HAdd.hAdd instHAdd Add.add Int.instAdd Int.add
      change (Int.subNatNat b (Nat.succ a)).NonNeg
      unfold Int.subNatNat
      rw [nat_sub_eq_zero_of_le_clean h]
      exact Int.NonNeg.mk (b - Nat.succ a)

private theorem two_mul_le_add_succ (a : Nat) :
    2 * a <= a + (a + 1) := by
  rw [Nat.two_mul]
  exact Nat.le_succ _

def sqrt2LoNat (n : Nat) : Nat :=
  (sqrt2BisectRaw n).loNum

def sqrt2HiNat (n : Nat) : Nat :=
  (sqrt2BisectRaw n).hiNum

theorem sqrt2_nat_adjacent (n : Nat) :
    sqrt2HiNat n = sqrt2LoNat n + 1 := by
  unfold sqrt2HiNat sqrt2LoNat
  exact sqrt2Bisect_width_num_one n

def sqrt2LoInt (n : Nat) : Int :=
  Int.ofNat (sqrt2LoNat n)

def sqrt2HiInt (n : Nat) : Int :=
  Int.ofNat (sqrt2HiNat n)

private theorem sqrt2_ordered (n : Nat) :
    sqrt2LoInt n <= sqrt2HiInt n := by
  unfold sqrt2LoInt sqrt2HiInt
  rw [sqrt2_nat_adjacent n]
  exact int_nat_le_succ (sqrt2LoNat n)

theorem sqrt2LoNat_mono_doubled (n : Nat) :
    2 * sqrt2LoNat n <= sqrt2LoNat (n + 1) := by
  unfold sqrt2LoNat
  change
    2 * (sqrt2BisectRaw n).loNum <=
      (sqrt2BisectRefine (sqrt2BisectRaw n)).loNum
  unfold sqrt2BisectRefine
  cases _h : sqrt2MidBelow (sqrt2BisectRaw n)
  · change
      2 * (sqrt2BisectRaw n).loNum <=
        (sqrt2UpperChild (sqrt2BisectRaw n)).loNum
    unfold sqrt2UpperChild
    change
      2 * (sqrt2BisectRaw n).loNum <=
        (sqrt2BisectRaw n).loNum + (sqrt2BisectRaw n).loNum
    rw [Nat.two_mul]
    exact Nat.le_refl _
  · change
      2 * (sqrt2BisectRaw n).loNum <=
        (sqrt2LowerChild (sqrt2BisectRaw n)).loNum
    unfold sqrt2LowerChild
    change
      2 * (sqrt2BisectRaw n).loNum <=
        (sqrt2BisectRaw n).loNum + (sqrt2BisectRaw n).hiNum
    have adjacent := sqrt2Bisect_width_num_one n
    conv => rhs; rw [adjacent]
    exact two_mul_le_add_succ (sqrt2BisectRaw n).loNum

private theorem sqrt2UpperChild_hi_le (I : Sqrt2BisectInterval) :
    (sqrt2UpperChild I).hiNum <= 2 * I.hiNum := by
  unfold sqrt2UpperChild
  change I.loNum + I.loNum + 1 <= 2 * I.hiNum
  conv => rhs; rw [I.adjacent]
  rw [Nat.two_mul]
  change I.loNum + I.loNum + 1 <= (I.loNum + 1) + (I.loNum + 1)
  calc
    I.loNum + I.loNum + 1 = I.loNum + (I.loNum + 1) := by
      rw [Nat.add_assoc]
    _ <= I.loNum + 1 + (I.loNum + 1) := by
      exact Nat.add_le_add_right (Nat.le_succ I.loNum) (I.loNum + 1)

private theorem sqrt2LowerChild_hi_le (I : Sqrt2BisectInterval) :
    (sqrt2LowerChild I).hiNum <= 2 * I.hiNum := by
  unfold sqrt2LowerChild
  change I.loNum + I.hiNum + 1 <= 2 * I.hiNum
  conv => lhs; rw [I.adjacent]
  conv => rhs; rw [I.adjacent]
  rw [Nat.two_mul]
  change
    I.loNum + (I.loNum + 1) + 1 <=
      (I.loNum + 1) + (I.loNum + 1)
  calc
    I.loNum + (I.loNum + 1) + 1 =
        I.loNum + ((I.loNum + 1) + 1) := by
      rw [Nat.add_assoc]
    _ = I.loNum + (1 + (I.loNum + 1)) := by
      rw [Nat.add_comm (I.loNum + 1) 1]
    _ = I.loNum + 1 + (I.loNum + 1) := by
      rw [Nat.add_assoc]
    _ <= I.loNum + 1 + (I.loNum + 1) := Nat.le_refl _

theorem sqrt2HiNat_mono_doubled (n : Nat) :
    sqrt2HiNat (n + 1) <= 2 * sqrt2HiNat n := by
  unfold sqrt2HiNat
  change
    (sqrt2BisectRefine (sqrt2BisectRaw n)).hiNum <=
      2 * (sqrt2BisectRaw n).hiNum
  unfold sqrt2BisectRefine
  cases _h : sqrt2MidBelow (sqrt2BisectRaw n)
  · change
      (sqrt2UpperChild (sqrt2BisectRaw n)).hiNum <=
        2 * (sqrt2BisectRaw n).hiNum
    exact sqrt2UpperChild_hi_le (sqrt2BisectRaw n)
  · change
      (sqrt2LowerChild (sqrt2BisectRaw n)).hiNum <=
        2 * (sqrt2BisectRaw n).hiNum
    exact sqrt2LowerChild_hi_le (sqrt2BisectRaw n)

private theorem sqrt2_mono_lo (n : Nat) :
    (2 : Int) * sqrt2LoInt n <= sqrt2LoInt (n + 1) := by
  unfold sqrt2LoInt
  change Int.ofNat (2 * sqrt2LoNat n) <= Int.ofNat (sqrt2LoNat (n + 1))
  exact int_nat_le_of_nat_le (sqrt2LoNat_mono_doubled n)

private theorem sqrt2_mono_hi (n : Nat) :
    sqrt2HiInt (n + 1) <= (2 : Int) * sqrt2HiInt n := by
  unfold sqrt2HiInt
  change Int.ofNat (sqrt2HiNat (n + 1)) <= Int.ofNat (2 * sqrt2HiNat n)
  exact int_nat_le_of_nat_le (sqrt2HiNat_mono_doubled n)

private theorem int_nat_succ_width_le_one (a : Nat) :
    Int.ofNat (a + 1) - Int.ofNat a <= (1 : Int) := by
  apply (Int.le_def
    (a := Int.ofNat (a + 1) - Int.ofNat a)
    (b := (1 : Int))).mpr
  change ((1 : Int) - (Int.ofNat (a + 1) - Int.ofNat a)).NonNeg
  rw [int_nat_succ_sub_eq_one a]
  exact int_nat_refl_sub_nonneg 1

private theorem sqrt2_width1 (n : Nat) :
    sqrt2HiInt n - sqrt2LoInt n <= (1 : Int) := by
  unfold sqrt2HiInt sqrt2LoInt
  rw [sqrt2_nat_adjacent n]
  exact int_nat_succ_width_le_one (sqrt2LoNat n)

def sqrt2D : DReal :=
  { lo := sqrt2LoInt
    hi := sqrt2HiInt
    ordered := sqrt2_ordered
    mono_lo := sqrt2_mono_lo
    mono_hi := sqrt2_mono_hi
    width1 := sqrt2_width1 }

private theorem nat_pow_two_clean (n : Nat) :
    n ^ 2 = n * n := by
  rw [show 2 = Nat.succ 1 by rfl]
  rw [Nat.pow_succ]
  rw [show 1 = Nat.succ 0 by rfl]
  rw [Nat.pow_succ]
  rw [Nat.pow_zero]
  rw [Nat.one_mul]

def sqrt2BracketNat (n : Nat) :
    sqrt2LoNat n * sqrt2LoNat n < 2 * powTwoNat n * powTwoNat n /\
      2 * powTwoNat n * powTwoNat n < sqrt2HiNat n * sqrt2HiNat n := by
  unfold sqrt2LoNat sqrt2HiNat
  have h := sqrt2Bisect_lo_sq_lt_two_lt_hi_sq n
  unfold Sqrt2NatBracket sqrt2NatLowerSqBelow sqrt2NatUpperSqAbove
    sqrt2BisectThreshold at h
  rw [sqrt2BisectRaw_depth n] at h
  exact h

theorem sqrt2_bracket (n : Nat) :
    (sqrt2D.lo n).natAbs ^ 2 < 2 * powTwoNat n * powTwoNat n /\
      2 * powTwoNat n * powTwoNat n < (sqrt2D.hi n).natAbs ^ 2 := by
  unfold sqrt2D sqrt2LoInt sqrt2HiInt
  change
    sqrt2LoNat n ^ 2 < 2 * powTwoNat n * powTwoNat n /\
      2 * powTwoNat n * powTwoNat n < sqrt2HiNat n ^ 2
  rw [nat_pow_two_clean (sqrt2LoNat n)]
  rw [nat_pow_two_clean (sqrt2HiNat n)]
  exact sqrt2BracketNat n

end BEDC.Real.DyadicIntervalStream
