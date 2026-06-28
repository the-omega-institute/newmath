import BEDC.Derived.Sqrt2BisectionUp

namespace BEDC.Real.DyadicIntervalStream

open BEDC.Derived.Sqrt2BisectionUp

structure Rat where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace Rat

private theorem ext {a b : Rat} (hnum : a.num = b.num) (hden : a.den = b.den) :
    a = b := by
  cases a
  cases b
  cases hnum
  cases hden
  rfl

instance : OfNat Rat n where
  ofNat := { num := Int.ofNat n, den := 1, den_pos := Nat.succ_pos 0 }

private def mul (a b : Rat) : Rat :=
  { num := a.num * b.num
    den := a.den * b.den
    den_pos := Nat.mul_pos a.den_pos b.den_pos }

private def inv (a : Rat) : Rat :=
  match a.num with
  | Int.ofNat 0 => (0 : Rat)
  | Int.ofNat (Nat.succ k) =>
      { num := Int.ofNat a.den, den := Nat.succ k, den_pos := Nat.succ_pos k }
  | Int.negSucc k =>
      { num := -(Int.ofNat a.den), den := Nat.succ k, den_pos := Nat.succ_pos k }

private def div (a b : Rat) : Rat :=
  mul a (inv b)

private def pow : Rat -> Nat -> Rat
  | _q, 0 => (1 : Rat)
  | q, Nat.succ n => mul q (pow q n)

instance : Mul Rat where
  mul := mul

instance : Inv Rat where
  inv := inv

instance : Div Rat where
  div := div

instance : Pow Rat Nat where
  pow := pow

def lt (a b : Rat) : Prop :=
  a.num * Int.ofNat b.den < b.num * Int.ofNat a.den

instance : LT Rat where
  lt := lt

def le (a b : Rat) : Prop :=
  a.num * Int.ofNat b.den <= b.num * Int.ofNat a.den

instance : LE Rat where
  le := le

def ofIntOverPowTwo (z : Int) (n : Nat) : Rat :=
  { num := z, den := powTwoNat n, den_pos := powTwoNat_pos n }

def invPowTwo (n : Nat) : Rat :=
  ofIntOverPowTwo 1 n

private theorem int_ofNat_zero_mul (z : Int) :
    (Int.ofNat 0) * z = 0 := by
  cases z with
  | ofNat n =>
      change Int.ofNat (0 * n) = Int.ofNat 0
      rw [Nat.zero_mul]
  | negSucc n =>
      change Int.negOfNat (0 * Nat.succ n) = Int.ofNat 0
      rw [Nat.zero_mul]
      rfl

private theorem int_mul_ofNat_one (z : Int) :
    z * Int.ofNat 1 = z := by
  cases z with
  | ofNat n =>
      change Int.ofNat (n * 1) = Int.ofNat n
      rw [Nat.mul_one]
  | negSucc n =>
      change Int.negOfNat (Nat.succ n * 1) = Int.negSucc n
      rw [Nat.mul_one]
      rfl

private theorem int_ofNat_one_mul (z : Int) :
    Int.ofNat 1 * z = z := by
  cases z with
  | ofNat n =>
      change Int.ofNat (1 * n) = Int.ofNat n
      rw [Nat.one_mul]
  | negSucc n =>
      change Int.negOfNat (1 * Nat.succ n) = Int.negSucc n
      rw [Nat.one_mul]
      rfl

end Rat

structure DReal where
  lo : Nat -> Int
  hi : Nat -> Int
  ordered : forall n : Nat, lo n <= hi n
  mono_lo : forall n : Nat, (2 : Int) * (lo n) <= lo (n + 1)
  mono_hi : forall n : Nat, hi (n + 1) <= (2 : Int) * (hi n)
  width1 : forall n : Nat, hi n - lo n <= 1

namespace DReal

def loQ (x : DReal) (n : Nat) : Rat :=
  Rat.ofIntOverPowTwo (x.lo n) n

def hiQ (x : DReal) (n : Nat) : Rat :=
  Rat.ofIntOverPowTwo (x.hi n) n

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

private theorem int_nat_lt_of_nat_lt {a b : Nat} :
    a < b -> (Int.ofNat a : Int) < Int.ofNat b := by
  intro h
  change (Int.ofNat a : Int) + 1 <= Int.ofNat b
  change Int.ofNat (a + 1) <= Int.ofNat b
  exact int_nat_le_of_nat_le (Nat.succ_le_of_lt h)

private theorem powTwoNat_self_covers (threshold : Nat) :
    threshold <= powTwoNat threshold := by
  induction threshold with
  | zero =>
      exact Nat.zero_le _
  | succ threshold ih =>
      change Nat.succ threshold <= 2 * powTwoNat threshold
      have stepToPow :
          Nat.succ threshold <= Nat.succ (powTwoNat threshold) :=
        Nat.succ_le_succ ih
      have powStep :
          Nat.succ (powTwoNat threshold) <= 2 * powTwoNat threshold := by
        rw [Nat.two_mul]
        change powTwoNat threshold + 1 <=
          powTwoNat threshold + powTwoNat threshold
        exact Nat.add_le_add_left
          (powTwoNat_pos threshold) (powTwoNat threshold)
      exact Nat.le_trans stepToPow powStep

private theorem nat_lt_powTwoNat_succ_self (n : Nat) :
    n < powTwoNat (n + 1) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (powTwoNat_self_covers (n + 1))

private theorem div_one_pos_nat (x : Nat) (hx : 0 < x) :
    Rat.div (1 : Rat)
        { num := Int.ofNat x, den := 1, den_pos := Nat.succ_pos 0 } =
      { num := 1, den := x, den_pos := hx } := by
  cases x with
  | zero =>
      cases hx
  | succ k =>
      unfold Rat.div Rat.inv Rat.mul
      apply Rat.ext
      · rfl
      · change 1 * (k + 1) = k + 1
        rw [Nat.one_mul]

private theorem two_pow_rat_shape (n : Nat) :
    ((2 : Rat) ^ n) =
      { num := Int.ofNat (powTwoNat n), den := 1, den_pos := Nat.succ_pos 0 } := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Rat.mul (2 : Rat) ((2 : Rat) ^ n) =
        { num := Int.ofNat (powTwoNat (Nat.succ n)),
          den := 1,
          den_pos := Nat.succ_pos 0 }
      rw [ih]
      apply Rat.ext
      · unfold Rat.mul
        change (2 : Int) * Int.ofNat (powTwoNat n) =
          Int.ofNat (2 * powTwoNat n)
        rfl
      · unfold Rat.mul
        rfl

private theorem one_div_two_pow_shape (n : Nat) :
    ((1 : Rat) / ((2 : Rat) ^ n)) = Rat.invPowTwo n := by
  change Rat.div (1 : Rat) ((2 : Rat) ^ n) = Rat.invPowTwo n
  rw [two_pow_rat_shape n]
  unfold Rat.invPowTwo Rat.ofIntOverPowTwo
  exact div_one_pos_nat (powTwoNat n) (powTwoNat_pos n)

private theorem rat_pos_num_pos {eps : Rat} :
    (0 : Rat) < eps -> 0 < eps.num := by
  intro h
  change Rat.lt (0 : Rat) eps at h
  unfold Rat.lt at h
  change (Int.ofNat 0 * Int.ofNat eps.den) <
    eps.num * Int.ofNat 1 at h
  rw [Rat.int_ofNat_zero_mul (Int.ofNat eps.den)] at h
  rw [Rat.int_mul_ofNat_one eps.num] at h
  exact h

private theorem one_le_pos_int_mul_pow {z : Int} {p : Nat} :
    0 < z -> (Int.ofNat p : Int) <= z * Int.ofNat p := by
  intro hz
  cases z with
  | ofNat m =>
      cases m with
      | zero =>
          cases hz
      | succ m =>
          change (Int.ofNat p : Int) <= Int.ofNat (Nat.succ m * p)
          apply int_nat_le_of_nat_le
          calc
            p = 1 * p := (Nat.one_mul p).symm
            _ <= Nat.succ m * p :=
              Nat.mul_le_mul_right p (Nat.succ_le_succ (Nat.zero_le m))
  | negSucc m =>
      cases hz

private theorem int_ofNat_lt_pos_mul_of_nat_lt {a p : Nat} {z : Int} :
    a < p -> 0 < z -> (Int.ofNat p : Int) <= z * Int.ofNat p ->
      (Int.ofNat a : Int) < z * Int.ofNat p := by
  intro hap hz _hle
  cases z with
  | ofNat m =>
      cases m with
      | zero =>
          cases hz
      | succ m =>
          change Int.ofNat a < Int.ofNat (Nat.succ m * p)
          apply int_nat_lt_of_nat_lt
          have pLe : p <= Nat.succ m * p := by
            calc
              p = 1 * p := (Nat.one_mul p).symm
              _ <= Nat.succ m * p :=
                Nat.mul_le_mul_right p (Nat.succ_le_succ (Nat.zero_le m))
          exact Nat.lt_of_lt_of_le hap pLe
  | negSucc m =>
      cases hz

theorem pow2_modulus (eps : Rat) (hε : (0 : Rat) < eps) :
    exists n : Nat, (1 : Rat) / ((2 : Rat) ^ n) < eps := by
  let n := eps.den + 1
  refine Exists.intro n ?_
  rw [one_div_two_pow_shape n]
  change Rat.lt (Rat.invPowTwo n) eps
  unfold Rat.lt Rat.invPowTwo Rat.ofIntOverPowTwo
  change (Int.ofNat 1 * Int.ofNat eps.den) <
    eps.num * Int.ofNat (powTwoNat n)
  rw [Rat.int_ofNat_one_mul (Int.ofNat eps.den)]
  have denLtPowNat : eps.den < powTwoNat n := by
    unfold n
    exact nat_lt_powTwoNat_succ_self eps.den
  have epsNumPos : 0 < eps.num := rat_pos_num_pos hε
  have powLeProduct :
      (Int.ofNat (powTwoNat n) : Int) <=
        eps.num * Int.ofNat (powTwoNat n) :=
    one_le_pos_int_mul_pow epsNumPos
  exact int_ofNat_lt_pos_mul_of_nat_lt denLtPowNat epsNumPos powLeProduct

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
