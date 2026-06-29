namespace BEDC.Real.RatInterval

structure RatNum where
  num : Int
  den : Nat
  den_pos : 0 < den

abbrev Rat : Type :=
  RatNum

namespace RatNum

instance : NatCast RatNum where
  natCast n := { num := Int.ofNat n, den := 1, den_pos := Nat.succ_pos 0 }

instance (n : Nat) : OfNat RatNum n where
  ofNat := { num := Int.ofNat n, den := 1, den_pos := Nat.succ_pos 0 }

def add (a b : RatNum) : RatNum :=
  { num := a.num * Int.ofNat b.den + b.num * Int.ofNat a.den
    den := a.den * b.den
    den_pos := Nat.mul_pos a.den_pos b.den_pos }

def neg (a : RatNum) : RatNum :=
  { num := -a.num, den := a.den, den_pos := a.den_pos }

def sub (a b : RatNum) : RatNum :=
  add a (neg b)

def mul (a b : RatNum) : RatNum :=
  { num := a.num * b.num
    den := a.den * b.den
    den_pos := Nat.mul_pos a.den_pos b.den_pos }

def inv (a : RatNum) : RatNum :=
  match a.num with
  | Int.ofNat 0 => (0 : RatNum)
  | Int.ofNat (Nat.succ k) =>
      { num := Int.ofNat a.den, den := Nat.succ k, den_pos := Nat.succ_pos k }
  | Int.negSucc k =>
      { num := -(Int.ofNat a.den), den := Nat.succ k, den_pos := Nat.succ_pos k }

def div (a b : RatNum) : RatNum :=
  mul a (inv b)

def pow : RatNum -> Nat -> RatNum
  | _a, 0 => (1 : RatNum)
  | a, Nat.succ n => mul a (pow a n)

instance : Add RatNum where
  add := add

instance : Neg RatNum where
  neg := neg

instance : Sub RatNum where
  sub := sub

instance : Mul RatNum where
  mul := mul

instance : Inv RatNum where
  inv := inv

instance : Div RatNum where
  div := div

instance : Pow RatNum Nat where
  pow := pow

def le (a b : RatNum) : Prop :=
  a.num * Int.ofNat b.den <= b.num * Int.ofNat a.den

def lt (a b : RatNum) : Prop :=
  a.num * Int.ofNat b.den < b.num * Int.ofNat a.den

instance : LE RatNum where
  le := le

instance : LT RatNum where
  lt := lt

instance instDecidableLe (a b : RatNum) : Decidable (a <= b) := by
  change Decidable (le a b)
  unfold le
  infer_instance

instance instDecidableLt (a b : RatNum) : Decidable (a < b) := by
  change Decidable (lt a b)
  unfold lt
  infer_instance

end RatNum

def sumN : Nat -> (Nat -> Rat) -> Rat
  | 0, _f => 0
  | Nat.succ n, f => sumN n f + f n

def qLeBool (a b : Rat) : Bool :=
  decide (a <= b)

def qLtBool (a b : Rat) : Bool :=
  decide (a < b)

theorem qLe_of_qLeBool {a b : Rat} :
    qLeBool a b = true -> a <= b := by
  intro h
  exact of_decide_eq_true h

theorem qLt_of_qLtBool {a b : Rat} :
    qLtBool a b = true -> a < b := by
  intro h
  exact of_decide_eq_true h

theorem boolAndLeftTrue {a b : Bool} :
    (a && b) = true -> a = true := by
  cases a with
  | false =>
      cases b with
      | false =>
          intro h
          cases h
      | true =>
          intro h
          cases h
  | true =>
      cases b with
      | false =>
          intro h
          cases h
      | true =>
          intro _h
          rfl

theorem boolAndRightTrue {a b : Bool} :
    (a && b) = true -> b = true := by
  cases a with
  | false =>
      cases b with
      | false =>
          intro h
          cases h
      | true =>
          intro h
          cases h
  | true =>
      cases b with
      | false =>
          intro h
          cases h
      | true =>
          intro _h
          rfl

structure I where
  lo : Rat
  hi : Rat
  ok : lo <= hi

structure CBox where
  re : I
  im : I

structure LeCert where
  lhs : Rat
  rhs : Rat

namespace LeCert

def check (c : LeCert) : Bool :=
  qLeBool c.lhs c.rhs

def Sound (c : LeCert) : Prop :=
  c.lhs <= c.rhs

theorem cert_sound (c : LeCert) :
    check c = true -> Sound c := by
  intro h
  exact qLe_of_qLeBool h

end LeCert

def sampleLeCert : LeCert :=
  { lhs := 1 / 3, rhs := 1 }

theorem sampleLeCert_ok :
    LeCert.check sampleLeCert = true := by
  rfl

theorem sampleLeCert_sound :
    LeCert.Sound sampleLeCert :=
  LeCert.cert_sound sampleLeCert sampleLeCert_ok

structure IntervalCert where
  lo : Rat
  hi : Rat

namespace IntervalCert

def check (c : IntervalCert) : Bool :=
  qLeBool c.lo c.hi

def Sound (c : IntervalCert) : Prop :=
  c.lo <= c.hi

def toInterval (c : IntervalCert) (h : check c = true) : I :=
  { lo := c.lo, hi := c.hi, ok := qLe_of_qLeBool h }

theorem cert_sound (c : IntervalCert) :
    check c = true -> Sound c := by
  intro h
  exact qLe_of_qLeBool h

end IntervalCert

def sampleIntervalCert : IntervalCert :=
  { lo := 0, hi := 1 }

theorem sampleIntervalCert_ok :
    IntervalCert.check sampleIntervalCert = true := by
  rfl

theorem sampleIntervalCert_sound :
    IntervalCert.Sound sampleIntervalCert :=
  IntervalCert.cert_sound sampleIntervalCert sampleIntervalCert_ok

end BEDC.Real.RatInterval
