import Std

set_option autoImplicit false

namespace BEDC
namespace ZetaCert
namespace Dy

abbrev P : Nat :=
  96

def S : Int :=
  79228162514264337593543950336

def two72 : Int :=
  4722366482869645213696

structure I where
  lo : Int
  hi : Int
deriving Repr, DecidableEq

def ok (x : I) : Bool :=
  decide (x.lo <= x.hi)

def pointM (z : Int) : I :=
  { lo := z, hi := z }

def zero : I :=
  pointM 0

def one : I :=
  pointM S

def neg (x : I) : I :=
  { lo := -x.hi, hi := -x.lo }

def add (x y : I) : I :=
  { lo := x.lo + y.lo, hi := x.hi + y.hi }

def sub (x y : I) : I :=
  { lo := x.lo - y.hi, hi := x.hi - y.lo }

def floorS (z : Int) : Int :=
  z / S

def ceilS (z : Int) : Int :=
  -((-z) / S)

def min4 (a b c d : Int) : Int :=
  min (min a b) (min c d)

def max4 (a b c d : Int) : Int :=
  max (max a b) (max c d)

def mul (x y : I) : I :=
  let p1 := x.lo * y.lo
  let p2 := x.lo * y.hi
  let p3 := x.hi * y.lo
  let p4 := x.hi * y.hi
  { lo := floorS (min4 p1 p2 p3 p4),
    hi := ceilS (max4 p1 p2 p3 p4) }

def eqb (x y : I) : Bool :=
  decide (x = y)

def subset (x y : I) : Bool :=
  decide (y.lo <= x.lo /\ x.hi <= y.hi)

def iabs (z : Int) : Int :=
  if z < 0 then -z else z

def mag (x : I) : Int :=
  max (iabs x.lo) (iabs x.hi)

def leInv125 (u : Int) : Bool :=
  decide (125 * u <= S)

def posMant (r : Int) : Bool :=
  decide (0 < r)

def ofQ2LeP (q : Int) (shift : Int) : I :=
  pointM (q * shift)

def MemM (m : Int) (x : I) : Prop :=
  x.lo <= m /\ m <= x.hi

def MemProdM (p : Int) (x : I) : Prop :=
  x.lo * S <= p /\ p <= x.hi * S

theorem S_pos_int : (0 : Int) < S := by
  decide

theorem S_ne_zero : S != 0 := by
  decide

theorem S_ne_zero_prop : S ≠ 0 := by
  decide

theorem ok_sound {x : I} :
    ok x = true -> x.lo <= x.hi := by
  intro h
  exact of_decide_eq_true h

theorem leInv125_sound {u : Int} :
    leInv125 u = true -> 125 * u <= S := by
  intro h
  exact of_decide_eq_true h

theorem posMant_sound {r : Int} :
    posMant r = true -> 0 < r := by
  intro h
  exact of_decide_eq_true h

end Dy
end ZetaCert
end BEDC
