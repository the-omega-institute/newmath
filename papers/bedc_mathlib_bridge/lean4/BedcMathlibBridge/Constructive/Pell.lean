import BEDC.Derived.PellUp
import BedcMathlibBridge.Constructive.Gaussian
import Mathlib.NumberTheory.PellMatiyasevic

/-!
Pell recurrence readback correspondence.

The bridge surface is the recursive `x`/`y` readback for the special
Matiyasevic Pell sequence. It deliberately stops before mathlib's Pell
equation theorem, whose footprint is recorded as boundary data.
-/

namespace BedcMathlibBridge.Constructive.Pell

local notation "Z" => BEDC.Derived.PellUp.Z

def toInt (x : Z) : Int :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt x

def ofInt (z : Int) : Z :=
  BedcMathlibBridge.Constructive.Gaussian.zOfInt z

def ofNat (n : Nat) : Z :=
  ofInt (n : Int)

def parameterD (a : Nat) : Z :=
  ofNat (a * a - 1)

def parameterA (a : Nat) : Z :=
  ofNat a

def parameterB : Z :=
  ofNat 1

def basePair (a : Nat) : BEDC.Derived.PellUp.PellPair :=
  { x := parameterA a, y := parameterB }

def bedcPair (a : Nat) : Nat -> BEDC.Derived.PellUp.PellPair
  | 0 => BEDC.Derived.PellUp.pellPairOne
  | n + 1 =>
      BEDC.Derived.PellUp.pellPairMul
        (parameterD a) (bedcPair a n) (basePair a)

def bedcX (a n : Nat) : Int :=
  toInt (bedcPair a n).x

def bedcY (a n : Nat) : Int :=
  toInt (bedcPair a n).y

theorem toInt_add (x y : Z) :
    toInt (BEDC.Derived.PellUp.Zadd x y) = toInt x + toInt y :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt_add x y

theorem toInt_mul (x y : Z) :
    toInt (BEDC.Derived.PellUp.Zmul x y) = toInt x * toInt y :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt_mul x y

theorem toInt_zero :
    toInt BEDC.Derived.PellUp.Zzero = 0 :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt_zero

theorem toInt_one :
    toInt BEDC.Derived.PellUp.Zone = 1 :=
  BedcMathlibBridge.Constructive.Gaussian.zToInt_one

theorem toInt_ofInt (z : Int) :
    toInt (ofInt z) = z :=
  BedcMathlibBridge.Constructive.Gaussian.zOfInt_toInt z

theorem toInt_ofNat (n : Nat) :
    toInt (ofNat n) = n :=
  toInt_ofInt (n : Int)

theorem parameterD_toInt (a : Nat) :
    toInt (parameterD a) = ((a * a - 1 : Nat) : Int) :=
  toInt_ofNat (a * a - 1)

theorem parameterA_toInt (a : Nat) :
    toInt (parameterA a) = (a : Int) :=
  toInt_ofNat a

theorem parameterB_toInt :
    toInt parameterB = (1 : Int) :=
  toInt_ofNat 1

theorem int_negOfNat_succ_clean (n : Nat) :
    Int.negOfNat (Nat.succ n) = Int.negSucc n := by
  rfl

theorem int_mul_one_clean (z : Int) :
    z * 1 = z := by
  cases z with
  | ofNat n =>
      change Int.ofNat (n * 1) = Int.ofNat n
      rw [Nat.mul_one]
  | negSucc n =>
      change Int.negOfNat (Nat.succ n * 1) = Int.negSucc n
      rw [Nat.mul_one]
      exact int_negOfNat_succ_clean n

theorem bedcX_zero (a : Nat) :
    bedcX a 0 = 1 := by
  unfold bedcX bedcPair
  change toInt BEDC.Derived.PellUp.Zone = 1
  exact toInt_one

theorem bedcY_zero (a : Nat) :
    bedcY a 0 = 0 := by
  unfold bedcY bedcPair
  change toInt BEDC.Derived.PellUp.Zzero = 0
  exact toInt_zero

theorem bedcX_succ (a n : Nat) :
    bedcX a (n + 1) =
      bedcX a n * (a : Int) + ((a * a - 1 : Nat) : Int) * bedcY a n := by
  dsimp [bedcX, bedcY, bedcPair, BEDC.Derived.PellUp.pellSolutionPow,
    BEDC.Derived.PellUp.pellSolutionStep, BEDC.Derived.PellUp.pellPairMul,
    basePair]
  rw [toInt_add, toInt_mul, toInt_mul, toInt_mul]
  rw [parameterA_toInt, parameterD_toInt, parameterB_toInt]
  rw [int_mul_one_clean]

theorem bedcY_succ (a n : Nat) :
    bedcY a (n + 1) = bedcX a n + bedcY a n * (a : Int) := by
  dsimp [bedcX, bedcY, bedcPair, BEDC.Derived.PellUp.pellSolutionPow,
    BEDC.Derived.PellUp.pellSolutionStep, BEDC.Derived.PellUp.pellPairMul,
    basePair]
  rw [toInt_add, toInt_mul, toInt_mul]
  rw [parameterA_toInt, parameterB_toInt]
  rw [int_mul_one_clean]

theorem mathlib_xz_succ_visible {a : Nat} (a1 : 1 < a) (n : Nat) :
    _root_.Pell.xz a1 (n + 1) =
      _root_.Pell.xz a1 n * (a : Int) +
        ((a * a - 1 : Nat) : Int) * _root_.Pell.yz a1 n := by
  unfold _root_.Pell.xz _root_.Pell.yz _root_.Pell.xn _root_.Pell.yn
  cases n <;> rfl

theorem mathlib_yz_succ_visible {a : Nat} (a1 : 1 < a) (n : Nat) :
    _root_.Pell.yz a1 (n + 1) =
      _root_.Pell.xz a1 n + _root_.Pell.yz a1 n * (a : Int) := by
  unfold _root_.Pell.xz _root_.Pell.yz _root_.Pell.xn _root_.Pell.yn
  cases n <;> rfl

theorem readback_eq_mathlib {a : Nat} (a1 : 1 < a) (n : Nat) :
    bedcX a n = _root_.Pell.xz a1 n ∧
      bedcY a n = _root_.Pell.yz a1 n := by
  induction n with
  | zero =>
      constructor
      · rw [bedcX_zero]
        rfl
      · rw [bedcY_zero]
        rfl
  | succ n ih =>
      constructor
      · rw [bedcX_succ, mathlib_xz_succ_visible, ih.left, ih.right]
      · rw [bedcY_succ, mathlib_yz_succ_visible, ih.left, ih.right]

theorem bedcX_eq_mathlib_xz {a : Nat} (a1 : 1 < a) (n : Nat) :
    bedcX a n = _root_.Pell.xz a1 n :=
  (readback_eq_mathlib a1 n).left

theorem bedcY_eq_mathlib_yz {a : Nat} (a1 : 1 < a) (n : Nat) :
    bedcY a n = _root_.Pell.yz a1 n :=
  (readback_eq_mathlib a1 n).right

end BedcMathlibBridge.Constructive.Pell
