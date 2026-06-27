import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.StirlingFirstUp
import BEDC.Derived.StirlingUp

namespace BEDC.Derived.StirlingInversionUp

open BEDC.Algebra.Rel

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

abbrev zZero : Z := integerRing.zero
abbrev zOne : Z := integerRing.one
abbrev zAdd : Z -> Z -> Z := integerRing.add
abbrev zMul : Z -> Z -> Z := integerRing.mul
abbrev zNeg : Z -> Z := integerRing.neg
abbrev zSub : Z -> Z -> Z := integerRing.sub

def zOfNat (n : Nat) : Z :=
  BEDC.Derived.RationalUp.intOfNat
    (BEDC.Derived.IntUp.natToUnary n)
    (BEDC.Derived.IntUp.natToUnary_unary n)

-- 有符号第一类 Stirling 数, 符号由 IntegerUp 的加法逆元承载。
def signedStirlingFirst : Nat -> Nat -> Z
  | 0, 0 => zOne
  | 0, Nat.succ _ => zZero
  | Nat.succ _, 0 => zZero
  | Nat.succ n, Nat.succ k =>
      zSub (signedStirlingFirst n k)
        (zMul (zOfNat n) (signedStirlingFirst n (Nat.succ k)))

-- 第二类 Stirling 数的 IntegerUp 提升, 递推与 StirlingUp.stirlingSecond 同形。
def stirlingSecondInteger : Nat -> Nat -> Z
  | 0, 0 => zOne
  | 0, Nat.succ _ => zZero
  | Nat.succ _, 0 => zZero
  | Nat.succ n, Nat.succ k =>
      zAdd
        (zMul (zOfNat (Nat.succ k)) (stirlingSecondInteger n (Nat.succ k)))
        (stirlingSecondInteger n k)

def kroneckerInteger : Nat -> Nat -> Z
  | 0, 0 => zOne
  | 0, Nat.succ _ => zZero
  | Nat.succ _, 0 => zZero
  | Nat.succ n, Nat.succ m => kroneckerInteger n m

def rightOrthogonalPrefix (n m : Nat) : Nat -> Z
  | 0 =>
      zMul (stirlingSecondInteger n 0) (signedStirlingFirst 0 m)
  | Nat.succ fuel =>
      zAdd (rightOrthogonalPrefix n m fuel)
        (zMul (stirlingSecondInteger n (Nat.succ fuel))
          (signedStirlingFirst (Nat.succ fuel) m))

def rightOrthogonalSum (n m : Nat) : Z :=
  rightOrthogonalPrefix n m n

def leftOrthogonalPrefix (n m : Nat) : Nat -> Z
  | 0 =>
      zMul (signedStirlingFirst n 0) (stirlingSecondInteger 0 m)
  | Nat.succ fuel =>
      zAdd (leftOrthogonalPrefix n m fuel)
        (zMul (signedStirlingFirst n (Nat.succ fuel))
          (stirlingSecondInteger (Nat.succ fuel) m))

def leftOrthogonalSum (n m : Nat) : Z :=
  leftOrthogonalPrefix n m n

def stirlingSecondTransformPrefix (a : Nat -> Z) (n : Nat) : Nat -> Z
  | 0 => zMul (stirlingSecondInteger n 0) (a 0)
  | Nat.succ fuel =>
      zAdd (stirlingSecondTransformPrefix a n fuel)
        (zMul (stirlingSecondInteger n (Nat.succ fuel)) (a (Nat.succ fuel)))

def stirlingSecondTransform (a : Nat -> Z) (n : Nat) : Z :=
  stirlingSecondTransformPrefix a n n

def signedStirlingTransformPrefix (a : Nat -> Z) (n : Nat) : Nat -> Z
  | 0 => zMul (signedStirlingFirst n 0) (a 0)
  | Nat.succ fuel =>
      zAdd (signedStirlingTransformPrefix a n fuel)
        (zMul (signedStirlingFirst n (Nat.succ fuel)) (a (Nat.succ fuel)))

def signedStirlingTransform (a : Nat -> Z) (n : Nat) : Z :=
  signedStirlingTransformPrefix a n n

theorem signedStirlingFirst_zero_zero :
    Zeq (signedStirlingFirst 0 0) zOne := by
  exact integerRing.refl zOne

theorem signedStirlingFirst_zero_succ (k : Nat) :
    Zeq (signedStirlingFirst 0 (Nat.succ k)) zZero := by
  exact integerRing.refl zZero

theorem signedStirlingFirst_succ_zero (n : Nat) :
    Zeq (signedStirlingFirst (Nat.succ n) 0) zZero := by
  exact integerRing.refl zZero

theorem signedStirlingFirst_recurrence (n k : Nat) :
    Zeq (signedStirlingFirst (Nat.succ n) (Nat.succ k))
      (zSub (signedStirlingFirst n k)
        (zMul (zOfNat n) (signedStirlingFirst n (Nat.succ k)))) := by
  exact integerRing.refl _

theorem stirlingSecondInteger_zero_zero :
    Zeq (stirlingSecondInteger 0 0) zOne := by
  exact integerRing.refl zOne

theorem stirlingSecondInteger_zero_succ (k : Nat) :
    Zeq (stirlingSecondInteger 0 (Nat.succ k)) zZero := by
  exact integerRing.refl zZero

theorem stirlingSecondInteger_succ_zero (n : Nat) :
    Zeq (stirlingSecondInteger (Nat.succ n) 0) zZero := by
  exact integerRing.refl zZero

theorem stirlingSecondInteger_recurrence (n k : Nat) :
    Zeq (stirlingSecondInteger (Nat.succ n) (Nat.succ k))
      (zAdd
        (zMul (zOfNat (Nat.succ k)) (stirlingSecondInteger n (Nat.succ k)))
        (stirlingSecondInteger n k)) := by
  exact integerRing.refl _

private theorem zSub_congr {a a' b b' : Z}
    (ha : Zeq a a') (hb : Zeq b b') :
    Zeq (zSub a b) (zSub a' b') := by
  exact integerRing.trans (integerRing.sub_eq_add_neg a b)
    (integerRing.trans
      (integerRing.add_congr ha (integerRing.neg_congr hb))
      (integerRing.symm (integerRing.sub_eq_add_neg a' b')))

private theorem zMul_zero_right (x : Z) :
    Zeq (zMul x zZero) zZero :=
  integerRing.mul_zero x

private theorem zMul_zero_left (x : Z) :
    Zeq (zMul zZero x) zZero :=
  integerRing.zero_mul x

private theorem zAdd_zero_zero :
    Zeq (zAdd zZero zZero) zZero :=
  integerRing.zero_add zZero

private theorem add_zero_tail {x y : Z}
    (hx : Zeq x zZero) (hy : Zeq y zZero) :
    Zeq (zAdd x y) zZero := by
  exact integerRing.trans (integerRing.add_congr hx hy) zAdd_zero_zero

private theorem zSub_zero_zero :
    Zeq (zSub zZero zZero) zZero := by
  exact integerRing.trans (integerRing.sub_eq_add_neg zZero zZero)
    (integerRing.trans
      (integerRing.add_congr (integerRing.refl zZero) integerRing.neg_zero)
      (integerRing.zero_add zZero))

private theorem zSub_one_zero :
    Zeq (zSub zOne zZero) zOne := by
  exact integerRing.trans (integerRing.sub_eq_add_neg zOne zZero)
    (integerRing.trans
      (integerRing.add_congr (integerRing.refl zOne) integerRing.neg_zero)
      (integerRing.add_zero zOne))

private theorem zMul_one_one :
    Zeq (zMul zOne zOne) zOne :=
  integerRing.one_mul zOne

theorem signedStirlingFirst_self_and_above :
    ∀ n : Nat, Zeq (signedStirlingFirst n n) zOne ∧
      ∀ extra : Nat, Zeq (signedStirlingFirst n (Nat.succ (n + extra))) zZero := by
  intro n
  induction n with
  | zero =>
      constructor
      · exact integerRing.refl zOne
      · intro extra
        exact signedStirlingFirst_zero_succ extra
  | succ n ih =>
      constructor
      · change Zeq
          (zSub (signedStirlingFirst n n)
            (zMul (zOfNat n) (signedStirlingFirst n (Nat.succ n)))) zOne
        have tailZero :
            Zeq (zMul (zOfNat n) (signedStirlingFirst n (Nat.succ n))) zZero :=
          integerRing.trans
            (integerRing.mul_congr (integerRing.refl (zOfNat n)) (ih.right 0))
            (zMul_zero_right (zOfNat n))
        exact integerRing.trans (zSub_congr ih.left tailZero) zSub_one_zero
      · intro extra
        change Zeq
          (zSub
            (signedStirlingFirst n (Nat.succ n + extra))
            (zMul (zOfNat n)
              (signedStirlingFirst n (Nat.succ (Nat.succ n + extra))))) zZero
        have headZero :
            Zeq (signedStirlingFirst n (Nat.succ n + extra)) zZero := by
          rw [Nat.succ_add]
          exact ih.right extra
        have tailZero :
            Zeq
              (zMul (zOfNat n)
                (signedStirlingFirst n (Nat.succ (Nat.succ n + extra)))) zZero := by
          have termZero :
              Zeq (signedStirlingFirst n (Nat.succ (Nat.succ n + extra))) zZero := by
            rw [Nat.succ_add]
            rw [show Nat.succ (Nat.succ (n + extra)) =
                Nat.succ (n + Nat.succ extra) by
              rw [Nat.add_succ]]
            exact ih.right (Nat.succ extra)
          exact integerRing.trans
            (integerRing.mul_congr (integerRing.refl (zOfNat n)) termZero)
            (zMul_zero_right (zOfNat n))
        exact integerRing.trans (zSub_congr headZero tailZero) zSub_zero_zero

theorem signedStirlingFirst_self (n : Nat) :
    Zeq (signedStirlingFirst n n) zOne :=
  (signedStirlingFirst_self_and_above n).left

theorem signedStirlingFirst_above (n extra : Nat) :
    Zeq (signedStirlingFirst n (Nat.succ (n + extra))) zZero :=
  (signedStirlingFirst_self_and_above n).right extra

theorem stirlingSecondInteger_self_and_above :
    ∀ n : Nat, Zeq (stirlingSecondInteger n n) zOne ∧
      ∀ extra : Nat, Zeq (stirlingSecondInteger n (Nat.succ (n + extra))) zZero := by
  intro n
  induction n with
  | zero =>
      constructor
      · exact integerRing.refl zOne
      · intro extra
        exact stirlingSecondInteger_zero_succ extra
  | succ n ih =>
      constructor
      · change Zeq
          (zAdd
            (zMul (zOfNat (Nat.succ n)) (stirlingSecondInteger n (Nat.succ n)))
            (stirlingSecondInteger n n)) zOne
        have headZero :
            Zeq
              (zMul (zOfNat (Nat.succ n)) (stirlingSecondInteger n (Nat.succ n)))
              zZero :=
          integerRing.trans
            (integerRing.mul_congr (integerRing.refl (zOfNat (Nat.succ n))) (ih.right 0))
            (zMul_zero_right (zOfNat (Nat.succ n)))
        exact integerRing.trans (integerRing.add_congr headZero ih.left)
          (integerRing.zero_add zOne)
      · intro extra
        change Zeq
          (zAdd
            (zMul (zOfNat (Nat.succ (Nat.succ n + extra)))
              (stirlingSecondInteger n (Nat.succ (Nat.succ n + extra))))
            (stirlingSecondInteger n (Nat.succ n + extra))) zZero
        have headZero :
            Zeq
              (zMul (zOfNat (Nat.succ (Nat.succ n + extra)))
                (stirlingSecondInteger n (Nat.succ (Nat.succ n + extra)))) zZero := by
          have termZero :
              Zeq (stirlingSecondInteger n (Nat.succ (Nat.succ n + extra))) zZero := by
            rw [Nat.succ_add]
            rw [show Nat.succ (Nat.succ (n + extra)) =
                Nat.succ (n + Nat.succ extra) by
              rw [Nat.add_succ]]
            exact ih.right (Nat.succ extra)
          exact integerRing.trans
            (integerRing.mul_congr
              (integerRing.refl (zOfNat (Nat.succ (Nat.succ n + extra)))) termZero)
            (zMul_zero_right (zOfNat (Nat.succ (Nat.succ n + extra))))
        have tailZero :
            Zeq (stirlingSecondInteger n (Nat.succ n + extra)) zZero := by
          rw [Nat.succ_add]
          exact ih.right extra
        exact add_zero_tail headZero tailZero

theorem stirlingSecondInteger_self (n : Nat) :
    Zeq (stirlingSecondInteger n n) zOne :=
  (stirlingSecondInteger_self_and_above n).left

theorem stirlingSecondInteger_above (n extra : Nat) :
    Zeq (stirlingSecondInteger n (Nat.succ (n + extra))) zZero :=
  (stirlingSecondInteger_self_and_above n).right extra

theorem rightOrthogonalPrefix_zero_column_strong (n fuel : Nat) :
    Zeq (rightOrthogonalPrefix (Nat.succ n) 0 fuel) zZero :=
  Nat.strongRecOn
    (motive := fun fuel => Zeq (rightOrthogonalPrefix (Nat.succ n) 0 fuel) zZero)
    fuel
    (fun fuel ih =>
      match fuel with
      | 0 =>
          zMul_zero_left zOne
      | Nat.succ tail =>
          add_zero_tail
            (ih tail (Nat.lt_succ_self tail))
            (zMul_zero_right (stirlingSecondInteger (Nat.succ n) (Nat.succ tail))))

theorem right_stirling_orthogonality_zero_column (n : Nat) :
    Zeq (rightOrthogonalSum (Nat.succ n) 0)
      (kroneckerInteger (Nat.succ n) 0) := by
  change Zeq (rightOrthogonalPrefix (Nat.succ n) 0 (Nat.succ n)) zZero
  exact rightOrthogonalPrefix_zero_column_strong n (Nat.succ n)

theorem leftOrthogonalPrefix_zero_column_strong (n fuel : Nat) :
    Zeq (leftOrthogonalPrefix (Nat.succ n) 0 fuel) zZero :=
  Nat.strongRecOn
    (motive := fun fuel => Zeq (leftOrthogonalPrefix (Nat.succ n) 0 fuel) zZero)
    fuel
    (fun fuel ih =>
      match fuel with
      | 0 =>
          zMul_zero_left zOne
      | Nat.succ tail =>
          add_zero_tail
            (ih tail (Nat.lt_succ_self tail))
            (zMul_zero_right (signedStirlingFirst (Nat.succ n) (Nat.succ tail))))

theorem left_stirling_orthogonality_zero_column (n : Nat) :
    Zeq (leftOrthogonalSum (Nat.succ n) 0)
      (kroneckerInteger (Nat.succ n) 0) := by
  change Zeq (leftOrthogonalPrefix (Nat.succ n) 0 (Nat.succ n)) zZero
  exact leftOrthogonalPrefix_zero_column_strong n (Nat.succ n)

theorem rightOrthogonalPrefix_above_signed (row fuel extra : Nat) :
    Zeq (rightOrthogonalPrefix row (Nat.succ (fuel + extra)) fuel) zZero := by
  induction fuel generalizing extra with
  | zero =>
      rw [Nat.zero_add]
      change Zeq
        (zMul (stirlingSecondInteger row 0) (signedStirlingFirst 0 (Nat.succ extra)))
        zZero
      exact integerRing.trans
        (integerRing.mul_congr (integerRing.refl (stirlingSecondInteger row 0))
          (signedStirlingFirst_zero_succ extra))
        (zMul_zero_right (stirlingSecondInteger row 0))
  | succ fuel ih =>
      have prefixZero :
          Zeq
            (rightOrthogonalPrefix row (Nat.succ (Nat.succ fuel + extra)) fuel)
            zZero := by
        rw [show Nat.succ (Nat.succ fuel + extra) =
            Nat.succ (fuel + Nat.succ extra) by
          rw [Nat.succ_add, Nat.add_succ]]
        exact ih (Nat.succ extra)
      have termZero :
          Zeq
            (zMul (stirlingSecondInteger row (Nat.succ fuel))
              (signedStirlingFirst (Nat.succ fuel)
                (Nat.succ (Nat.succ fuel + extra)))) zZero :=
        integerRing.trans
          (integerRing.mul_congr
            (integerRing.refl (stirlingSecondInteger row (Nat.succ fuel)))
            (signedStirlingFirst_above (Nat.succ fuel) extra))
          (zMul_zero_right (stirlingSecondInteger row (Nat.succ fuel)))
      change Zeq
        (zAdd (rightOrthogonalPrefix row (Nat.succ (Nat.succ fuel + extra)) fuel)
          (zMul (stirlingSecondInteger row (Nat.succ fuel))
            (signedStirlingFirst (Nat.succ fuel)
              (Nat.succ (Nat.succ fuel + extra))))) zZero
      exact add_zero_tail prefixZero termZero

theorem leftOrthogonalPrefix_above_second (row fuel extra : Nat) :
    Zeq (leftOrthogonalPrefix row (Nat.succ (fuel + extra)) fuel) zZero := by
  induction fuel generalizing extra with
  | zero =>
      rw [Nat.zero_add]
      change Zeq
        (zMul (signedStirlingFirst row 0) (stirlingSecondInteger 0 (Nat.succ extra)))
        zZero
      exact integerRing.trans
        (integerRing.mul_congr (integerRing.refl (signedStirlingFirst row 0))
          (stirlingSecondInteger_zero_succ extra))
        (zMul_zero_right (signedStirlingFirst row 0))
  | succ fuel ih =>
      have prefixZero :
          Zeq
            (leftOrthogonalPrefix row (Nat.succ (Nat.succ fuel + extra)) fuel)
            zZero := by
        rw [show Nat.succ (Nat.succ fuel + extra) =
            Nat.succ (fuel + Nat.succ extra) by
          rw [Nat.succ_add, Nat.add_succ]]
        exact ih (Nat.succ extra)
      have termZero :
          Zeq
            (zMul (signedStirlingFirst row (Nat.succ fuel))
              (stirlingSecondInteger (Nat.succ fuel)
                (Nat.succ (Nat.succ fuel + extra)))) zZero :=
        integerRing.trans
          (integerRing.mul_congr
            (integerRing.refl (signedStirlingFirst row (Nat.succ fuel)))
            (stirlingSecondInteger_above (Nat.succ fuel) extra))
          (zMul_zero_right (signedStirlingFirst row (Nat.succ fuel)))
      change Zeq
        (zAdd (leftOrthogonalPrefix row (Nat.succ (Nat.succ fuel + extra)) fuel)
          (zMul (signedStirlingFirst row (Nat.succ fuel))
            (stirlingSecondInteger (Nat.succ fuel)
              (Nat.succ (Nat.succ fuel + extra))))) zZero
      exact add_zero_tail prefixZero termZero

theorem right_stirling_orthogonality_origin :
    Zeq (rightOrthogonalSum 0 0) (kroneckerInteger 0 0) := by
  change Zeq (zMul zOne zOne) zOne
  exact integerRing.one_mul zOne

theorem left_stirling_orthogonality_origin :
    Zeq (leftOrthogonalSum 0 0) (kroneckerInteger 0 0) := by
  change Zeq (zMul zOne zOne) zOne
  exact integerRing.one_mul zOne

theorem right_stirling_orthogonality_zero_row (m : Nat) :
    Zeq (rightOrthogonalSum 0 (Nat.succ m))
      (kroneckerInteger 0 (Nat.succ m)) := by
  change Zeq (zMul zOne zZero) zZero
  exact zMul_zero_right zOne

theorem left_stirling_orthogonality_zero_row (m : Nat) :
    Zeq (leftOrthogonalSum 0 (Nat.succ m))
      (kroneckerInteger 0 (Nat.succ m)) := by
  change Zeq (zMul zZero zZero) zZero
  exact zMul_zero_left zZero

theorem kroneckerInteger_self (n : Nat) :
    Zeq (kroneckerInteger n n) zOne := by
  induction n with
  | zero =>
      exact integerRing.refl zOne
  | succ _ ih =>
      exact ih

theorem right_stirling_orthogonality_diagonal (n : Nat) :
    Zeq (rightOrthogonalSum n n) (kroneckerInteger n n) := by
  cases n with
  | zero =>
      exact right_stirling_orthogonality_origin
  | succ n =>
      unfold rightOrthogonalSum
      rw [Nat.add_one]
      change Zeq
        (zAdd (rightOrthogonalPrefix (Nat.succ n) (Nat.succ n) n)
          (zMul (stirlingSecondInteger (Nat.succ n) (Nat.succ n))
            (signedStirlingFirst (Nat.succ n) (Nat.succ n))))
        (kroneckerInteger (Nat.succ n) (Nat.succ n))
      have prefixZero :
          Zeq (rightOrthogonalPrefix (Nat.succ n) (Nat.succ n) n) zZero := by
        change Zeq (rightOrthogonalPrefix (Nat.succ n) (Nat.succ (n + 0)) n) zZero
        exact rightOrthogonalPrefix_above_signed (Nat.succ n) n 0
      have productOne :
          Zeq
            (zMul (stirlingSecondInteger (Nat.succ n) (Nat.succ n))
              (signedStirlingFirst (Nat.succ n) (Nat.succ n))) zOne :=
        integerRing.trans
          (integerRing.mul_congr
            (stirlingSecondInteger_self (Nat.succ n))
            (signedStirlingFirst_self (Nat.succ n)))
          zMul_one_one
      exact integerRing.trans
        (integerRing.trans (integerRing.add_congr prefixZero productOne)
          (integerRing.zero_add zOne))
        (integerRing.symm (kroneckerInteger_self (Nat.succ n)))

theorem left_stirling_orthogonality_diagonal (n : Nat) :
    Zeq (leftOrthogonalSum n n) (kroneckerInteger n n) := by
  cases n with
  | zero =>
      exact left_stirling_orthogonality_origin
  | succ n =>
      unfold leftOrthogonalSum
      rw [Nat.add_one]
      change Zeq
        (zAdd (leftOrthogonalPrefix (Nat.succ n) (Nat.succ n) n)
          (zMul (signedStirlingFirst (Nat.succ n) (Nat.succ n))
            (stirlingSecondInteger (Nat.succ n) (Nat.succ n))))
        (kroneckerInteger (Nat.succ n) (Nat.succ n))
      have prefixZero :
          Zeq (leftOrthogonalPrefix (Nat.succ n) (Nat.succ n) n) zZero := by
        change Zeq (leftOrthogonalPrefix (Nat.succ n) (Nat.succ (n + 0)) n) zZero
        exact leftOrthogonalPrefix_above_second (Nat.succ n) n 0
      have productOne :
          Zeq
            (zMul (signedStirlingFirst (Nat.succ n) (Nat.succ n))
              (stirlingSecondInteger (Nat.succ n) (Nat.succ n))) zOne :=
        integerRing.trans
          (integerRing.mul_congr
            (signedStirlingFirst_self (Nat.succ n))
            (stirlingSecondInteger_self (Nat.succ n)))
          zMul_one_one
      exact integerRing.trans
        (integerRing.trans (integerRing.add_congr prefixZero productOne)
          (integerRing.zero_add zOne))
        (integerRing.symm (kroneckerInteger_self (Nat.succ n)))

theorem stirling_second_transform_zero (a : Nat -> Z) :
    Zeq (stirlingSecondTransform a 0) (a 0) := by
  change Zeq (zMul zOne (a 0)) (a 0)
  exact integerRing.one_mul (a 0)

theorem signed_stirling_transform_zero (a : Nat -> Z) :
    Zeq (signedStirlingTransform a 0) (a 0) := by
  change Zeq (zMul zOne (a 0)) (a 0)
  exact integerRing.one_mul (a 0)

theorem stirling_inversion_zero (a : Nat -> Z) :
    Zeq
      (signedStirlingTransform (fun k => stirlingSecondTransform a k) 0)
      (a 0) := by
  exact integerRing.trans
    (signed_stirling_transform_zero (fun k => stirlingSecondTransform a k))
    (stirling_second_transform_zero a)

theorem StirlingInversionUp_constructive_export (a : Nat -> Z) :
    Zeq (rightOrthogonalSum 0 0) (kroneckerInteger 0 0) ∧
      (∀ n : Nat,
        Zeq (rightOrthogonalSum (Nat.succ n) 0)
          (kroneckerInteger (Nat.succ n) 0)) ∧
      Zeq (leftOrthogonalSum 0 0) (kroneckerInteger 0 0) ∧
      (∀ n : Nat,
        Zeq (leftOrthogonalSum (Nat.succ n) 0)
          (kroneckerInteger (Nat.succ n) 0)) ∧
      (∀ n : Nat,
        Zeq (rightOrthogonalSum n n) (kroneckerInteger n n)) ∧
      (∀ n : Nat,
        Zeq (leftOrthogonalSum n n) (kroneckerInteger n n)) ∧
      Zeq
        (signedStirlingTransform (fun k => stirlingSecondTransform a k) 0)
        (a 0) := by
  constructor
  · exact right_stirling_orthogonality_origin
  · constructor
    · intro n
      exact right_stirling_orthogonality_zero_column n
    · constructor
      · exact left_stirling_orthogonality_origin
      · constructor
        · intro n
          exact left_stirling_orthogonality_zero_column n
        · constructor
          · intro n
            exact right_stirling_orthogonality_diagonal n
          · constructor
            · intro n
              exact left_stirling_orthogonality_diagonal n
            · exact stirling_inversion_zero a

end BEDC.Derived.StirlingInversionUp
