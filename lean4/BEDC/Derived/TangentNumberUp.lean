import BEDC.Derived.BernoulliUp
import BEDC.Derived.ZigzagUp

namespace BEDC.Derived.TangentNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev binomial : Nat -> Nat -> Nat :=
  BEDC.Derived.ZigzagUp.binomial

abbrev finiteNatSum : (Nat -> Nat) -> Nat -> Nat :=
  BEDC.Derived.ZigzagUp.finiteNatSum

abbrev valueAt : List Nat -> Nat -> Nat :=
  BEDC.Derived.ZigzagUp.valueAt

abbrev zigzagTerm : List Nat -> Nat -> Nat -> Nat :=
  BEDC.Derived.ZigzagUp.zigzagTerm

abbrev zigzagConvolution : List Nat -> Nat -> Nat :=
  BEDC.Derived.ZigzagUp.zigzagConvolution

abbrev ZigzagPrefix : List Nat -> Prop :=
  BEDC.Derived.ZigzagUp.ZigzagPrefix

abbrev ZigzagNumber : Nat -> Nat -> Prop :=
  BEDC.Derived.ZigzagUp.ZigzagNumber

abbrev EulerZigzagNumber : Nat -> Nat -> Prop :=
  BEDC.Derived.ZigzagUp.EulerZigzagNumber

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

def natAsInteger (n : Nat) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat (natToUnary n) (natToUnary_unary n)

-- BernoulliUp 提供有理数小值层；这里保留闭式候选的数据面,
-- 不把尚未形式化的全局 Bernoulli 恒等式伪装成定理.
structure BernoulliTangentClosedFormInput where
  index : Nat
  powerOfTwo : Nat
  bernoulliIndex : Nat
  bernoulliNumeratorAbs : Nat
  bernoulliDenominator : Nat
  divisor : Nat

def bernoulliTangentClosedFormInput (n : Nat) :
    BernoulliTangentClosedFormInput :=
  let b := BEDC.Derived.BernoulliUp.rawBernoulli (2 * n)
  { index := n
    powerOfTwo := Nat.pow 2 (2 * n)
    bernoulliIndex := 2 * n
    bernoulliNumeratorAbs := BEDC.Derived.BernoulliUp.intAbsNat b.num
    bernoulliDenominator := b.den
    divisor := b.den * (2 * n) }

def bernoulliTangentCoefficientFn (n : Nat) : Nat :=
  let b := BEDC.Derived.BernoulliUp.rawBernoulli (2 * n)
  let p := Nat.pow 2 (2 * n)
  (p * (p - 1) * BEDC.Derived.BernoulliUp.intAbsNat b.num) /
    (b.den * (2 * n))

def zigzagPrefixFn : Nat -> List Nat
  | 0 => [1]
  | 1 => [1, 1]
  | Nat.succ (Nat.succ n) =>
      let previous := zigzagPrefixFn (Nat.succ n)
      previous ++ [zigzagConvolution previous (Nat.succ n) / 2]

def zigzagNumberFn (n : Nat) : Nat :=
  valueAt (zigzagPrefixFn n) n

def tangentZigzagIndex (n : Nat) : Nat :=
  2 * n - 1

def tangentNumberFn (n : Nat) : Nat :=
  zigzagNumberFn (tangentZigzagIndex n)

def tangentNumber (n a : Nat) : Prop :=
  a = tangentNumberFn n

def tangentTaylorCoefficientNumerator (n : Nat) : Nat :=
  tangentNumberFn n

def tangentTaylorCoefficientFactorialIndex (n : Nat) : Nat :=
  2 * n - 1

def tangentInteger (n : Nat) : IntegerUp :=
  natAsInteger (tangentNumberFn n)

def TangentInteger (n : Nat) (z : IntegerUp) : Prop :=
  IntEq z (tangentInteger n)

theorem tangent_zigzag_index_zero :
    tangentZigzagIndex 0 = 0 := by
  rfl

theorem tangent_zigzag_index_one :
    tangentZigzagIndex 1 = 1 := by
  rfl

theorem tangent_zigzag_index_two :
    tangentZigzagIndex 2 = 3 := by
  rfl

theorem tangent_zigzag_index_three :
    tangentZigzagIndex 3 = 5 := by
  rfl

theorem tangent_zigzag_index_four :
    tangentZigzagIndex 4 = 7 := by
  rfl

theorem tangentNumberFn_zero :
    tangentNumberFn 0 = 1 := by
  rfl

theorem tangentNumberFn_one :
    tangentNumberFn 1 = 1 := by
  rfl

theorem tangentNumberFn_two :
    tangentNumberFn 2 = 2 := by
  rfl

theorem tangentNumberFn_three :
    tangentNumberFn 3 = 16 := by
  rfl

theorem tangentNumberFn_four :
    tangentNumberFn 4 = 272 := by
  rfl

theorem bernoulliTangentCoefficientFn_one :
    bernoulliTangentCoefficientFn 1 = 1 := by
  rfl

theorem bernoulliTangentCoefficientFn_two :
    bernoulliTangentCoefficientFn 2 = 2 := by
  rfl

theorem bernoulliTangentCoefficientFn_three :
    bernoulliTangentCoefficientFn 3 = 16 := by
  rfl

theorem bernoulliTangentCoefficientFn_four :
    bernoulliTangentCoefficientFn 4 = 272 := by
  rfl

theorem bernoulli_tangent_small_values_match :
    bernoulliTangentCoefficientFn 1 = tangentNumberFn 1 ∧
      bernoulliTangentCoefficientFn 2 = tangentNumberFn 2 ∧
        bernoulliTangentCoefficientFn 3 = tangentNumberFn 3 ∧
          bernoulliTangentCoefficientFn 4 = tangentNumberFn 4 := by
  exact And.intro bernoulliTangentCoefficientFn_one
    (And.intro bernoulliTangentCoefficientFn_two
      (And.intro bernoulliTangentCoefficientFn_three
        bernoulliTangentCoefficientFn_four))

theorem tangentTaylorCoefficientFactorialIndex_one :
    tangentTaylorCoefficientFactorialIndex 1 = 1 := by
  rfl

theorem tangentTaylorCoefficientFactorialIndex_two :
    tangentTaylorCoefficientFactorialIndex 2 = 3 := by
  rfl

theorem tangentTaylorCoefficientFactorialIndex_three :
    tangentTaylorCoefficientFactorialIndex 3 = 5 := by
  rfl

theorem tangentTaylorCoefficientFactorialIndex_four :
    tangentTaylorCoefficientFactorialIndex 4 = 7 := by
  rfl

theorem tangentNumber_one :
    tangentNumber 1 1 := by
  rfl

theorem tangentNumber_two :
    tangentNumber 2 2 := by
  rfl

theorem tangentNumber_three :
    tangentNumber 3 16 := by
  rfl

theorem tangentNumber_four :
    tangentNumber 4 272 := by
  rfl

theorem zigzag_prefix_six :
    ZigzagPrefix [1, 1, 1, 2, 5, 16, 61] := by
  exact BEDC.Derived.ZigzagUp.ZigzagPrefix.step
    (m := 4) BEDC.Derived.ZigzagUp.zigzag_prefix_five rfl rfl

theorem zigzag_prefix_seven :
    ZigzagPrefix [1, 1, 1, 2, 5, 16, 61, 272] := by
  exact BEDC.Derived.ZigzagUp.ZigzagPrefix.step
    (m := 5) zigzag_prefix_six rfl rfl

theorem zigzag_A6 :
    ZigzagNumber 6 61 := by
  exact Exists.intro [1, 1, 1, 2, 5, 16, 61]
    (And.intro zigzag_prefix_six (And.intro rfl rfl))

theorem zigzag_A7 :
    ZigzagNumber 7 272 := by
  exact Exists.intro [1, 1, 1, 2, 5, 16, 61, 272]
    (And.intro zigzag_prefix_seven (And.intro rfl rfl))

theorem tangentNumber_one_odd_zigzag :
    tangentNumber 1 1 ∧ ZigzagNumber 1 1 := by
  exact And.intro tangentNumber_one BEDC.Derived.ZigzagUp.zigzag_A1

theorem tangentNumber_two_odd_zigzag :
    tangentNumber 2 2 ∧ ZigzagNumber 3 2 := by
  exact And.intro tangentNumber_two BEDC.Derived.ZigzagUp.zigzag_A3

theorem tangentNumber_three_odd_zigzag :
    tangentNumber 3 16 ∧ ZigzagNumber 5 16 := by
  exact And.intro tangentNumber_three BEDC.Derived.ZigzagUp.zigzag_A5

theorem tangentNumber_four_odd_zigzag :
    tangentNumber 4 272 ∧ ZigzagNumber 7 272 := by
  exact And.intro tangentNumber_four zigzag_A7

theorem tangentNumber_odd_zigzag_small_values :
    (tangentNumber 1 1 ∧ ZigzagNumber 1 1) ∧
      (tangentNumber 2 2 ∧ ZigzagNumber 3 2) ∧
        (tangentNumber 3 16 ∧ ZigzagNumber 5 16) ∧
          (tangentNumber 4 272 ∧ ZigzagNumber 7 272) := by
  exact And.intro tangentNumber_one_odd_zigzag
    (And.intro tangentNumber_two_odd_zigzag
      (And.intro tangentNumber_three_odd_zigzag tangentNumber_four_odd_zigzag))

theorem tangentInteger_refl (n : Nat) :
    TangentInteger n (tangentInteger n) := by
  exact BEDC.Derived.RationalUp.IntEq_refl (tangentInteger n)

theorem tangentInteger_one :
    TangentInteger 1 (natAsInteger 1) := by
  exact BEDC.Derived.RationalUp.IntEq_refl (natAsInteger 1)

theorem tangentInteger_two :
    TangentInteger 2 (natAsInteger 2) := by
  exact BEDC.Derived.RationalUp.IntEq_refl (natAsInteger 2)

theorem tangentInteger_three :
    TangentInteger 3 (natAsInteger 16) := by
  exact BEDC.Derived.RationalUp.IntEq_refl (natAsInteger 16)

theorem tangentInteger_four :
    TangentInteger 4 (natAsInteger 272) := by
  exact BEDC.Derived.RationalUp.IntEq_refl (natAsInteger 272)

theorem tangentInteger_integrality (n : Nat) :
    ∃ z : IntegerUp, TangentInteger n z := by
  exact Exists.intro (tangentInteger n) (tangentInteger_refl n)

theorem tangentNumber_integer_carrier {n a : Nat} :
    tangentNumber n a -> TangentInteger n (natAsInteger a) := by
  intro h
  rw [h]
  exact tangentInteger_refl n

theorem tangent_small_values :
    tangentNumber 1 1 ∧ tangentNumber 2 2 ∧
      tangentNumber 3 16 ∧ tangentNumber 4 272 := by
  exact And.intro tangentNumber_one
    (And.intro tangentNumber_two
      (And.intro tangentNumber_three tangentNumber_four))

theorem tangent_integer_small_values :
    TangentInteger 1 (natAsInteger 1) ∧ TangentInteger 2 (natAsInteger 2) ∧
      TangentInteger 3 (natAsInteger 16) ∧ TangentInteger 4 (natAsInteger 272) := by
  exact And.intro tangentInteger_one
    (And.intro tangentInteger_two
      (And.intro tangentInteger_three tangentInteger_four))

theorem tangentNumberUp_constructive_export :
    ZigzagPrefix [1, 1, 1, 2, 5, 16, 61, 272] ∧
      tangentNumber 1 1 ∧ tangentNumber 2 2 ∧ tangentNumber 3 16 ∧
        tangentNumber 4 272 ∧ ZigzagNumber 7 272 ∧
          (∀ n : Nat, ∃ z : IntegerUp, TangentInteger n z) := by
  exact And.intro zigzag_prefix_seven
    (And.intro tangentNumber_one
      (And.intro tangentNumber_two
        (And.intro tangentNumber_three
          (And.intro tangentNumber_four
            (And.intro zigzag_A7 tangentInteger_integrality)))))

end BEDC.Derived.TangentNumberUp
