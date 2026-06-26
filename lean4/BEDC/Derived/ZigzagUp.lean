import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.ZigzagUp

abbrev binomial (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

def valueAt : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, Nat.succ n => valueAt xs n

def zigzagTerm (values : List Nat) (n k : Nat) : Nat :=
  binomial n k * valueAt values k * valueAt values (n - k)

def zigzagConvolution (values : List Nat) (n : Nat) : Nat :=
  finiteNatSum (zigzagTerm values n) n

-- `ZigzagPrefix values` 表示 `values = [A_0, ..., A_m]`
-- 由欧拉之字数递归生成, 且 `A_0 = A_1 = 1`.
inductive ZigzagPrefix : List Nat -> Prop where
  | zero : ZigzagPrefix [1]
  | one : ZigzagPrefix [1, 1]
  | step {values : List Nat} {aNext m : Nat} :
      ZigzagPrefix values ->
        values.length = Nat.succ (Nat.succ m) ->
          2 * aNext = zigzagConvolution values (Nat.succ m) ->
            ZigzagPrefix (values ++ [aNext])

def ZigzagNumber (n a : Nat) : Prop :=
  exists values : List Nat,
    ZigzagPrefix values /\ values.length = Nat.succ n /\ valueAt values n = a

def tangentNumber (n a : Nat) : Prop :=
  ZigzagNumber (2 * n + 1) a

def secantNumber (n a : Nat) : Prop :=
  ZigzagNumber (2 * n) a

abbrev EulerZigzagNumber := ZigzagNumber

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp
abbrev IntEq := BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def integerLawSurface : BEDC.Derived.IntUp.IntegerUpCommRingLaws :=
  BEDC.Derived.IntUp.IntegerUp_comm_ring_laws

theorem integer_ring_reuses_rel_comm_ring :
    integerRing.zero = BEDC.Algebra.Rel.intZero := by
  rfl

theorem finiteNatSum_zero (f : Nat -> Nat) :
    finiteNatSum f 0 = f 0 := by
  rfl

theorem finiteNatSum_succ (f : Nat -> Nat) (n : Nat) :
    finiteNatSum f (Nat.succ n) = finiteNatSum f n + f (Nat.succ n) := by
  rfl

theorem valueAt_zero_cons (x : Nat) (xs : List Nat) :
    valueAt (x :: xs) 0 = x := by
  rfl

theorem valueAt_succ_cons (x : Nat) (xs : List Nat) (n : Nat) :
    valueAt (x :: xs) (Nat.succ n) = valueAt xs n := by
  rfl

theorem zigzag_convolution_zero (values : List Nat) :
    zigzagConvolution values 0 =
      binomial 0 0 * valueAt values 0 * valueAt values 0 := by
  rfl

theorem zigzag_convolution_succ (values : List Nat) (n : Nat) :
    zigzagConvolution values (Nat.succ n) =
      finiteNatSum (zigzagTerm values (Nat.succ n)) n +
        binomial (Nat.succ n) (Nat.succ n) *
          valueAt values (Nat.succ n) * valueAt values 0 := by
  unfold zigzagConvolution
  change finiteNatSum (zigzagTerm values (Nat.succ n)) n +
      zigzagTerm values (Nat.succ n) (Nat.succ n) =
    finiteNatSum (zigzagTerm values (Nat.succ n)) n +
      binomial (Nat.succ n) (Nat.succ n) *
        valueAt values (Nat.succ n) * valueAt values 0
  unfold zigzagTerm
  rw [Nat.sub_self]

theorem zigzag_recurrence {values : List Nat} {aNext m : Nat} :
    ZigzagPrefix values ->
      values.length = Nat.succ (Nat.succ m) ->
        2 * aNext = zigzagConvolution values (Nat.succ m) ->
          ZigzagPrefix (values ++ [aNext]) := by
  intro hPrefix hLength hRecurrence
  exact ZigzagPrefix.step hPrefix hLength hRecurrence

theorem zigzag_prefix_zero : ZigzagPrefix [1] := by
  exact ZigzagPrefix.zero

theorem zigzag_prefix_one : ZigzagPrefix [1, 1] := by
  exact ZigzagPrefix.one

theorem zigzag_prefix_two : ZigzagPrefix [1, 1, 1] := by
  exact ZigzagPrefix.step (m := 0) ZigzagPrefix.one rfl rfl

theorem zigzag_prefix_three : ZigzagPrefix [1, 1, 1, 2] := by
  exact ZigzagPrefix.step (m := 1) zigzag_prefix_two rfl rfl

theorem zigzag_prefix_four : ZigzagPrefix [1, 1, 1, 2, 5] := by
  exact ZigzagPrefix.step (m := 2) zigzag_prefix_three rfl rfl

theorem zigzag_prefix_five : ZigzagPrefix [1, 1, 1, 2, 5, 16] := by
  exact ZigzagPrefix.step (m := 3) zigzag_prefix_four rfl rfl

theorem zigzag_A0 : ZigzagNumber 0 1 := by
  exact Exists.intro [1] (And.intro zigzag_prefix_zero (And.intro rfl rfl))

theorem zigzag_A1 : ZigzagNumber 1 1 := by
  exact Exists.intro [1, 1] (And.intro zigzag_prefix_one (And.intro rfl rfl))

theorem zigzag_A2 : ZigzagNumber 2 1 := by
  exact Exists.intro [1, 1, 1] (And.intro zigzag_prefix_two (And.intro rfl rfl))

theorem zigzag_A3 : ZigzagNumber 3 2 := by
  exact Exists.intro [1, 1, 1, 2] (And.intro zigzag_prefix_three (And.intro rfl rfl))

theorem zigzag_A4 : ZigzagNumber 4 5 := by
  exact Exists.intro [1, 1, 1, 2, 5] (And.intro zigzag_prefix_four (And.intro rfl rfl))

theorem zigzag_A5 : ZigzagNumber 5 16 := by
  exact Exists.intro [1, 1, 1, 2, 5, 16]
    (And.intro zigzag_prefix_five (And.intro rfl rfl))

theorem zigzag_small_values :
    ZigzagNumber 0 1 /\ ZigzagNumber 1 1 /\ ZigzagNumber 2 1 /\
      ZigzagNumber 3 2 /\ ZigzagNumber 4 5 /\ ZigzagNumber 5 16 := by
  exact And.intro zigzag_A0
    (And.intro zigzag_A1
      (And.intro zigzag_A2
        (And.intro zigzag_A3
          (And.intro zigzag_A4 zigzag_A5))))

theorem tangentNumber_odd_zigzag (n a : Nat) :
    tangentNumber n a = ZigzagNumber (2 * n + 1) a := by
  rfl

theorem secantNumber_even_zigzag (n a : Nat) :
    secantNumber n a = ZigzagNumber (2 * n) a := by
  rfl

theorem tangent_T0 : tangentNumber 0 1 := by
  exact zigzag_A1

theorem tangent_T1 : tangentNumber 1 2 := by
  exact zigzag_A3

theorem tangent_T2 : tangentNumber 2 16 := by
  exact zigzag_A5

theorem secant_S0 : secantNumber 0 1 := by
  exact zigzag_A0

theorem secant_S1 : secantNumber 1 1 := by
  exact zigzag_A2

theorem secant_S2 : secantNumber 2 5 := by
  exact zigzag_A4

theorem zigzag_odd_even_split :
    tangentNumber 0 1 /\ tangentNumber 1 2 /\ tangentNumber 2 16 /\
      secantNumber 0 1 /\ secantNumber 1 1 /\ secantNumber 2 5 := by
  exact And.intro tangent_T0
    (And.intro tangent_T1
      (And.intro tangent_T2
        (And.intro secant_S0
          (And.intro secant_S1 secant_S2))))

theorem euler_zigzag_mathlib_indexing (n a : Nat) :
    EulerZigzagNumber n a = ZigzagNumber n a := by
  rfl

theorem ZigzagUp_constructive_export :
    ZigzagPrefix [1, 1, 1, 2, 5, 16] /\
      ZigzagNumber 0 1 /\ ZigzagNumber 1 1 /\ ZigzagNumber 2 1 /\
        ZigzagNumber 3 2 /\ ZigzagNumber 4 5 /\ ZigzagNumber 5 16 /\
          tangentNumber 0 1 /\ tangentNumber 1 2 /\ tangentNumber 2 16 /\
            secantNumber 0 1 /\ secantNumber 1 1 /\ secantNumber 2 5 := by
  exact And.intro zigzag_prefix_five
    (And.intro zigzag_A0
      (And.intro zigzag_A1
        (And.intro zigzag_A2
          (And.intro zigzag_A3
            (And.intro zigzag_A4
              (And.intro zigzag_A5
                (And.intro tangent_T0
                  (And.intro tangent_T1
                    (And.intro tangent_T2
                      (And.intro secant_S0
                        (And.intro secant_S1 secant_S2)))))))))))

end BEDC.Derived.ZigzagUp
