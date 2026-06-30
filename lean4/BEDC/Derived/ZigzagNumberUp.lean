import BEDC.Derived.ZigzagUp

namespace BEDC.Derived.ZigzagNumberUp

abbrev binomial (n k : Nat) : Nat :=
  BEDC.Derived.ZigzagUp.binomial n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.ZigzagUp.finiteNatSum f

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

def tangentNumber (n a : Nat) : Prop :=
  ZigzagNumber (2 * n + 1) a

def secantNumber (n a : Nat) : Prop :=
  ZigzagNumber (2 * n) a

theorem finiteNatSum_zero (f : Nat -> Nat) :
    finiteNatSum f 0 = f 0 := by
  rfl

theorem finiteNatSum_succ (f : Nat -> Nat) (n : Nat) :
    finiteNatSum f (Nat.succ n) = finiteNatSum f n + f (Nat.succ n) := by
  rfl

theorem zigzagConvolution_positive_succ (values : List Nat) (n : Nat) :
    zigzagConvolution values (Nat.succ n) =
      finiteNatSum
        (fun k => binomial (Nat.succ n) k *
          valueAt values k * valueAt values (Nat.succ n - k))
        (Nat.succ n) := by
  rfl

theorem zigzagPrefix_step_from_positive_recurrence
    {values : List Nat} {aNext n : Nat}
    (hPrefix : ZigzagPrefix values)
    (hlen : values.length = Nat.succ (Nat.succ n))
    (hrec : 2 * aNext = zigzagConvolution values (Nat.succ n)) :
    ZigzagPrefix (values ++ [aNext]) := by
  exact BEDC.Derived.ZigzagUp.ZigzagPrefix.step hPrefix hlen hrec

theorem euler_zigzag_number_same_as_zigzag (n a : Nat) :
    EulerZigzagNumber n a = ZigzagNumber n a := by
  rfl

theorem tangentNumber_odd_classification (n a : Nat) :
    tangentNumber n a = ZigzagNumber (2 * n + 1) a := by
  rfl

theorem secantNumber_even_classification (n a : Nat) :
    secantNumber n a = ZigzagNumber (2 * n) a := by
  rfl

theorem zigzag_A0 : ZigzagNumber 0 1 := by
  exact BEDC.Derived.ZigzagUp.zigzag_A0

theorem zigzag_A1 : ZigzagNumber 1 1 := by
  exact BEDC.Derived.ZigzagUp.zigzag_A1

theorem zigzag_A2 : ZigzagNumber 2 1 := by
  exact BEDC.Derived.ZigzagUp.zigzag_A2

theorem zigzag_A3 : ZigzagNumber 3 2 := by
  exact BEDC.Derived.ZigzagUp.zigzag_A3

theorem zigzag_A4 : ZigzagNumber 4 5 := by
  exact BEDC.Derived.ZigzagUp.zigzag_A4

theorem zigzag_A5 : ZigzagNumber 5 16 := by
  exact BEDC.Derived.ZigzagUp.zigzag_A5

theorem zigzag_small_values :
    ZigzagNumber 0 1 /\ ZigzagNumber 1 1 /\ ZigzagNumber 2 1 /\
      ZigzagNumber 3 2 /\ ZigzagNumber 4 5 /\ ZigzagNumber 5 16 := by
  exact And.intro zigzag_A0
    (And.intro zigzag_A1
      (And.intro zigzag_A2
        (And.intro zigzag_A3
          (And.intro zigzag_A4 zigzag_A5))))

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

theorem tangent_secant_small_values :
    tangentNumber 0 1 /\ tangentNumber 1 2 /\ tangentNumber 2 16 /\
      secantNumber 0 1 /\ secantNumber 1 1 /\ secantNumber 2 5 := by
  exact And.intro tangent_T0
    (And.intro tangent_T1
      (And.intro tangent_T2
        (And.intro secant_S0
          (And.intro secant_S1 secant_S2))))

theorem ZigzagNumberUp_constructive_export :
    (forall values : List Nat, forall aNext n : Nat,
      ZigzagPrefix values ->
        values.length = Nat.succ (Nat.succ n) ->
          2 * aNext = zigzagConvolution values (Nat.succ n) ->
            ZigzagPrefix (values ++ [aNext])) /\
      (forall n a : Nat, tangentNumber n a = ZigzagNumber (2 * n + 1) a) /\
        (forall n a : Nat, secantNumber n a = ZigzagNumber (2 * n) a) /\
          ZigzagNumber 0 1 /\ ZigzagNumber 1 1 /\ ZigzagNumber 2 1 /\
            ZigzagNumber 3 2 /\ ZigzagNumber 4 5 /\ ZigzagNumber 5 16 /\
              tangentNumber 0 1 /\ tangentNumber 1 2 /\ tangentNumber 2 16 /\
                secantNumber 0 1 /\ secantNumber 1 1 /\ secantNumber 2 5 := by
  constructor
  · intro values aNext n hPrefix hlen hrec
    exact zigzagPrefix_step_from_positive_recurrence
      (values := values) (aNext := aNext) (n := n) hPrefix hlen hrec
  · constructor
    · intro n a
      exact tangentNumber_odd_classification n a
    · constructor
      · intro n a
        exact secantNumber_even_classification n a
      · exact And.intro zigzag_A0
          (And.intro zigzag_A1
            (And.intro zigzag_A2
              (And.intro zigzag_A3
                (And.intro zigzag_A4
                  (And.intro zigzag_A5
                    (And.intro tangent_T0
                      (And.intro tangent_T1
                        (And.intro tangent_T2
                          (And.intro secant_S0
                            (And.intro secant_S1 secant_S2))))))))))

end BEDC.Derived.ZigzagNumberUp
