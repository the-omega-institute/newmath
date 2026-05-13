import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyWitnessScheduleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyWitnessScheduleUp : Type where
  | mk :
      (family modulus window dyadic readback sealRow transport route provenance name : BHist) →
        RegularCauchyWitnessScheduleUp
  deriving DecidableEq

def regularCauchyWitnessScheduleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyWitnessScheduleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyWitnessScheduleEncodeBHist h

def regularCauchyWitnessScheduleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyWitnessScheduleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyWitnessScheduleDecodeBHist tail)

private theorem regularCauchyWitnessScheduleDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyWitnessScheduleDecodeBHist
        (regularCauchyWitnessScheduleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyWitnessScheduleToEventFlow :
    RegularCauchyWitnessScheduleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyWitnessScheduleUp.mk family modulus window dyadic readback sealRow
      transport route provenance name =>
      [[BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist family,
        [BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyWitnessScheduleEncodeBHist name]

def regularCauchyWitnessScheduleFromEventFlow :
    EventFlow → Option RegularCauchyWitnessScheduleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | family :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadic :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | sealRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (RegularCauchyWitnessScheduleUp.mk
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            family)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            modulus)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            window)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            dyadic)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            readback)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            sealRow)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            transport)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            route)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            provenance)
                                                                                          (regularCauchyWitnessScheduleDecodeBHist
                                                                                            name))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem regularCauchyWitnessSchedule_round_trip :
    ∀ x : RegularCauchyWitnessScheduleUp,
      regularCauchyWitnessScheduleFromEventFlow
        (regularCauchyWitnessScheduleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family modulus window dyadic readback sealRow transport route provenance name =>
      change
        some
          (RegularCauchyWitnessScheduleUp.mk
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist family))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist modulus))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist window))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist dyadic))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist readback))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist sealRow))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist transport))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist route))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist provenance))
            (regularCauchyWitnessScheduleDecodeBHist
              (regularCauchyWitnessScheduleEncodeBHist name))) =
          some
            (RegularCauchyWitnessScheduleUp.mk family modulus window dyadic readback sealRow
              transport route provenance name)
      rw [regularCauchyWitnessScheduleDecode_encode_bhist family,
        regularCauchyWitnessScheduleDecode_encode_bhist modulus,
        regularCauchyWitnessScheduleDecode_encode_bhist window,
        regularCauchyWitnessScheduleDecode_encode_bhist dyadic,
        regularCauchyWitnessScheduleDecode_encode_bhist readback,
        regularCauchyWitnessScheduleDecode_encode_bhist sealRow,
        regularCauchyWitnessScheduleDecode_encode_bhist transport,
        regularCauchyWitnessScheduleDecode_encode_bhist route,
        regularCauchyWitnessScheduleDecode_encode_bhist provenance,
        regularCauchyWitnessScheduleDecode_encode_bhist name]

private theorem regularCauchyWitnessScheduleToEventFlow_injective
    {x y : RegularCauchyWitnessScheduleUp} :
    regularCauchyWitnessScheduleToEventFlow x =
      regularCauchyWitnessScheduleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyWitnessScheduleFromEventFlow
          (regularCauchyWitnessScheduleToEventFlow x) =
        regularCauchyWitnessScheduleFromEventFlow
          (regularCauchyWitnessScheduleToEventFlow y) :=
    congrArg regularCauchyWitnessScheduleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyWitnessSchedule_round_trip x).symm
      (Eq.trans hread (regularCauchyWitnessSchedule_round_trip y)))

instance regularCauchyWitnessScheduleBHistCarrier :
    BHistCarrier RegularCauchyWitnessScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyWitnessScheduleToEventFlow
  fromEventFlow := regularCauchyWitnessScheduleFromEventFlow

instance regularCauchyWitnessScheduleChapterTasteGate :
    ChapterTasteGate RegularCauchyWitnessScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyWitnessScheduleFromEventFlow
        (regularCauchyWitnessScheduleToEventFlow x) = some x
    exact regularCauchyWitnessSchedule_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyWitnessScheduleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyWitnessScheduleUp :=
  regularCauchyWitnessScheduleChapterTasteGate

theorem RegularCauchyWitnessScheduleUp_taste_gate_boundary :
    ChapterTasteGate RegularCauchyWitnessScheduleUp ∧
      (∀ (x : RegularCauchyWitnessScheduleUp) (w : RawEvent) (m : DisplayAlphabet),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyWitnessScheduleChapterTasteGate
  · intro x w m hw hm
    exact ChapterTasteGate.conservativity x w m hw hm

theorem RegularCauchyWitnessScheduleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyWitnessScheduleDecodeBHist
        (regularCauchyWitnessScheduleEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyWitnessScheduleUp,
        regularCauchyWitnessScheduleFromEventFlow
          (regularCauchyWitnessScheduleToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyWitnessScheduleUp,
          regularCauchyWitnessScheduleToEventFlow x =
            regularCauchyWitnessScheduleToEventFlow y → x = y) ∧
          regularCauchyWitnessScheduleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyWitnessScheduleDecode_encode_bhist
  · constructor
    · exact regularCauchyWitnessSchedule_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyWitnessScheduleToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyWitnessScheduleUp
