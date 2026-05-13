import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountableObservationScheduleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountableObservationScheduleUp : Type where
  | mk :
      (observedPrefix requestWindow streamSource transport routes provenance
        nameCert : BHist) →
      CountableObservationScheduleUp
  deriving DecidableEq

def countableObservationScheduleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countableObservationScheduleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countableObservationScheduleEncodeBHist h

def countableObservationScheduleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countableObservationScheduleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countableObservationScheduleDecodeBHist tail)

private theorem countableObservationScheduleDecode_encode_bhist :
    ∀ h : BHist,
      countableObservationScheduleDecodeBHist (countableObservationScheduleEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def countableObservationScheduleToEventFlow :
    CountableObservationScheduleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CountableObservationScheduleUp.mk observedPrefix requestWindow streamSource transport
      routes provenance nameCert =>
      [[BMark.b0],
        countableObservationScheduleEncodeBHist observedPrefix,
        [BMark.b1, BMark.b0],
        countableObservationScheduleEncodeBHist requestWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        countableObservationScheduleEncodeBHist streamSource,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        countableObservationScheduleEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        countableObservationScheduleEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        countableObservationScheduleEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        countableObservationScheduleEncodeBHist nameCert]

def countableObservationScheduleFromEventFlow :
    EventFlow → Option CountableObservationScheduleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observedPrefix :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | requestWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | streamSource :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | routes :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nameCert :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (CountableObservationScheduleUp.mk
                                                                  (countableObservationScheduleDecodeBHist observedPrefix)
                                                                  (countableObservationScheduleDecodeBHist requestWindow)
                                                                  (countableObservationScheduleDecodeBHist streamSource)
                                                                  (countableObservationScheduleDecodeBHist transport)
                                                                  (countableObservationScheduleDecodeBHist routes)
                                                                  (countableObservationScheduleDecodeBHist provenance)
                                                                  (countableObservationScheduleDecodeBHist nameCert))
                                                          | _ :: _ => none

private theorem countableObservationSchedule_round_trip :
    ∀ x : CountableObservationScheduleUp,
      countableObservationScheduleFromEventFlow
          (countableObservationScheduleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observedPrefix requestWindow streamSource transport routes provenance nameCert =>
      change
        some
          (CountableObservationScheduleUp.mk
            (countableObservationScheduleDecodeBHist
              (countableObservationScheduleEncodeBHist observedPrefix))
            (countableObservationScheduleDecodeBHist
              (countableObservationScheduleEncodeBHist requestWindow))
            (countableObservationScheduleDecodeBHist
              (countableObservationScheduleEncodeBHist streamSource))
            (countableObservationScheduleDecodeBHist
              (countableObservationScheduleEncodeBHist transport))
            (countableObservationScheduleDecodeBHist
              (countableObservationScheduleEncodeBHist routes))
            (countableObservationScheduleDecodeBHist
              (countableObservationScheduleEncodeBHist provenance))
            (countableObservationScheduleDecodeBHist
              (countableObservationScheduleEncodeBHist nameCert))) =
          some
            (CountableObservationScheduleUp.mk observedPrefix requestWindow streamSource
              transport routes provenance nameCert)
      rw [countableObservationScheduleDecode_encode_bhist observedPrefix,
        countableObservationScheduleDecode_encode_bhist requestWindow,
        countableObservationScheduleDecode_encode_bhist streamSource,
        countableObservationScheduleDecode_encode_bhist transport,
        countableObservationScheduleDecode_encode_bhist routes,
        countableObservationScheduleDecode_encode_bhist provenance,
        countableObservationScheduleDecode_encode_bhist nameCert]

private theorem countableObservationScheduleToEventFlow_injective
    {x y : CountableObservationScheduleUp} :
    countableObservationScheduleToEventFlow x =
      countableObservationScheduleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countableObservationScheduleFromEventFlow
          (countableObservationScheduleToEventFlow x) =
        countableObservationScheduleFromEventFlow
          (countableObservationScheduleToEventFlow y) :=
    congrArg countableObservationScheduleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (countableObservationSchedule_round_trip x).symm
      (Eq.trans hread (countableObservationSchedule_round_trip y)))

instance countableObservationScheduleBHistCarrier :
    BHistCarrier CountableObservationScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countableObservationScheduleToEventFlow
  fromEventFlow := countableObservationScheduleFromEventFlow

instance countableObservationScheduleChapterTasteGate :
    ChapterTasteGate CountableObservationScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      countableObservationScheduleFromEventFlow
          (countableObservationScheduleToEventFlow x) =
        some x
    exact countableObservationSchedule_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (countableObservationScheduleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CountableObservationScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  countableObservationScheduleChapterTasteGate

theorem CountableObservationScheduleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      countableObservationScheduleDecodeBHist (countableObservationScheduleEncodeBHist h) =
        h) ∧
      (∀ x : CountableObservationScheduleUp,
        countableObservationScheduleFromEventFlow
            (countableObservationScheduleToEventFlow x) =
          some x) ∧
        (∀ x y : CountableObservationScheduleUp,
          countableObservationScheduleToEventFlow x =
            countableObservationScheduleToEventFlow y → x = y) ∧
          countableObservationScheduleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact countableObservationScheduleDecode_encode_bhist
  · constructor
    · exact countableObservationSchedule_round_trip
    · constructor
      · intro x y heq
        exact countableObservationScheduleToEventFlow_injective heq
      · rfl

end BEDC.Derived.CountableObservationScheduleUp
