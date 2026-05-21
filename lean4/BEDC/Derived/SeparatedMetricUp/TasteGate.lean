import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedMetricUp : Type where
  | mk :
      (metric distance separation limitLeft limitRight equivalence transport continuation
        provenance name : BHist) ->
        SeparatedMetricUp

def separatedMetricEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedMetricEncodeBHist h

def separatedMetricDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedMetricDecodeBHist tail)

private theorem separatedMetricDecode_encode_bhist :
    forall h : BHist, separatedMetricDecodeBHist (separatedMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def separatedMetricToEventFlow : SeparatedMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedMetricUp.mk metric distance separation limitLeft limitRight equivalence
      transport continuation provenance name =>
      [BMark.b1 :: BMark.b0 :: BMark.b0 :: BMark.b0 :: [],
        separatedMetricEncodeBHist metric,
        separatedMetricEncodeBHist distance,
        separatedMetricEncodeBHist separation,
        separatedMetricEncodeBHist limitLeft,
        separatedMetricEncodeBHist limitRight,
        separatedMetricEncodeBHist equivalence,
        separatedMetricEncodeBHist transport,
        separatedMetricEncodeBHist continuation,
        separatedMetricEncodeBHist provenance,
        separatedMetricEncodeBHist name]

def separatedMetricReadRows : EventFlow -> Option SeparatedMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | metric :: rest1 =>
      match rest1 with
      | distance :: rest2 =>
          match rest2 with
          | separation :: rest3 =>
              match rest3 with
              | limitLeft :: rest4 =>
                  match rest4 with
                  | limitRight :: rest5 =>
                      match rest5 with
                      | equivalence :: rest6 =>
                          match rest6 with
                          | transport :: rest7 =>
                              match rest7 with
                              | continuation :: rest8 =>
                                  match rest8 with
                                  | provenance :: rest9 =>
                                      match rest9 with
                                      | name :: rest10 =>
                                          match rest10 with
                                          | [] =>
                                              some
                                                (SeparatedMetricUp.mk
                                                  (separatedMetricDecodeBHist metric)
                                                  (separatedMetricDecodeBHist distance)
                                                  (separatedMetricDecodeBHist separation)
                                                  (separatedMetricDecodeBHist limitLeft)
                                                  (separatedMetricDecodeBHist limitRight)
                                                  (separatedMetricDecodeBHist equivalence)
                                                  (separatedMetricDecodeBHist transport)
                                                  (separatedMetricDecodeBHist continuation)
                                                  (separatedMetricDecodeBHist provenance)
                                                  (separatedMetricDecodeBHist name))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

def separatedMetricFromEventFlow : EventFlow -> Option SeparatedMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: rows => separatedMetricReadRows rows
  | [] => none

private theorem separatedMetric_round_trip :
    forall x : SeparatedMetricUp,
      separatedMetricFromEventFlow (separatedMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric distance separation limitLeft limitRight equivalence transport continuation
      provenance name =>
      change
        some
          (SeparatedMetricUp.mk
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist metric))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist distance))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist separation))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist limitLeft))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist limitRight))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist equivalence))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist transport))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist continuation))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist provenance))
            (separatedMetricDecodeBHist (separatedMetricEncodeBHist name))) =
          some
            (SeparatedMetricUp.mk metric distance separation limitLeft limitRight
              equivalence transport continuation provenance name)
      rw [separatedMetricDecode_encode_bhist metric,
        separatedMetricDecode_encode_bhist distance,
        separatedMetricDecode_encode_bhist separation,
        separatedMetricDecode_encode_bhist limitLeft,
        separatedMetricDecode_encode_bhist limitRight,
        separatedMetricDecode_encode_bhist equivalence,
        separatedMetricDecode_encode_bhist transport,
        separatedMetricDecode_encode_bhist continuation,
        separatedMetricDecode_encode_bhist provenance,
        separatedMetricDecode_encode_bhist name]

private theorem separatedMetricToEventFlow_injective {x y : SeparatedMetricUp} :
    separatedMetricToEventFlow x = separatedMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedMetricFromEventFlow (separatedMetricToEventFlow x) =
        separatedMetricFromEventFlow (separatedMetricToEventFlow y) :=
    congrArg separatedMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (separatedMetric_round_trip x).symm
      (Eq.trans hread (separatedMetric_round_trip y)))

instance separatedMetricBHistCarrier : BHistCarrier SeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedMetricToEventFlow
  fromEventFlow := separatedMetricFromEventFlow

instance separatedMetricChapterTasteGate : ChapterTasteGate SeparatedMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separatedMetricFromEventFlow (separatedMetricToEventFlow x) = some x
    exact separatedMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separatedMetricToEventFlow_injective heq)

theorem SeparatedMetricTasteGate_single_carrier_alignment :
    (forall h : BHist, separatedMetricDecodeBHist (separatedMetricEncodeBHist h) = h) /\
      (forall x : SeparatedMetricUp,
        separatedMetricFromEventFlow (separatedMetricToEventFlow x) = some x) /\
      (forall {x y : SeparatedMetricUp},
        separatedMetricToEventFlow x = separatedMetricToEventFlow y -> x = y) /\
      separatedMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact separatedMetricDecode_encode_bhist
  · constructor
    · intro x
      change separatedMetricFromEventFlow (separatedMetricToEventFlow x) = some x
      exact separatedMetric_round_trip x
    · constructor
      · intro x y heq
        exact separatedMetricToEventFlow_injective heq
      · rfl

end BEDC.Derived.SeparatedMetricUp
