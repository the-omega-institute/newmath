import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisUnarySpineNormalizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisUnarySpineNormalizerUp : Type where
  | mk
      (sourceSpine axisZeroSpine lengthLedger standardBoundary componentTransport
        continuationRoutes provenance name : BHist) :
      AxisUnarySpineNormalizerUp
  deriving DecidableEq

def axisUnarySpineNormalizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisUnarySpineNormalizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisUnarySpineNormalizerEncodeBHist h

def axisUnarySpineNormalizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisUnarySpineNormalizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisUnarySpineNormalizerDecodeBHist tail)

private theorem axisUnarySpineNormalizerDecode_encode_bhist :
    ∀ h : BHist,
      axisUnarySpineNormalizerDecodeBHist (axisUnarySpineNormalizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axisUnarySpineNormalizerToEventFlow : AxisUnarySpineNormalizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisUnarySpineNormalizerUp.mk sourceSpine axisZeroSpine lengthLedger standardBoundary
      componentTransport continuationRoutes provenance name =>
      [[BMark.b0],
        axisUnarySpineNormalizerEncodeBHist sourceSpine,
        [BMark.b1, BMark.b0],
        axisUnarySpineNormalizerEncodeBHist axisZeroSpine,
        [BMark.b1, BMark.b1, BMark.b0],
        axisUnarySpineNormalizerEncodeBHist lengthLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisUnarySpineNormalizerEncodeBHist standardBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisUnarySpineNormalizerEncodeBHist componentTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisUnarySpineNormalizerEncodeBHist continuationRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisUnarySpineNormalizerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisUnarySpineNormalizerEncodeBHist name]

def axisUnarySpineNormalizerFromEventFlow : EventFlow → Option AxisUnarySpineNormalizerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceSpine :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | axisZeroSpine :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | lengthLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | standardBoundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | componentTransport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuationRoutes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (AxisUnarySpineNormalizerUp.mk
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            sourceSpine)
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            axisZeroSpine)
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            lengthLedger)
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            standardBoundary)
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            componentTransport)
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            continuationRoutes)
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            provenance)
                                                                          (axisUnarySpineNormalizerDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem axisUnarySpineNormalizer_round_trip :
    ∀ x : AxisUnarySpineNormalizerUp,
      axisUnarySpineNormalizerFromEventFlow (axisUnarySpineNormalizerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceSpine axisZeroSpine lengthLedger standardBoundary componentTransport
      continuationRoutes provenance name =>
      change
        some
          (AxisUnarySpineNormalizerUp.mk
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist sourceSpine))
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist axisZeroSpine))
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist lengthLedger))
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist standardBoundary))
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist componentTransport))
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist continuationRoutes))
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist provenance))
            (axisUnarySpineNormalizerDecodeBHist
              (axisUnarySpineNormalizerEncodeBHist name))) =
          some
            (AxisUnarySpineNormalizerUp.mk sourceSpine axisZeroSpine lengthLedger
              standardBoundary componentTransport continuationRoutes provenance name)
      rw [axisUnarySpineNormalizerDecode_encode_bhist sourceSpine,
        axisUnarySpineNormalizerDecode_encode_bhist axisZeroSpine,
        axisUnarySpineNormalizerDecode_encode_bhist lengthLedger,
        axisUnarySpineNormalizerDecode_encode_bhist standardBoundary,
        axisUnarySpineNormalizerDecode_encode_bhist componentTransport,
        axisUnarySpineNormalizerDecode_encode_bhist continuationRoutes,
        axisUnarySpineNormalizerDecode_encode_bhist provenance,
        axisUnarySpineNormalizerDecode_encode_bhist name]

private theorem axisUnarySpineNormalizerToEventFlow_injective
    {x y : AxisUnarySpineNormalizerUp} :
    axisUnarySpineNormalizerToEventFlow x = axisUnarySpineNormalizerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisUnarySpineNormalizerFromEventFlow (axisUnarySpineNormalizerToEventFlow x) =
        axisUnarySpineNormalizerFromEventFlow (axisUnarySpineNormalizerToEventFlow y) :=
    congrArg axisUnarySpineNormalizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisUnarySpineNormalizer_round_trip x).symm
      (Eq.trans hread (axisUnarySpineNormalizer_round_trip y)))

instance axisUnarySpineNormalizerBHistCarrier : BHistCarrier AxisUnarySpineNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisUnarySpineNormalizerToEventFlow
  fromEventFlow := axisUnarySpineNormalizerFromEventFlow

instance axisUnarySpineNormalizerChapterTasteGate :
    ChapterTasteGate AxisUnarySpineNormalizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      axisUnarySpineNormalizerFromEventFlow (axisUnarySpineNormalizerToEventFlow x) =
        some x
    exact axisUnarySpineNormalizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisUnarySpineNormalizerToEventFlow_injective heq)

theorem AxisUnarySpineNormalizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      axisUnarySpineNormalizerDecodeBHist (axisUnarySpineNormalizerEncodeBHist h) = h) ∧
      (∀ x : AxisUnarySpineNormalizerUp,
        axisUnarySpineNormalizerFromEventFlow (axisUnarySpineNormalizerToEventFlow x) =
          some x) ∧
        (∀ x y : AxisUnarySpineNormalizerUp,
          axisUnarySpineNormalizerToEventFlow x = axisUnarySpineNormalizerToEventFlow y →
            x = y) ∧
          axisUnarySpineNormalizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact axisUnarySpineNormalizerDecode_encode_bhist
  · constructor
    · exact axisUnarySpineNormalizer_round_trip
    · constructor
      · intro x y heq
        exact axisUnarySpineNormalizerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AxisUnarySpineNormalizerUp
