import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricReflectionSandwichUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricReflectionSandwichUp : Type where
  | mk :
      (sourceMetric separatedMetric embedding completion denseEmbedding dyadicLedger realSeal
        transport replay provenance localNameCert : BHist) →
      MetricReflectionSandwichUp
  deriving DecidableEq

def metricReflectionSandwichEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricReflectionSandwichEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricReflectionSandwichEncodeBHist h

def metricReflectionSandwichDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricReflectionSandwichDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricReflectionSandwichDecodeBHist tail)

private theorem metricReflectionSandwich_decode_encode_bhist :
    ∀ h : BHist,
      metricReflectionSandwichDecodeBHist (metricReflectionSandwichEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metricReflectionSandwichFields : MetricReflectionSandwichUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricReflectionSandwichUp.mk sourceMetric separatedMetric embedding completion
      denseEmbedding dyadicLedger realSeal transport replay provenance localNameCert =>
      [sourceMetric, separatedMetric, embedding, completion, denseEmbedding, dyadicLedger,
        realSeal, transport, replay, provenance, localNameCert]

def metricReflectionSandwichToEventFlow : MetricReflectionSandwichUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map metricReflectionSandwichEncodeBHist (metricReflectionSandwichFields x)

def metricReflectionSandwichFromEventFlow : EventFlow → Option MetricReflectionSandwichUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceMetric :: rest0 =>
      match rest0 with
      | [] => none
      | separatedMetric :: rest1 =>
          match rest1 with
          | [] => none
          | embedding :: rest2 =>
              match rest2 with
              | [] => none
              | completion :: rest3 =>
                  match rest3 with
                  | [] => none
                  | denseEmbedding :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadicLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localNameCert :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (MetricReflectionSandwichUp.mk
                                                      (metricReflectionSandwichDecodeBHist
                                                        sourceMetric)
                                                      (metricReflectionSandwichDecodeBHist
                                                        separatedMetric)
                                                      (metricReflectionSandwichDecodeBHist
                                                        embedding)
                                                      (metricReflectionSandwichDecodeBHist
                                                        completion)
                                                      (metricReflectionSandwichDecodeBHist
                                                        denseEmbedding)
                                                      (metricReflectionSandwichDecodeBHist
                                                        dyadicLedger)
                                                      (metricReflectionSandwichDecodeBHist
                                                        realSeal)
                                                      (metricReflectionSandwichDecodeBHist
                                                        transport)
                                                      (metricReflectionSandwichDecodeBHist
                                                        replay)
                                                      (metricReflectionSandwichDecodeBHist
                                                        provenance)
                                                      (metricReflectionSandwichDecodeBHist
                                                        localNameCert))
                                              | _ :: _ => none

private theorem metricReflectionSandwich_round_trip :
    ∀ x : MetricReflectionSandwichUp,
      metricReflectionSandwichFromEventFlow (metricReflectionSandwichToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceMetric separatedMetric embedding completion denseEmbedding dyadicLedger realSeal
      transport replay provenance localNameCert =>
      change
        some
          (MetricReflectionSandwichUp.mk
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist sourceMetric))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist separatedMetric))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist embedding))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist completion))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist denseEmbedding))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist dyadicLedger))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist realSeal))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist transport))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist replay))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist provenance))
            (metricReflectionSandwichDecodeBHist
              (metricReflectionSandwichEncodeBHist localNameCert))) =
          some
            (MetricReflectionSandwichUp.mk sourceMetric separatedMetric embedding completion
              denseEmbedding dyadicLedger realSeal transport replay provenance localNameCert)
      rw [metricReflectionSandwich_decode_encode_bhist sourceMetric,
        metricReflectionSandwich_decode_encode_bhist separatedMetric,
        metricReflectionSandwich_decode_encode_bhist embedding,
        metricReflectionSandwich_decode_encode_bhist completion,
        metricReflectionSandwich_decode_encode_bhist denseEmbedding,
        metricReflectionSandwich_decode_encode_bhist dyadicLedger,
        metricReflectionSandwich_decode_encode_bhist realSeal,
        metricReflectionSandwich_decode_encode_bhist transport,
        metricReflectionSandwich_decode_encode_bhist replay,
        metricReflectionSandwich_decode_encode_bhist provenance,
        metricReflectionSandwich_decode_encode_bhist localNameCert]

private theorem metricReflectionSandwichToEventFlow_injective {x y : MetricReflectionSandwichUp} :
    metricReflectionSandwichToEventFlow x = metricReflectionSandwichToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricReflectionSandwichFromEventFlow (metricReflectionSandwichToEventFlow x) =
        metricReflectionSandwichFromEventFlow (metricReflectionSandwichToEventFlow y) :=
    congrArg metricReflectionSandwichFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricReflectionSandwich_round_trip x).symm
      (Eq.trans hread (metricReflectionSandwich_round_trip y)))

instance metricReflectionSandwichBHistCarrier : BHistCarrier MetricReflectionSandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricReflectionSandwichToEventFlow
  fromEventFlow := metricReflectionSandwichFromEventFlow

instance metricReflectionSandwichChapterTasteGate :
    ChapterTasteGate MetricReflectionSandwichUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricReflectionSandwichFromEventFlow
      (metricReflectionSandwichToEventFlow x) = some x
    exact metricReflectionSandwich_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricReflectionSandwichToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricReflectionSandwichUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricReflectionSandwichChapterTasteGate

theorem MetricReflectionSandwichTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricReflectionSandwichDecodeBHist (metricReflectionSandwichEncodeBHist h) = h) ∧
      (∀ x : MetricReflectionSandwichUp,
        metricReflectionSandwichFromEventFlow (metricReflectionSandwichToEventFlow x) = some x) ∧
        (∀ x y : MetricReflectionSandwichUp,
          metricReflectionSandwichToEventFlow x = metricReflectionSandwichToEventFlow y → x = y) ∧
          metricReflectionSandwichEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metricReflectionSandwich_decode_encode_bhist
  · constructor
    · exact metricReflectionSandwich_round_trip
    · constructor
      · intro x y heq
        exact metricReflectionSandwichToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetricReflectionSandwichUp
