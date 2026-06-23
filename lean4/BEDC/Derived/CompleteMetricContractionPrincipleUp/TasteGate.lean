import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteMetricContractionPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteMetricContractionPrincipleUp : Type where
  | mk :
      (completeMetric metricDistance contractionModulus picardOrbit cauchyRoute fixedPointSeal
        transport replay provenance localName : BHist) →
        CompleteMetricContractionPrincipleUp
  deriving DecidableEq

def completeMetricContractionPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeMetricContractionPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeMetricContractionPrincipleEncodeBHist h

def completeMetricContractionPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeMetricContractionPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeMetricContractionPrincipleDecodeBHist tail)

theorem CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      completeMetricContractionPrincipleDecodeBHist
          (completeMetricContractionPrincipleEncodeBHist h) =
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

def completeMetricContractionPrincipleFields :
    CompleteMetricContractionPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteMetricContractionPrincipleUp.mk completeMetric metricDistance contractionModulus
      picardOrbit cauchyRoute fixedPointSeal transport replay provenance localName =>
      [completeMetric, metricDistance, contractionModulus, picardOrbit, cauchyRoute,
        fixedPointSeal, transport, replay, provenance, localName]

def completeMetricContractionPrincipleToEventFlow :
    CompleteMetricContractionPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (completeMetricContractionPrincipleFields x).map
        completeMetricContractionPrincipleEncodeBHist

def completeMetricContractionPrincipleFromEventFlow :
    EventFlow → Option CompleteMetricContractionPrincipleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | completeMetric :: rest0 =>
      match rest0 with
      | [] => none
      | metricDistance :: rest1 =>
          match rest1 with
          | [] => none
          | contractionModulus :: rest2 =>
              match rest2 with
              | [] => none
              | picardOrbit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | cauchyRoute :: rest4 =>
                      match rest4 with
                      | [] => none
                      | fixedPointSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CompleteMetricContractionPrincipleUp.mk
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    completeMetric)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    metricDistance)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    contractionModulus)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    picardOrbit)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    cauchyRoute)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    fixedPointSeal)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    transport)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    replay)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    provenance)
                                                  (completeMetricContractionPrincipleDecodeBHist
                                                    localName))
                                          | _ :: _ => none

theorem CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompleteMetricContractionPrincipleUp,
      completeMetricContractionPrincipleFromEventFlow
          (completeMetricContractionPrincipleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk completeMetric metricDistance contractionModulus picardOrbit cauchyRoute fixedPointSeal
      transport replay provenance localName =>
      change
        some
          (CompleteMetricContractionPrincipleUp.mk
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist completeMetric))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist metricDistance))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist contractionModulus))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist picardOrbit))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist cauchyRoute))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist fixedPointSeal))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist transport))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist replay))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist provenance))
            (completeMetricContractionPrincipleDecodeBHist
              (completeMetricContractionPrincipleEncodeBHist localName))) =
          some
            (CompleteMetricContractionPrincipleUp.mk completeMetric metricDistance
              contractionModulus picardOrbit cauchyRoute fixedPointSeal transport replay
              provenance localName)
      rw [
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          completeMetric,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          metricDistance,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          contractionModulus,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          picardOrbit,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          cauchyRoute,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          fixedPointSeal,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          transport,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          replay,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          provenance,
        CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
          localName]

theorem CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompleteMetricContractionPrincipleUp} :
    completeMetricContractionPrincipleToEventFlow x =
        completeMetricContractionPrincipleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeMetricContractionPrincipleFromEventFlow
          (completeMetricContractionPrincipleToEventFlow x) =
        completeMetricContractionPrincipleFromEventFlow
          (completeMetricContractionPrincipleToEventFlow y) :=
    congrArg completeMetricContractionPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance completeMetricContractionPrincipleBHistCarrier :
    BHistCarrier CompleteMetricContractionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeMetricContractionPrincipleToEventFlow
  fromEventFlow := completeMetricContractionPrincipleFromEventFlow

instance completeMetricContractionPrincipleChapterTasteGate :
    ChapterTasteGate CompleteMetricContractionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      completeMetricContractionPrincipleDecodeBHist
          (completeMetricContractionPrincipleEncodeBHist h) =
        h) ∧
      (∀ x : CompleteMetricContractionPrincipleUp,
        completeMetricContractionPrincipleFromEventFlow
            (completeMetricContractionPrincipleToEventFlow x) =
          some x) ∧
        (∀ x y : CompleteMetricContractionPrincipleUp,
          completeMetricContractionPrincipleToEventFlow x =
              completeMetricContractionPrincipleToEventFlow y →
            x = y) ∧
          completeMetricContractionPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          CompleteMetricContractionPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.CompleteMetricContractionPrincipleUp
