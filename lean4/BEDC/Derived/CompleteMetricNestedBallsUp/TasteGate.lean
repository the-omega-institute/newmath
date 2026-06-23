import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteMetricNestedBallsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteMetricNestedBallsUp : Type where
  | mk
      (completeMetric metricSpace radiusLedger containment streamWindows rationalReadback
        realSeal transport continuation provenance nameCert : BHist) :
      CompleteMetricNestedBallsUp
  deriving DecidableEq

def completeMetricNestedBallsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeMetricNestedBallsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeMetricNestedBallsEncodeBHist h

def completeMetricNestedBallsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeMetricNestedBallsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeMetricNestedBallsDecodeBHist tail)

private theorem CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeMetricNestedBallsFields : CompleteMetricNestedBallsUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteMetricNestedBallsUp.mk completeMetric metricSpace radiusLedger containment
      streamWindows rationalReadback realSeal transport continuation provenance nameCert =>
      [completeMetric, metricSpace, radiusLedger, containment, streamWindows, rationalReadback,
        realSeal, transport, continuation, provenance, nameCert]

def completeMetricNestedBallsToEventFlow : CompleteMetricNestedBallsUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completeMetricNestedBallsFields x).map completeMetricNestedBallsEncodeBHist

private def completeMetricNestedBallsEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completeMetricNestedBallsEventAt index rest

def completeMetricNestedBallsFromEventFlow
    (ef : EventFlow) : Option CompleteMetricNestedBallsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompleteMetricNestedBallsUp.mk
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 0 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 1 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 2 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 3 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 4 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 5 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 6 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 7 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 8 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 9 ef))
      (completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEventAt 10 ef)))

private theorem CompleteMetricNestedBallsTasteGate_single_carrier_alignment_round_trip
    (x : CompleteMetricNestedBallsUp) :
    completeMetricNestedBallsFromEventFlow (completeMetricNestedBallsToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk completeMetric metricSpace radiusLedger containment streamWindows rationalReadback
      realSeal transport continuation provenance nameCert =>
      change
        some
          (CompleteMetricNestedBallsUp.mk
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist completeMetric))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist metricSpace))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist radiusLedger))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist containment))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist streamWindows))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist rationalReadback))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist realSeal))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist transport))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist continuation))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist provenance))
            (completeMetricNestedBallsDecodeBHist
              (completeMetricNestedBallsEncodeBHist nameCert))) =
          some
            (CompleteMetricNestedBallsUp.mk completeMetric metricSpace radiusLedger containment
              streamWindows rationalReadback realSeal transport continuation provenance
              nameCert)
      rw [CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode
          completeMetric,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode metricSpace,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode radiusLedger,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode containment,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode streamWindows,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode
          rationalReadback,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode realSeal,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode transport,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode continuation,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode provenance,
        CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem CompleteMetricNestedBallsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompleteMetricNestedBallsUp} :
    completeMetricNestedBallsToEventFlow x = completeMetricNestedBallsToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeMetricNestedBallsFromEventFlow (completeMetricNestedBallsToEventFlow x) =
        completeMetricNestedBallsFromEventFlow (completeMetricNestedBallsToEventFlow y) :=
    congrArg completeMetricNestedBallsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompleteMetricNestedBallsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompleteMetricNestedBallsTasteGate_single_carrier_alignment_round_trip y)))

instance completeMetricNestedBallsBHistCarrier : BHistCarrier CompleteMetricNestedBallsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeMetricNestedBallsToEventFlow
  fromEventFlow := completeMetricNestedBallsFromEventFlow

instance completeMetricNestedBallsChapterTasteGate :
    ChapterTasteGate CompleteMetricNestedBallsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeMetricNestedBallsFromEventFlow (completeMetricNestedBallsToEventFlow x) =
      some x
    exact CompleteMetricNestedBallsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompleteMetricNestedBallsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompleteMetricNestedBallsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completeMetricNestedBallsChapterTasteGate

theorem CompleteMetricNestedBallsTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      completeMetricNestedBallsDecodeBHist (completeMetricNestedBallsEncodeBHist h) = h) ∧
      (∀ x : CompleteMetricNestedBallsUp,
        completeMetricNestedBallsFromEventFlow (completeMetricNestedBallsToEventFlow x) =
          some x) ∧
        completeMetricNestedBallsEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CompleteMetricNestedBallsTasteGate_single_carrier_alignment_decode_encode,
      CompleteMetricNestedBallsTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CompleteMetricNestedBallsUp
