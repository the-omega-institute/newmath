import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricTriangleUniformEstimateUp : Type where
  | mk
      (sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
        precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
        localName : BHist) :
      MetricTriangleUniformEstimateUp
  deriving DecidableEq

def metricTriangleUniformEstimateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricTriangleUniformEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricTriangleUniformEstimateEncodeBHist h

def metricTriangleUniformEstimateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricTriangleUniformEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricTriangleUniformEstimateDecodeBHist tail)

private theorem metricTriangleUniformEstimate_decode_encode :
    ∀ h : BHist,
      metricTriangleUniformEstimateDecodeBHist
        (metricTriangleUniformEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricTriangleUniformEstimateToEventFlow :
    MetricTriangleUniformEstimateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricTriangleUniformEstimateUp.mk sourceMetric targetMetric graph left right center
      sourceBoundLeft sourceBoundRight precision targetBoundLeft targetBoundRight targetTriangle
      transport route provenance localName =>
      [[BMark.b0],
        metricTriangleUniformEstimateEncodeBHist sourceMetric,
        [BMark.b1],
        metricTriangleUniformEstimateEncodeBHist targetMetric,
        [BMark.b0, BMark.b0],
        metricTriangleUniformEstimateEncodeBHist graph,
        [BMark.b0, BMark.b1],
        metricTriangleUniformEstimateEncodeBHist left,
        [BMark.b1, BMark.b0],
        metricTriangleUniformEstimateEncodeBHist right,
        [BMark.b1, BMark.b1],
        metricTriangleUniformEstimateEncodeBHist center,
        [BMark.b0, BMark.b0, BMark.b0],
        metricTriangleUniformEstimateEncodeBHist sourceBoundLeft,
        [BMark.b0, BMark.b0, BMark.b1],
        metricTriangleUniformEstimateEncodeBHist sourceBoundRight,
        [BMark.b0, BMark.b1, BMark.b0],
        metricTriangleUniformEstimateEncodeBHist precision,
        [BMark.b0, BMark.b1, BMark.b1],
        metricTriangleUniformEstimateEncodeBHist targetBoundLeft,
        [BMark.b1, BMark.b0, BMark.b0],
        metricTriangleUniformEstimateEncodeBHist targetBoundRight,
        [BMark.b1, BMark.b0, BMark.b1],
        metricTriangleUniformEstimateEncodeBHist targetTriangle,
        [BMark.b1, BMark.b1, BMark.b0],
        metricTriangleUniformEstimateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1],
        metricTriangleUniformEstimateEncodeBHist route,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b0],
        metricTriangleUniformEstimateEncodeBHist provenance,
        [BMark.b0, BMark.b0, BMark.b0, BMark.b1],
        metricTriangleUniformEstimateEncodeBHist localName]

private def metricTriangleUniformEstimateDecodePacket
    (sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName : RawEvent) :
    MetricTriangleUniformEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  MetricTriangleUniformEstimateUp.mk
    (metricTriangleUniformEstimateDecodeBHist sourceMetric)
    (metricTriangleUniformEstimateDecodeBHist targetMetric)
    (metricTriangleUniformEstimateDecodeBHist graph)
    (metricTriangleUniformEstimateDecodeBHist left)
    (metricTriangleUniformEstimateDecodeBHist right)
    (metricTriangleUniformEstimateDecodeBHist center)
    (metricTriangleUniformEstimateDecodeBHist sourceBoundLeft)
    (metricTriangleUniformEstimateDecodeBHist sourceBoundRight)
    (metricTriangleUniformEstimateDecodeBHist precision)
    (metricTriangleUniformEstimateDecodeBHist targetBoundLeft)
    (metricTriangleUniformEstimateDecodeBHist targetBoundRight)
    (metricTriangleUniformEstimateDecodeBHist targetTriangle)
    (metricTriangleUniformEstimateDecodeBHist transport)
    (metricTriangleUniformEstimateDecodeBHist route)
    (metricTriangleUniformEstimateDecodeBHist provenance)
    (metricTriangleUniformEstimateDecodeBHist localName)

private def metricTriangleUniformEstimateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => metricTriangleUniformEstimateRawAt n rest

private def metricTriangleUniformEstimateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => metricTriangleUniformEstimateLengthEq n rest

def metricTriangleUniformEstimateFromEventFlow :
    EventFlow → Option MetricTriangleUniformEstimateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match metricTriangleUniformEstimateLengthEq 32 flow with
      | true =>
          some
            (metricTriangleUniformEstimateDecodePacket
              (metricTriangleUniformEstimateRawAt 1 flow)
              (metricTriangleUniformEstimateRawAt 3 flow)
              (metricTriangleUniformEstimateRawAt 5 flow)
              (metricTriangleUniformEstimateRawAt 7 flow)
              (metricTriangleUniformEstimateRawAt 9 flow)
              (metricTriangleUniformEstimateRawAt 11 flow)
              (metricTriangleUniformEstimateRawAt 13 flow)
              (metricTriangleUniformEstimateRawAt 15 flow)
              (metricTriangleUniformEstimateRawAt 17 flow)
              (metricTriangleUniformEstimateRawAt 19 flow)
              (metricTriangleUniformEstimateRawAt 21 flow)
              (metricTriangleUniformEstimateRawAt 23 flow)
              (metricTriangleUniformEstimateRawAt 25 flow)
              (metricTriangleUniformEstimateRawAt 27 flow)
              (metricTriangleUniformEstimateRawAt 29 flow)
              (metricTriangleUniformEstimateRawAt 31 flow))
      | false => none

private theorem metricTriangleUniformEstimate_round_trip :
    ∀ x : MetricTriangleUniformEstimateUp,
      metricTriangleUniformEstimateFromEventFlow
        (metricTriangleUniformEstimateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName =>
      change
        some
          (metricTriangleUniformEstimateDecodePacket
            (metricTriangleUniformEstimateEncodeBHist sourceMetric)
            (metricTriangleUniformEstimateEncodeBHist targetMetric)
            (metricTriangleUniformEstimateEncodeBHist graph)
            (metricTriangleUniformEstimateEncodeBHist left)
            (metricTriangleUniformEstimateEncodeBHist right)
            (metricTriangleUniformEstimateEncodeBHist center)
            (metricTriangleUniformEstimateEncodeBHist sourceBoundLeft)
            (metricTriangleUniformEstimateEncodeBHist sourceBoundRight)
            (metricTriangleUniformEstimateEncodeBHist precision)
            (metricTriangleUniformEstimateEncodeBHist targetBoundLeft)
            (metricTriangleUniformEstimateEncodeBHist targetBoundRight)
            (metricTriangleUniformEstimateEncodeBHist targetTriangle)
            (metricTriangleUniformEstimateEncodeBHist transport)
            (metricTriangleUniformEstimateEncodeBHist route)
            (metricTriangleUniformEstimateEncodeBHist provenance)
            (metricTriangleUniformEstimateEncodeBHist localName)) =
          some
            (MetricTriangleUniformEstimateUp.mk sourceMetric targetMetric graph left right
              center sourceBoundLeft sourceBoundRight precision targetBoundLeft
              targetBoundRight targetTriangle transport route provenance localName)
      unfold metricTriangleUniformEstimateDecodePacket
      rw [metricTriangleUniformEstimate_decode_encode sourceMetric,
        metricTriangleUniformEstimate_decode_encode targetMetric,
        metricTriangleUniformEstimate_decode_encode graph,
        metricTriangleUniformEstimate_decode_encode left,
        metricTriangleUniformEstimate_decode_encode right,
        metricTriangleUniformEstimate_decode_encode center,
        metricTriangleUniformEstimate_decode_encode sourceBoundLeft,
        metricTriangleUniformEstimate_decode_encode sourceBoundRight,
        metricTriangleUniformEstimate_decode_encode precision,
        metricTriangleUniformEstimate_decode_encode targetBoundLeft,
        metricTriangleUniformEstimate_decode_encode targetBoundRight,
        metricTriangleUniformEstimate_decode_encode targetTriangle,
        metricTriangleUniformEstimate_decode_encode transport,
        metricTriangleUniformEstimate_decode_encode route,
        metricTriangleUniformEstimate_decode_encode provenance,
        metricTriangleUniformEstimate_decode_encode localName]

private theorem metricTriangleUniformEstimateToEventFlow_injective
    {x y : MetricTriangleUniformEstimateUp} :
    metricTriangleUniformEstimateToEventFlow x =
        metricTriangleUniformEstimateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricTriangleUniformEstimateFromEventFlow
          (metricTriangleUniformEstimateToEventFlow x) =
        metricTriangleUniformEstimateFromEventFlow
          (metricTriangleUniformEstimateToEventFlow y) :=
    congrArg metricTriangleUniformEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (metricTriangleUniformEstimate_round_trip x).symm
      (Eq.trans hread (metricTriangleUniformEstimate_round_trip y)))

instance metricTriangleUniformEstimateBHistCarrier :
    BHistCarrier MetricTriangleUniformEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricTriangleUniformEstimateToEventFlow
  fromEventFlow := metricTriangleUniformEstimateFromEventFlow

instance metricTriangleUniformEstimateChapterTasteGate :
    ChapterTasteGate MetricTriangleUniformEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricTriangleUniformEstimateFromEventFlow
          (metricTriangleUniformEstimateToEventFlow x) = some x
    exact metricTriangleUniformEstimate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricTriangleUniformEstimateToEventFlow_injective heq)

theorem MetricTriangleUniformEstimateTasteGate_single_carrier_alignment :
    (forall x : MetricTriangleUniformEstimateUp,
      metricTriangleUniformEstimateFromEventFlow
          (metricTriangleUniformEstimateToEventFlow x) = some x) ∧
      (forall x y : MetricTriangleUniformEstimateUp,
        metricTriangleUniformEstimateToEventFlow x =
            metricTriangleUniformEstimateToEventFlow y ->
          x = y) ∧
        ∃ x : MetricTriangleUniformEstimateUp,
          x =
              MetricTriangleUniformEstimateUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty ∧
            metricTriangleUniformEstimateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
        precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
        localName =>
        change
          some
            (metricTriangleUniformEstimateDecodePacket
              (metricTriangleUniformEstimateEncodeBHist sourceMetric)
              (metricTriangleUniformEstimateEncodeBHist targetMetric)
              (metricTriangleUniformEstimateEncodeBHist graph)
              (metricTriangleUniformEstimateEncodeBHist left)
              (metricTriangleUniformEstimateEncodeBHist right)
              (metricTriangleUniformEstimateEncodeBHist center)
              (metricTriangleUniformEstimateEncodeBHist sourceBoundLeft)
              (metricTriangleUniformEstimateEncodeBHist sourceBoundRight)
              (metricTriangleUniformEstimateEncodeBHist precision)
              (metricTriangleUniformEstimateEncodeBHist targetBoundLeft)
              (metricTriangleUniformEstimateEncodeBHist targetBoundRight)
              (metricTriangleUniformEstimateEncodeBHist targetTriangle)
              (metricTriangleUniformEstimateEncodeBHist transport)
              (metricTriangleUniformEstimateEncodeBHist route)
              (metricTriangleUniformEstimateEncodeBHist provenance)
              (metricTriangleUniformEstimateEncodeBHist localName)) =
            some
              (MetricTriangleUniformEstimateUp.mk sourceMetric targetMetric graph left right
                center sourceBoundLeft sourceBoundRight precision targetBoundLeft
                targetBoundRight targetTriangle transport route provenance localName)
        unfold metricTriangleUniformEstimateDecodePacket
        rw [metricTriangleUniformEstimate_decode_encode sourceMetric,
          metricTriangleUniformEstimate_decode_encode targetMetric,
          metricTriangleUniformEstimate_decode_encode graph,
          metricTriangleUniformEstimate_decode_encode left,
          metricTriangleUniformEstimate_decode_encode right,
          metricTriangleUniformEstimate_decode_encode center,
          metricTriangleUniformEstimate_decode_encode sourceBoundLeft,
          metricTriangleUniformEstimate_decode_encode sourceBoundRight,
          metricTriangleUniformEstimate_decode_encode precision,
          metricTriangleUniformEstimate_decode_encode targetBoundLeft,
          metricTriangleUniformEstimate_decode_encode targetBoundRight,
          metricTriangleUniformEstimate_decode_encode targetTriangle,
          metricTriangleUniformEstimate_decode_encode transport,
          metricTriangleUniformEstimate_decode_encode route,
          metricTriangleUniformEstimate_decode_encode provenance,
          metricTriangleUniformEstimate_decode_encode localName]
  · constructor
    · intro _ _ heq
      exact metricTriangleUniformEstimateToEventFlow_injective heq
    · exact
        ⟨MetricTriangleUniformEstimateUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
          rfl, rfl⟩

end BEDC.Derived.MetricTriangleUniformEstimateUp
