import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealDyadicOrderEmbeddingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealDyadicOrderEmbeddingUp : Type where
  | mk
      (leftEndpoint rightEndpoint orderRow leftEmbedding rightEmbedding windowRow readbackRow
        densityRow transportRow replayRow provenanceRow nameRow : BHist) :
      RealDyadicOrderEmbeddingUp
  deriving DecidableEq

def realDyadicOrderEmbeddingEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realDyadicOrderEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realDyadicOrderEmbeddingEncodeBHist h

def realDyadicOrderEmbeddingDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realDyadicOrderEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realDyadicOrderEmbeddingDecodeBHist tail)

private theorem realDyadicOrderEmbedding_decode_encode_bhist :
    forall h : BHist,
      realDyadicOrderEmbeddingDecodeBHist (realDyadicOrderEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realDyadicOrderEmbeddingFields : RealDyadicOrderEmbeddingUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealDyadicOrderEmbeddingUp.mk leftEndpoint rightEndpoint orderRow leftEmbedding
      rightEmbedding windowRow readbackRow densityRow transportRow replayRow provenanceRow
      nameRow =>
      [leftEndpoint, rightEndpoint, orderRow, leftEmbedding, rightEmbedding, windowRow,
        readbackRow, densityRow, transportRow, replayRow, provenanceRow, nameRow]

def realDyadicOrderEmbeddingToEventFlow : RealDyadicOrderEmbeddingUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realDyadicOrderEmbeddingEncodeBHist (realDyadicOrderEmbeddingFields x)

def realDyadicOrderEmbeddingFromEventFlow : EventFlow -> Option RealDyadicOrderEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [leftEndpoint, rightEndpoint, orderRow, leftEmbedding, rightEmbedding, windowRow,
      readbackRow, densityRow, transportRow, replayRow, provenanceRow, nameRow] =>
      some
        (RealDyadicOrderEmbeddingUp.mk
          (realDyadicOrderEmbeddingDecodeBHist leftEndpoint)
          (realDyadicOrderEmbeddingDecodeBHist rightEndpoint)
          (realDyadicOrderEmbeddingDecodeBHist orderRow)
          (realDyadicOrderEmbeddingDecodeBHist leftEmbedding)
          (realDyadicOrderEmbeddingDecodeBHist rightEmbedding)
          (realDyadicOrderEmbeddingDecodeBHist windowRow)
          (realDyadicOrderEmbeddingDecodeBHist readbackRow)
          (realDyadicOrderEmbeddingDecodeBHist densityRow)
          (realDyadicOrderEmbeddingDecodeBHist transportRow)
          (realDyadicOrderEmbeddingDecodeBHist replayRow)
          (realDyadicOrderEmbeddingDecodeBHist provenanceRow)
          (realDyadicOrderEmbeddingDecodeBHist nameRow))
  | _ => none

private theorem realDyadicOrderEmbedding_round_trip :
    forall x : RealDyadicOrderEmbeddingUp,
      realDyadicOrderEmbeddingFromEventFlow (realDyadicOrderEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftEndpoint rightEndpoint orderRow leftEmbedding rightEmbedding windowRow readbackRow
      densityRow transportRow replayRow provenanceRow nameRow =>
      change
        some
          (RealDyadicOrderEmbeddingUp.mk
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist leftEndpoint))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist rightEndpoint))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist orderRow))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist leftEmbedding))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist rightEmbedding))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist windowRow))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist readbackRow))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist densityRow))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist transportRow))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist replayRow))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist provenanceRow))
            (realDyadicOrderEmbeddingDecodeBHist
              (realDyadicOrderEmbeddingEncodeBHist nameRow))) =
          some
            (RealDyadicOrderEmbeddingUp.mk leftEndpoint rightEndpoint orderRow leftEmbedding
              rightEmbedding windowRow readbackRow densityRow transportRow replayRow
              provenanceRow nameRow)
      rw [realDyadicOrderEmbedding_decode_encode_bhist leftEndpoint,
        realDyadicOrderEmbedding_decode_encode_bhist rightEndpoint,
        realDyadicOrderEmbedding_decode_encode_bhist orderRow,
        realDyadicOrderEmbedding_decode_encode_bhist leftEmbedding,
        realDyadicOrderEmbedding_decode_encode_bhist rightEmbedding,
        realDyadicOrderEmbedding_decode_encode_bhist windowRow,
        realDyadicOrderEmbedding_decode_encode_bhist readbackRow,
        realDyadicOrderEmbedding_decode_encode_bhist densityRow,
        realDyadicOrderEmbedding_decode_encode_bhist transportRow,
        realDyadicOrderEmbedding_decode_encode_bhist replayRow,
        realDyadicOrderEmbedding_decode_encode_bhist provenanceRow,
        realDyadicOrderEmbedding_decode_encode_bhist nameRow]

private theorem realDyadicOrderEmbeddingToEventFlow_injective
    {x y : RealDyadicOrderEmbeddingUp} :
    realDyadicOrderEmbeddingToEventFlow x = realDyadicOrderEmbeddingToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realDyadicOrderEmbeddingFromEventFlow (realDyadicOrderEmbeddingToEventFlow x) =
        realDyadicOrderEmbeddingFromEventFlow (realDyadicOrderEmbeddingToEventFlow y) :=
    congrArg realDyadicOrderEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realDyadicOrderEmbedding_round_trip x).symm
      (Eq.trans hread (realDyadicOrderEmbedding_round_trip y)))

private theorem realDyadicOrderEmbedding_fields_faithful :
    forall x y : RealDyadicOrderEmbeddingUp,
      realDyadicOrderEmbeddingFields x = realDyadicOrderEmbeddingFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk leftEndpoint1 rightEndpoint1 orderRow1 leftEmbedding1 rightEmbedding1 windowRow1
      readbackRow1 densityRow1 transportRow1 replayRow1 provenanceRow1 nameRow1 =>
      cases y with
      | mk leftEndpoint2 rightEndpoint2 orderRow2 leftEmbedding2 rightEmbedding2 windowRow2
          readbackRow2 densityRow2 transportRow2 replayRow2 provenanceRow2 nameRow2 =>
          cases hfields
          rfl

instance realDyadicOrderEmbeddingBHistCarrier :
    BHistCarrier RealDyadicOrderEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realDyadicOrderEmbeddingToEventFlow
  fromEventFlow := realDyadicOrderEmbeddingFromEventFlow

instance realDyadicOrderEmbeddingChapterTasteGate :
    ChapterTasteGate RealDyadicOrderEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realDyadicOrderEmbeddingFromEventFlow (realDyadicOrderEmbeddingToEventFlow x) =
      some x
    exact realDyadicOrderEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realDyadicOrderEmbeddingToEventFlow_injective heq)

instance realDyadicOrderEmbeddingFieldFaithful :
    FieldFaithful RealDyadicOrderEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realDyadicOrderEmbeddingFields
  field_faithful := realDyadicOrderEmbedding_fields_faithful

def taste_gate : ChapterTasteGate RealDyadicOrderEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realDyadicOrderEmbeddingChapterTasteGate

theorem RealDyadicOrderEmbeddingTasteGate_single_carrier_alignment :
    (forall h : BHist,
        realDyadicOrderEmbeddingDecodeBHist (realDyadicOrderEmbeddingEncodeBHist h) = h) ∧
      realDyadicOrderEmbeddingFields
          (RealDyadicOrderEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact ⟨realDyadicOrderEmbedding_decode_encode_bhist, rfl⟩

end BEDC.Derived.RealDyadicOrderEmbeddingUp.TasteGate
