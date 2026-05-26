import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.JordanVariationDecompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive JordanVariationDecompositionUp : Type where
  | mk
      (boundedVariation partition endpoints dyadicEdges positiveLedger negativeLedger
        reconstruction refinement transport continuation provenance nameCert : BHist) :
      JordanVariationDecompositionUp
  deriving DecidableEq

def jordanVariationDecompositionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: jordanVariationDecompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: jordanVariationDecompositionEncodeBHist h

def jordanVariationDecompositionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (jordanVariationDecompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (jordanVariationDecompositionDecodeBHist tail)

private theorem JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def jordanVariationDecompositionFields : JordanVariationDecompositionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | JordanVariationDecompositionUp.mk boundedVariation partition endpoints dyadicEdges
      positiveLedger negativeLedger reconstruction refinement transport continuation provenance
      nameCert =>
      [boundedVariation, partition, endpoints, dyadicEdges, positiveLedger, negativeLedger,
        reconstruction, refinement, transport, continuation, provenance, nameCert]

def jordanVariationDecompositionToEventFlow : JordanVariationDecompositionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (jordanVariationDecompositionFields x).map jordanVariationDecompositionEncodeBHist

private def jordanVariationDecompositionEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => jordanVariationDecompositionEventAt index rest

def jordanVariationDecompositionFromEventFlow
    (ef : EventFlow) : Option JordanVariationDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (JordanVariationDecompositionUp.mk
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 0 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 1 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 2 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 3 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 4 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 5 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 6 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 7 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 8 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 9 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 10 ef))
      (jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEventAt 11 ef)))

private theorem JordanVariationDecompositionTasteGate_single_carrier_alignment_round_trip
    (x : JordanVariationDecompositionUp) :
    jordanVariationDecompositionFromEventFlow (jordanVariationDecompositionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk boundedVariation partition endpoints dyadicEdges positiveLedger negativeLedger
      reconstruction refinement transport continuation provenance nameCert =>
      change
        some
          (JordanVariationDecompositionUp.mk
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist boundedVariation))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist partition))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist endpoints))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist dyadicEdges))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist positiveLedger))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist negativeLedger))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist reconstruction))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist refinement))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist transport))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist continuation))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist provenance))
            (jordanVariationDecompositionDecodeBHist
              (jordanVariationDecompositionEncodeBHist nameCert))) =
          some
            (JordanVariationDecompositionUp.mk boundedVariation partition endpoints dyadicEdges
              positiveLedger negativeLedger reconstruction refinement transport continuation
              provenance nameCert)
      rw [JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode
          boundedVariation,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode partition,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode endpoints,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode dyadicEdges,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode
          positiveLedger,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode
          negativeLedger,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode
          reconstruction,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode refinement,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode transport,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode continuation,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode provenance,
        JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem JordanVariationDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : JordanVariationDecompositionUp} :
    jordanVariationDecompositionToEventFlow x = jordanVariationDecompositionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      jordanVariationDecompositionFromEventFlow (jordanVariationDecompositionToEventFlow x) =
        jordanVariationDecompositionFromEventFlow (jordanVariationDecompositionToEventFlow y) :=
    congrArg jordanVariationDecompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (JordanVariationDecompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (JordanVariationDecompositionTasteGate_single_carrier_alignment_round_trip y)))

instance jordanVariationDecompositionBHistCarrier :
    BHistCarrier JordanVariationDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := jordanVariationDecompositionToEventFlow
  fromEventFlow := jordanVariationDecompositionFromEventFlow

instance jordanVariationDecompositionChapterTasteGate :
    ChapterTasteGate JordanVariationDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      jordanVariationDecompositionFromEventFlow (jordanVariationDecompositionToEventFlow x) =
        some x
    exact JordanVariationDecompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (JordanVariationDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate JordanVariationDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  jordanVariationDecompositionChapterTasteGate

theorem JordanVariationDecompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      jordanVariationDecompositionDecodeBHist (jordanVariationDecompositionEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier JordanVariationDecompositionUp) ∧
        Nonempty (ChapterTasteGate JordanVariationDecompositionUp) ∧
          jordanVariationDecompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨JordanVariationDecompositionTasteGate_single_carrier_alignment_decode_encode,
      ⟨jordanVariationDecompositionBHistCarrier⟩,
      ⟨jordanVariationDecompositionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.JordanVariationDecompositionUp
