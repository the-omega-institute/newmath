import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCauchyTailEnvelopeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCauchyTailEnvelopeUp : Type where
  | mk (stream regular dyadic tail reindex transport replay provenance name : BHist) :
      DyadicCauchyTailEnvelopeUp
  deriving DecidableEq

def dyadicCauchyTailEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCauchyTailEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCauchyTailEnvelopeEncodeBHist h

def dyadicCauchyTailEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCauchyTailEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCauchyTailEnvelopeDecodeBHist tail)

private theorem DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicCauchyTailEnvelopeDecodeBHist
          (dyadicCauchyTailEnvelopeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCauchyTailEnvelopeFields : DyadicCauchyTailEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCauchyTailEnvelopeUp.mk stream regular dyadic tail reindex transport replay
      provenance name =>
      [stream, regular, dyadic, tail, reindex, transport, replay, provenance, name]

def dyadicCauchyTailEnvelopeToEventFlow : DyadicCauchyTailEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCauchyTailEnvelopeFields x).map dyadicCauchyTailEnvelopeEncodeBHist

private def dyadicCauchyTailEnvelopeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicCauchyTailEnvelopeEventAt index rest

def dyadicCauchyTailEnvelopeFromEventFlow
    (ef : EventFlow) : Option DyadicCauchyTailEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicCauchyTailEnvelopeUp.mk
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 0 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 1 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 2 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 3 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 4 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 5 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 6 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 7 ef))
      (dyadicCauchyTailEnvelopeDecodeBHist (dyadicCauchyTailEnvelopeEventAt 8 ef)))

private theorem DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_round_trip
    (x : DyadicCauchyTailEnvelopeUp) :
    dyadicCauchyTailEnvelopeFromEventFlow (dyadicCauchyTailEnvelopeToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk stream regular dyadic tail reindex transport replay provenance name =>
      change
        some
          (DyadicCauchyTailEnvelopeUp.mk
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist stream))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist regular))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist dyadic))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist tail))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist reindex))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist transport))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist replay))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist provenance))
            (dyadicCauchyTailEnvelopeDecodeBHist
              (dyadicCauchyTailEnvelopeEncodeBHist name))) =
          some
            (DyadicCauchyTailEnvelopeUp.mk stream regular dyadic tail reindex transport
              replay provenance name)
      rw [DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode stream,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode regular,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode dyadic,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode tail,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode reindex,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode transport,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode replay,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode provenance,
        DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_decode_encode name]

private theorem DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicCauchyTailEnvelopeUp} :
    dyadicCauchyTailEnvelopeToEventFlow x = dyadicCauchyTailEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCauchyTailEnvelopeFromEventFlow (dyadicCauchyTailEnvelopeToEventFlow x) =
        dyadicCauchyTailEnvelopeFromEventFlow (dyadicCauchyTailEnvelopeToEventFlow y) :=
    congrArg dyadicCauchyTailEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicCauchyTailEnvelopeBHistCarrier :
    BHistCarrier DyadicCauchyTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCauchyTailEnvelopeToEventFlow
  fromEventFlow := dyadicCauchyTailEnvelopeFromEventFlow

instance dyadicCauchyTailEnvelopeChapterTasteGate :
    ChapterTasteGate DyadicCauchyTailEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicCauchyTailEnvelopeFromEventFlow (dyadicCauchyTailEnvelopeToEventFlow x) =
      some x
    exact DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DyadicCauchyTailEnvelopeUp) ∧
      Nonempty (ChapterTasteGate DyadicCauchyTailEnvelopeUp) ∧
        ∃ stream regular dyadic tail reindex transport replay provenance name : BHist,
          BHistCarrier.fromEventFlow
              (BHistCarrier.toEventFlow
                (DyadicCauchyTailEnvelopeUp.mk stream regular dyadic tail reindex transport
                  replay provenance name)) =
            some
              (DyadicCauchyTailEnvelopeUp.mk stream regular dyadic tail reindex transport
                replay provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨dyadicCauchyTailEnvelopeBHistCarrier⟩
  constructor
  · exact ⟨dyadicCauchyTailEnvelopeChapterTasteGate⟩
  · exact
      ⟨BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, by
          change
            dyadicCauchyTailEnvelopeFromEventFlow
                (dyadicCauchyTailEnvelopeToEventFlow
                  (DyadicCauchyTailEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty)) =
              some
                (DyadicCauchyTailEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
          exact
            DyadicCauchyTailEnvelopeTasteGate_single_carrier_alignment_round_trip
              (DyadicCauchyTailEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)⟩

end BEDC.Derived.DyadicCauchyTailEnvelopeUp.TasteGate
