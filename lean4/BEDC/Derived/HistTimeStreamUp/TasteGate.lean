import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HistTimeStreamUp : Type where
  | mk :
      (source schedule start replay transport provenance name : BHist) ->
        HistTimeStreamUp
  deriving DecidableEq

def histTimeStreamEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: histTimeStreamEncodeBHist h
  | BHist.e1 h => BMark.b1 :: histTimeStreamEncodeBHist h

def histTimeStreamDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (histTimeStreamDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (histTimeStreamDecodeBHist tail)

private theorem HistTimeStreamTasteGate_single_carrier_alignment_decode :
    forall h : BHist, histTimeStreamDecodeBHist (histTimeStreamEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def histTimeStreamFields : HistTimeStreamUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HistTimeStreamUp.mk source schedule start replay transport provenance name =>
      [source, schedule, start, replay, transport, provenance, name]

def histTimeStreamToEventFlow : HistTimeStreamUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HistTimeStreamUp.mk source schedule start replay transport provenance name =>
      [[BMark.b0],
        histTimeStreamEncodeBHist source,
        [BMark.b1],
        histTimeStreamEncodeBHist schedule,
        [BMark.b0, BMark.b0],
        histTimeStreamEncodeBHist start,
        [BMark.b0, BMark.b1],
        histTimeStreamEncodeBHist replay,
        [BMark.b1, BMark.b0],
        histTimeStreamEncodeBHist transport,
        [BMark.b1, BMark.b1],
        histTimeStreamEncodeBHist provenance,
        [BMark.b0, BMark.b0, BMark.b0],
        histTimeStreamEncodeBHist name]

private def histTimeStreamDecodePacket
    (source schedule start replay transport provenance name : RawEvent) :
    HistTimeStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  HistTimeStreamUp.mk
    (histTimeStreamDecodeBHist source)
    (histTimeStreamDecodeBHist schedule)
    (histTimeStreamDecodeBHist start)
    (histTimeStreamDecodeBHist replay)
    (histTimeStreamDecodeBHist transport)
    (histTimeStreamDecodeBHist provenance)
    (histTimeStreamDecodeBHist name)

private def histTimeStreamRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => histTimeStreamRawAt n rest

private def histTimeStreamLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => histTimeStreamLengthEq n rest

def histTimeStreamFromEventFlow : EventFlow -> Option HistTimeStreamUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match histTimeStreamLengthEq 14 flow with
      | true =>
          some
            (histTimeStreamDecodePacket
              (histTimeStreamRawAt 1 flow)
              (histTimeStreamRawAt 3 flow)
              (histTimeStreamRawAt 5 flow)
              (histTimeStreamRawAt 7 flow)
              (histTimeStreamRawAt 9 flow)
              (histTimeStreamRawAt 11 flow)
              (histTimeStreamRawAt 13 flow))
      | false => none

private theorem histTimeStream_round_trip :
    forall x : HistTimeStreamUp,
      histTimeStreamFromEventFlow (histTimeStreamToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source schedule start replay transport provenance name =>
      change
        some
          (histTimeStreamDecodePacket
            (histTimeStreamEncodeBHist source)
            (histTimeStreamEncodeBHist schedule)
            (histTimeStreamEncodeBHist start)
            (histTimeStreamEncodeBHist replay)
            (histTimeStreamEncodeBHist transport)
            (histTimeStreamEncodeBHist provenance)
            (histTimeStreamEncodeBHist name)) =
          some
            (HistTimeStreamUp.mk source schedule start replay transport provenance name)
      unfold histTimeStreamDecodePacket
      rw [HistTimeStreamTasteGate_single_carrier_alignment_decode source,
        HistTimeStreamTasteGate_single_carrier_alignment_decode schedule,
        HistTimeStreamTasteGate_single_carrier_alignment_decode start,
        HistTimeStreamTasteGate_single_carrier_alignment_decode replay,
        HistTimeStreamTasteGate_single_carrier_alignment_decode transport,
        HistTimeStreamTasteGate_single_carrier_alignment_decode provenance,
        HistTimeStreamTasteGate_single_carrier_alignment_decode name]

private theorem histTimeStreamToEventFlow_injective {x y : HistTimeStreamUp} :
    histTimeStreamToEventFlow x = histTimeStreamToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      histTimeStreamFromEventFlow (histTimeStreamToEventFlow x) =
        histTimeStreamFromEventFlow (histTimeStreamToEventFlow y) :=
    congrArg histTimeStreamFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (histTimeStream_round_trip x).symm
      (Eq.trans hread (histTimeStream_round_trip y)))

private theorem histTimeStream_field_faithful :
    forall x y : HistTimeStreamUp, histTimeStreamFields x = histTimeStreamFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 schedule1 start1 replay1 transport1 provenance1 name1 =>
      cases y with
      | mk source2 schedule2 start2 replay2 transport2 provenance2 name2 =>
          cases hfields
          rfl

instance histTimeStreamBHistCarrier : BHistCarrier HistTimeStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := histTimeStreamToEventFlow
  fromEventFlow := histTimeStreamFromEventFlow

instance histTimeStreamChapterTasteGate : ChapterTasteGate HistTimeStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change histTimeStreamFromEventFlow (histTimeStreamToEventFlow x) = some x
    exact histTimeStream_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (histTimeStreamToEventFlow_injective heq)

instance histTimeStreamFieldFaithful : FieldFaithful HistTimeStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := histTimeStreamFields
  field_faithful := histTimeStream_field_faithful

def taste_gate : ChapterTasteGate HistTimeStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  histTimeStreamChapterTasteGate

theorem HistTimeStreamTasteGate_single_carrier_alignment :
    (forall h : BHist, histTimeStreamDecodeBHist (histTimeStreamEncodeBHist h) = h) ∧
      (forall x : HistTimeStreamUp,
        histTimeStreamFromEventFlow (histTimeStreamToEventFlow x) = some x) ∧
        (forall x y : HistTimeStreamUp,
          histTimeStreamToEventFlow x = histTimeStreamToEventFlow y -> x = y) ∧
          histTimeStreamEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨HistTimeStreamTasteGate_single_carrier_alignment_decode,
      histTimeStream_round_trip,
      (fun _ _ heq => histTimeStreamToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HistTimeStreamUp
