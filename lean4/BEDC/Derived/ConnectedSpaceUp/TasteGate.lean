import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConnectedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConnectedSpaceUp : Type where
  | mk
      (topology clopenCandidate separationAttempt pullback metricConsumer realConsumer
        chainComparison transport replay provenance localName : BHist) : ConnectedSpaceUp

def connectedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: connectedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: connectedSpaceEncodeBHist h

def connectedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (connectedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (connectedSpaceDecodeBHist tail)

private theorem ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, connectedSpaceDecodeBHist (connectedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def connectedSpaceFields : ConnectedSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConnectedSpaceUp.mk topology clopenCandidate separationAttempt pullback metricConsumer
      realConsumer chainComparison transport replay provenance localName =>
      [topology, clopenCandidate, separationAttempt, pullback, metricConsumer, realConsumer,
        chainComparison, transport, replay, provenance, localName]

def connectedSpaceToEventFlow : ConnectedSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (connectedSpaceFields x).map connectedSpaceEncodeBHist

private def connectedSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => connectedSpaceEventAtDefault index rest

def connectedSpaceFromEventFlow (ef : EventFlow) : Option ConnectedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConnectedSpaceUp.mk
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 0 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 1 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 2 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 3 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 4 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 5 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 6 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 7 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 8 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 9 ef))
      (connectedSpaceDecodeBHist (connectedSpaceEventAtDefault 10 ef)))

private theorem ConnectedSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConnectedSpaceUp,
      connectedSpaceFromEventFlow (connectedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk topology clopenCandidate separationAttempt pullback metricConsumer realConsumer
      chainComparison transport replay provenance localName =>
      change
        some
          (ConnectedSpaceUp.mk
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist topology))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist clopenCandidate))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist separationAttempt))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist pullback))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist metricConsumer))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist realConsumer))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist chainComparison))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist transport))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist replay))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist provenance))
            (connectedSpaceDecodeBHist (connectedSpaceEncodeBHist localName))) =
          some
            (ConnectedSpaceUp.mk topology clopenCandidate separationAttempt pullback
              metricConsumer realConsumer chainComparison transport replay provenance localName)
      rw [ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode topology,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode clopenCandidate,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode separationAttempt,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode pullback,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode metricConsumer,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode realConsumer,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode chainComparison,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode transport,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode replay,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode provenance,
        ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem ConnectedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConnectedSpaceUp} :
    connectedSpaceToEventFlow x = connectedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      connectedSpaceFromEventFlow (connectedSpaceToEventFlow x) =
        connectedSpaceFromEventFlow (connectedSpaceToEventFlow y) :=
    congrArg connectedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConnectedSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ConnectedSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance connectedSpaceBHistCarrier : BHistCarrier ConnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := connectedSpaceToEventFlow
  fromEventFlow := connectedSpaceFromEventFlow

instance connectedSpaceChapterTasteGate : ChapterTasteGate ConnectedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change connectedSpaceFromEventFlow (connectedSpaceToEventFlow x) = some x
    exact ConnectedSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConnectedSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ConnectedSpaceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ConnectedSpaceUp) ∧
      Nonempty (ChapterTasteGate ConnectedSpaceUp) ∧
        (∀ h : BHist, connectedSpaceDecodeBHist (connectedSpaceEncodeBHist h) = h) ∧
          connectedSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨connectedSpaceBHistCarrier⟩, ⟨connectedSpaceChapterTasteGate⟩,
      ConnectedSpaceTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.ConnectedSpaceUp
