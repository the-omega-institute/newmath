import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalStreamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalStreamUp : Type where
  | mk
      (decimalPrefix streamSchedule windowLedger placeValue dyadicComparison regSeqHandoff
        realSeal transport replay provenance localName : BHist) :
      DecimalStreamUp
  deriving DecidableEq

def decimalStreamEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decimalStreamEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decimalStreamEncodeBHist h

def decimalStreamDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decimalStreamDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decimalStreamDecodeBHist tail)

private theorem DecimalStreamTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, decimalStreamDecodeBHist (decimalStreamEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def decimalStreamFields : DecimalStreamUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalStreamUp.mk decimalPrefix streamSchedule windowLedger placeValue dyadicComparison
      regSeqHandoff realSeal transport replay provenance localName =>
      [decimalPrefix, streamSchedule, windowLedger, placeValue, dyadicComparison,
        regSeqHandoff, realSeal, transport, replay, provenance, localName]

def decimalStreamToEventFlow : DecimalStreamUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (decimalStreamFields x).map decimalStreamEncodeBHist

private def decimalStreamEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => decimalStreamEventAtDefault index rest

def decimalStreamFromEventFlow (ef : EventFlow) : Option DecimalStreamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DecimalStreamUp.mk
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 0 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 1 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 2 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 3 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 4 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 5 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 6 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 7 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 8 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 9 ef))
      (decimalStreamDecodeBHist (decimalStreamEventAtDefault 10 ef)))

private theorem DecimalStreamTasteGate_single_carrier_alignment_round_trip :
    forall x : DecimalStreamUp, decimalStreamFromEventFlow (decimalStreamToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk decimalPrefix streamSchedule windowLedger placeValue dyadicComparison regSeqHandoff realSeal
      transport replay provenance localName =>
      change
        some
          (DecimalStreamUp.mk
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist decimalPrefix))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist streamSchedule))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist windowLedger))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist placeValue))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist dyadicComparison))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist regSeqHandoff))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist realSeal))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist transport))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist replay))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist provenance))
            (decimalStreamDecodeBHist (decimalStreamEncodeBHist localName))) =
          some
            (DecimalStreamUp.mk decimalPrefix streamSchedule windowLedger placeValue
              dyadicComparison regSeqHandoff realSeal transport replay provenance localName)
      rw [DecimalStreamTasteGate_single_carrier_alignment_decode_encode decimalPrefix,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode streamSchedule,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode windowLedger,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode placeValue,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode dyadicComparison,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode regSeqHandoff,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode realSeal,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode transport,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode replay,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode provenance,
        DecimalStreamTasteGate_single_carrier_alignment_decode_encode localName]

private theorem DecimalStreamTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DecimalStreamUp} :
    decimalStreamToEventFlow x = decimalStreamToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decimalStreamFromEventFlow (decimalStreamToEventFlow x) =
        decimalStreamFromEventFlow (decimalStreamToEventFlow y) :=
    congrArg decimalStreamFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DecimalStreamTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DecimalStreamTasteGate_single_carrier_alignment_round_trip y)))

private theorem DecimalStreamTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : DecimalStreamUp, decimalStreamFields x = decimalStreamFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk decimalPrefix₁ streamSchedule₁ windowLedger₁ placeValue₁ dyadicComparison₁
      regSeqHandoff₁ realSeal₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk decimalPrefix₂ streamSchedule₂ windowLedger₂ placeValue₂ dyadicComparison₂
          regSeqHandoff₂ realSeal₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance decimalStreamBHistCarrier : BHistCarrier DecimalStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decimalStreamToEventFlow
  fromEventFlow := decimalStreamFromEventFlow

instance decimalStreamChapterTasteGate : ChapterTasteGate DecimalStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => DecimalStreamTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DecimalStreamTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance decimalStreamFieldFaithful : FieldFaithful DecimalStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := decimalStreamFields
  field_faithful := DecimalStreamTasteGate_single_carrier_alignment_fields_faithful

instance decimalStreamNontrivial : BEDC.Meta.TasteGate.Nontrivial DecimalStreamUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DecimalStreamUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DecimalStreamUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DecimalStreamTasteGate_single_carrier_alignment :
    (∀ h : BHist, decimalStreamDecodeBHist (decimalStreamEncodeBHist h) = h) ∧
      (∀ x : DecimalStreamUp, decimalStreamFromEventFlow (decimalStreamToEventFlow x) = some x) ∧
        (∀ x y : DecimalStreamUp, decimalStreamToEventFlow x = decimalStreamToEventFlow y -> x = y) ∧
          decimalStreamEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact DecimalStreamTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact DecimalStreamTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact DecimalStreamTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.DecimalStreamUp
