import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularRealLocatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularRealLocatorUp : Type where
  | mk
      (dyadic stream regseq approximation realSeal transport replay provenance localName :
        BHist) : BishopRegularRealLocatorUp
  deriving DecidableEq

def bishopRegularRealLocatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularRealLocatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularRealLocatorEncodeBHist h

def bishopRegularRealLocatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularRealLocatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularRealLocatorDecodeBHist tail)

private theorem BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopRegularRealLocatorDecodeBHist
      (bishopRegularRealLocatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRegularRealLocatorFields : BishopRegularRealLocatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularRealLocatorUp.mk dyadic stream regseq approximation realSeal transport
      replay provenance localName =>
      [dyadic, stream, regseq, approximation, realSeal, transport, replay, provenance,
        localName]

def bishopRegularRealLocatorToEventFlow : BishopRegularRealLocatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopRegularRealLocatorFields x).map bishopRegularRealLocatorEncodeBHist

private def bishopRegularRealLocatorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRegularRealLocatorEventAtDefault index rest

def bishopRegularRealLocatorFromEventFlow
    (ef : EventFlow) : Option BishopRegularRealLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopRegularRealLocatorUp.mk
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 0 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 1 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 2 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 3 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 4 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 5 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 6 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 7 ef))
      (bishopRegularRealLocatorDecodeBHist (bishopRegularRealLocatorEventAtDefault 8 ef)))

private theorem BishopRegularRealLocatorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRegularRealLocatorUp,
      bishopRegularRealLocatorFromEventFlow (bishopRegularRealLocatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadic stream regseq approximation realSeal transport replay provenance localName =>
      change
        some
          (BishopRegularRealLocatorUp.mk
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist dyadic))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist stream))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist regseq))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist approximation))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist realSeal))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist transport))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist replay))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist provenance))
            (bishopRegularRealLocatorDecodeBHist
              (bishopRegularRealLocatorEncodeBHist localName))) =
          some
            (BishopRegularRealLocatorUp.mk dyadic stream regseq approximation realSeal
              transport replay provenance localName)
      rw [BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode dyadic,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode stream,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode regseq,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode approximation,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode realSeal,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode transport,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode replay,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode provenance,
        BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode localName]

private theorem bishopRegularRealLocatorToEventFlow_injective
    {x y : BishopRegularRealLocatorUp} :
    bishopRegularRealLocatorToEventFlow x = bishopRegularRealLocatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularRealLocatorFromEventFlow (bishopRegularRealLocatorToEventFlow x) =
        bishopRegularRealLocatorFromEventFlow (bishopRegularRealLocatorToEventFlow y) :=
    congrArg bishopRegularRealLocatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopRegularRealLocatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRegularRealLocatorTasteGate_single_carrier_alignment_round_trip y)))

instance bishopRegularRealLocatorBHistCarrier : BHistCarrier BishopRegularRealLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularRealLocatorToEventFlow
  fromEventFlow := bishopRegularRealLocatorFromEventFlow

instance bishopRegularRealLocatorChapterTasteGate :
    ChapterTasteGate BishopRegularRealLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRegularRealLocatorFromEventFlow (bishopRegularRealLocatorToEventFlow x) =
      some x
    exact BishopRegularRealLocatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRegularRealLocatorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopRegularRealLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRegularRealLocatorChapterTasteGate

theorem BishopRegularRealLocatorTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopRegularRealLocatorDecodeBHist
      (bishopRegularRealLocatorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopRegularRealLocatorUp) ∧
        Nonempty (ChapterTasteGate BishopRegularRealLocatorUp) ∧
          bishopRegularRealLocatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopRegularRealLocatorTasteGate_single_carrier_alignment_decode_encode,
      ⟨bishopRegularRealLocatorBHistCarrier⟩,
      ⟨bishopRegularRealLocatorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopRegularRealLocatorUp
