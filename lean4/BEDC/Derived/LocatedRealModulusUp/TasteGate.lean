import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealModulusUp : Type where
  | mk (locatedRow dyadicLedger window readback realSeal transport replay provenance
      localName : BHist) : LocatedRealModulusUp
  deriving DecidableEq

def locatedRealModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealModulusEncodeBHist h

def locatedRealModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealModulusDecodeBHist tail)

private theorem LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealModulusFields : LocatedRealModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealModulusUp.mk locatedRow dyadicLedger window readback realSeal transport replay
      provenance localName =>
      [locatedRow, dyadicLedger, window, readback, realSeal, transport, replay, provenance,
        localName]

def locatedRealModulusToEventFlow : LocatedRealModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealModulusFields x).map locatedRealModulusEncodeBHist

private def locatedRealModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealModulusEventAt index rest

def locatedRealModulusFromEventFlow (ef : EventFlow) :
    Option LocatedRealModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealModulusUp.mk
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 0 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 1 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 2 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 3 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 4 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 5 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 6 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 7 ef))
      (locatedRealModulusDecodeBHist (locatedRealModulusEventAt 8 ef)))

def locatedRealModulusBHistCarrier :
    BHistCarrier LocatedRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealModulusToEventFlow
  fromEventFlow := locatedRealModulusFromEventFlow

instance locatedRealModulusBHistCarrierInstance :
    BHistCarrier LocatedRealModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealModulusBHistCarrier

private theorem LocatedRealModulusTasteGate_single_carrier_alignment_round_trip
    (x : LocatedRealModulusUp) :
    locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk locatedRow dyadicLedger window readback realSeal transport replay provenance localName =>
      change
        some
          (LocatedRealModulusUp.mk
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist locatedRow))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist dyadicLedger))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist window))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist readback))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist realSeal))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist transport))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist replay))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist provenance))
            (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist localName))) =
          some
            (LocatedRealModulusUp.mk locatedRow dyadicLedger window readback realSeal transport
              replay provenance localName)
      rw [LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode locatedRow,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode window,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode readback,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode realSeal,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode transport,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode replay,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode provenance,
        LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode localName]

private theorem LocatedRealModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealModulusUp} :
    locatedRealModulusToEventFlow x = locatedRealModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) =
        locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow y) :=
    congrArg locatedRealModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedRealModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedRealModulusTasteGate_single_carrier_alignment_round_trip y)))

def locatedRealModulusChapterTasteGate :
    @ChapterTasteGate LocatedRealModulusUp locatedRealModulusBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact LocatedRealModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedRealModulusChapterTasteGateInstance :
    ChapterTasteGate LocatedRealModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealModulusChapterTasteGate

theorem LocatedRealModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedRealModulusUp) ∧
      Nonempty (ChapterTasteGate LocatedRealModulusUp) ∧
      locatedRealModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedRealModulusTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨locatedRealModulusBHistCarrier⟩, ⟨⟨locatedRealModulusChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.LocatedRealModulusUp
