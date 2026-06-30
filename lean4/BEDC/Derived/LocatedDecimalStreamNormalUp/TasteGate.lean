import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedDecimalStreamNormalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedDecimalStreamNormalUp : Type where
  | mk (D S E W R Y T H C P N : BHist) : LocatedDecimalStreamNormalUp
  deriving DecidableEq

def locatedDecimalStreamNormalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedDecimalStreamNormalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedDecimalStreamNormalEncodeBHist h

private def locatedDecimalStreamNormalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedDecimalStreamNormalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedDecimalStreamNormalDecodeBHist tail)

private theorem LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def locatedDecimalStreamNormalToEventFlow :
    LocatedDecimalStreamNormalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedDecimalStreamNormalUp.mk D S E W R Y T H C P N =>
      [locatedDecimalStreamNormalEncodeBHist D,
        locatedDecimalStreamNormalEncodeBHist S,
        locatedDecimalStreamNormalEncodeBHist E,
        locatedDecimalStreamNormalEncodeBHist W,
        locatedDecimalStreamNormalEncodeBHist R,
        locatedDecimalStreamNormalEncodeBHist Y,
        locatedDecimalStreamNormalEncodeBHist T,
        locatedDecimalStreamNormalEncodeBHist H,
        locatedDecimalStreamNormalEncodeBHist C,
        locatedDecimalStreamNormalEncodeBHist P,
        locatedDecimalStreamNormalEncodeBHist N]

private def locatedDecimalStreamNormalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedDecimalStreamNormalEventAtDefault index rest

private def locatedDecimalStreamNormalFromEventFlow
    (ef : EventFlow) : Option LocatedDecimalStreamNormalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedDecimalStreamNormalUp.mk
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 0 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 1 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 2 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 3 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 4 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 5 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 6 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 7 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 8 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 9 ef))
      (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEventAtDefault 10 ef)))

private theorem LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedDecimalStreamNormalUp,
      locatedDecimalStreamNormalFromEventFlow (locatedDecimalStreamNormalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S E W R Y T H C P N =>
      change
        some
          (LocatedDecimalStreamNormalUp.mk
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist D))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist S))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist E))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist W))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist R))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist Y))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist T))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist H))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist C))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist P))
            (locatedDecimalStreamNormalDecodeBHist (locatedDecimalStreamNormalEncodeBHist N))) =
          some (LocatedDecimalStreamNormalUp.mk D S E W R Y T H C P N)
      rw [LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode D,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode S,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode E,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode W,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode R,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode Y,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode T,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode H,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode C,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode P,
        LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_decode N]

private theorem LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedDecimalStreamNormalUp} :
    locatedDecimalStreamNormalToEventFlow x = locatedDecimalStreamNormalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedDecimalStreamNormalFromEventFlow (locatedDecimalStreamNormalToEventFlow x) =
        locatedDecimalStreamNormalFromEventFlow (locatedDecimalStreamNormalToEventFlow y) :=
    congrArg locatedDecimalStreamNormalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_round_trip y)))

instance locatedDecimalStreamNormalBHistCarrier :
    BHistCarrier LocatedDecimalStreamNormalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedDecimalStreamNormalToEventFlow
  fromEventFlow := locatedDecimalStreamNormalFromEventFlow

instance locatedDecimalStreamNormalChapterTasteGate :
    ChapterTasteGate LocatedDecimalStreamNormalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedDecimalStreamNormalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedDecimalStreamNormalTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier LocatedDecimalStreamNormalUp) ∧
      Nonempty (ChapterTasteGate LocatedDecimalStreamNormalUp) ∧
        locatedDecimalStreamNormalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨locatedDecimalStreamNormalBHistCarrier⟩
  · constructor
    · exact ⟨locatedDecimalStreamNormalChapterTasteGate⟩
    · rfl

end BEDC.Derived.LocatedDecimalStreamNormalUp.TasteGate
