import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalMidpointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalMidpointUp : Type where
  | mk (I D E0 E1 B S R Q H C P N : BHist) : LocatedIntervalMidpointUp
  deriving DecidableEq

def locatedIntervalMidpointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalMidpointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalMidpointEncodeBHist h

def locatedIntervalMidpointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalMidpointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalMidpointDecodeBHist tail)

private theorem LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalMidpointToEventFlow : LocatedIntervalMidpointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalMidpointUp.mk I D E0 E1 B S R Q H C P N =>
      [locatedIntervalMidpointEncodeBHist I,
        locatedIntervalMidpointEncodeBHist D,
        locatedIntervalMidpointEncodeBHist E0,
        locatedIntervalMidpointEncodeBHist E1,
        locatedIntervalMidpointEncodeBHist B,
        locatedIntervalMidpointEncodeBHist S,
        locatedIntervalMidpointEncodeBHist R,
        locatedIntervalMidpointEncodeBHist Q,
        locatedIntervalMidpointEncodeBHist H,
        locatedIntervalMidpointEncodeBHist C,
        locatedIntervalMidpointEncodeBHist P,
        locatedIntervalMidpointEncodeBHist N]

private def locatedIntervalMidpointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalMidpointEventAtDefault index rest

def locatedIntervalMidpointFromEventFlow (ef : EventFlow) :
    Option LocatedIntervalMidpointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalMidpointUp.mk
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 0 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 1 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 2 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 3 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 4 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 5 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 6 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 7 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 8 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 9 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 10 ef))
      (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEventAtDefault 11 ef)))

private theorem LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedIntervalMidpointUp,
      locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D E0 E1 B S R Q H C P N =>
      change
        some
          (LocatedIntervalMidpointUp.mk
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist I))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist D))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist E0))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist E1))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist B))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist S))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist R))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist Q))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist H))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist C))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist P))
            (locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist N))) =
          some (LocatedIntervalMidpointUp.mk I D E0 E1 B S R Q H C P N)
      rw [LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode I,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode D,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode E0,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode E1,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode B,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode S,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode R,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode H,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode C,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode P,
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalMidpointUp} :
    locatedIntervalMidpointToEventFlow x = locatedIntervalMidpointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) =
        locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow y) :=
    congrArg locatedIntervalMidpointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_round_trip y)))

instance locatedIntervalMidpointBHistCarrier : BHistCarrier LocatedIntervalMidpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalMidpointToEventFlow
  fromEventFlow := locatedIntervalMidpointFromEventFlow

instance locatedIntervalMidpointChapterTasteGate :
    ChapterTasteGate LocatedIntervalMidpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) = some x
    exact LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedIntervalMidpointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedIntervalMidpointChapterTasteGate

theorem LocatedIntervalMidpointUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedIntervalMidpointDecodeBHist (locatedIntervalMidpointEncodeBHist h) = h) ∧
      (∀ x : LocatedIntervalMidpointUp,
        locatedIntervalMidpointFromEventFlow (locatedIntervalMidpointToEventFlow x) = some x) ∧
        (∀ x y : LocatedIntervalMidpointUp,
          locatedIntervalMidpointToEventFlow x = locatedIntervalMidpointToEventFlow y → x = y) ∧
          locatedIntervalMidpointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_decode_encode,
      LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        LocatedIntervalMidpointUpTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedIntervalMidpointUp
